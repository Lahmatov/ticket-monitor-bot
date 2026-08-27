#!/usr/bin/env python3
"""
FPF ticket monitor -> Telegram notifier.

Watches the Portuguese Football Federation ticketing site
(https://bilheteira.fpf.pt/) for Portugal national-team matches and sends a
Telegram message as soon as a match becomes buyable.

Runs as a short-lived job (see the GitHub Actions workflow) rather than a
long-lived bot: each invocation fetches the listing once, compares it against
persisted state, notifies about anything newly on sale, and exits.

Cadence (enforced here, not by cron, so it is correct across DST):
  * Daytime in Lisbon (07:00-00:00): act on every scheduled run.
  * Night in Lisbon   (00:00-07:00): act at most once every ~2 hours.

Modes (``--mode``):
  * normal      – the real thing: fetch, detect, notify.
  * diagnostic  – fetch and print what the parser sees; write the raw HTML to
                  --dump-file so selectors can be calibrated. No notifications.
  * test        – send a single Telegram test message to verify credentials.

The sites to watch are listed in ``sources.json`` next to this script (each
entry: id, name, url, optional keywords / CSS selectors). Empty keywords means
"watch every event on that site". See the README.

Configuration is via environment variables (all optional except the Telegram
secrets, which are only needed for `normal`/`test`):

  TELEGRAM_BOT_TOKEN   Bot token from @BotFather.
  TELEGRAM_CHAT_ID     Destination chat id.
  SOURCES_FILE         Path to the sources JSON (default: ./sources.json).
  STATE_FILE           Path to the JSON state file (default ./state.json).

Legacy single-source override (takes precedence over SOURCES_FILE when any is
set): FPF_URL, MATCH_KEYWORDS (comma list), EVENT_SELECTOR, TITLE_SELECTOR,
LINK_SELECTOR.

The status keyword lists (sold-out / coming-soon / buy) live in CONFIG below
and can be tuned without touching the logic.
"""

from __future__ import annotations

import argparse
import json
import logging
import os
import re
import sys
import time
from datetime import datetime, timezone
from urllib.parse import urljoin, urlparse
from zoneinfo import ZoneInfo

import requests
from bs4 import BeautifulSoup

# --------------------------------------------------------------------------- #
# Configuration                                                               #
# --------------------------------------------------------------------------- #

LISBON = ZoneInfo("Europe/Lisbon")

# Night runs (Lisbon 00:00-07:00) act at most this often.
NIGHT_MIN_INTERVAL_MIN = 105  # ~2h, with slack for cron jitter

# Network
REQUEST_TIMEOUT = 25
REQUEST_RETRIES = 3
REQUEST_BACKOFF = 3  # seconds, exponential
USER_AGENT = (
    "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
    "(KHTML, like Gecko) Chrome/124.0 Safari/537.36"
)

# hrefs that look like an event / ticket page (heuristic mode)
EVENT_URL_HINTS = (
    "evento",
    "event",
    "bilhete",
    "bilhetes",
    "ticket",
    "jogo",
    "match",
    "espetaculo",
    "sessao",
)

# Status detection keywords (Portuguese first, English fallback). Order of the
# checks in classify_status() matters: sold-out and coming-soon win over "buy".
SOLD_OUT_WORDS = (
    "esgotado",
    "esgotados",
    "esgotada",
    "vendas encerradas",
    "venda encerrada",
    "indisponivel",
    "indisponível",
    "sold out",
)
SOON_WORDS = (
    "brevemente",
    "em breve",
    "proximamente",
    "próximamente",
    "disponivel brevemente",
    "disponível brevemente",
    "a venda em breve",
    "à venda em breve",
    "coming soon",
    "muito em breve",
)
BUY_WORDS = (
    "comprar",
    "compra",
    "adquirir",
    "à venda",
    "a venda",
    "disponivel",
    "disponível",
    "bilhetes",
    "buy",
    "buy now",
    "on sale",
)

# How long a match may be absent from the listing before we forget it (so a
# re-opened sale would notify again). Keeps state bounded.
FORGET_AFTER_DAYS = 7

# Alert if the site can't be read this many runs in a row, then re-alert every
# this many failures so a persistent breakage stays visible without spamming.
FAILURE_ALERT_THRESHOLD = 4
FAILURE_REALERT_EVERY = 24

log = logging.getLogger("fpf")


# --------------------------------------------------------------------------- #
# Small helpers                                                               #
# --------------------------------------------------------------------------- #


def _now_utc() -> datetime:
    return datetime.now(timezone.utc)


def _parse_iso(value: str | None) -> datetime | None:
    if not value:
        return None
    try:
        return datetime.fromisoformat(value)
    except ValueError:
        return None


def _norm_ws(text: str) -> str:
    return re.sub(r"\s+", " ", text or "").strip()


def _contains_any(haystack: str, needles) -> bool:
    low = haystack.lower()
    return any(n in low for n in needles)


DATE_RE = re.compile(
    r"\b(\d{1,2})\s*(?:de\s*)?"
    r"(jan|fev|mar|abr|mai|jun|jul|ago|set|out|nov|dez|"
    r"janeiro|fevereiro|março|marco|abril|maio|junho|julho|agosto|"
    r"setembro|outubro|novembro|dezembro)\w*"
    r"(?:\s*(?:de\s*)?(\d{4}))?",
    re.IGNORECASE,
)
NUMERIC_DATE_RE = re.compile(r"\b\d{1,2}[/.\-]\d{1,2}(?:[/.\-]\d{2,4})?\b")


def _extract_date(text: str) -> str | None:
    m = NUMERIC_DATE_RE.search(text)
    if m:
        return m.group(0)
    m = DATE_RE.search(text)
    if m:
        return _norm_ws(m.group(0))
    return None


# --------------------------------------------------------------------------- #
# Config from environment                                                     #
# --------------------------------------------------------------------------- #


DEFAULT_SOURCES_FILE = os.path.join(os.path.dirname(os.path.abspath(__file__)),
                                    "sources.json")


class Source:
    """One ticketing site to watch."""

    def __init__(self, id, name, url, keywords=None, exclude_keywords=None,
                 event_selector="", title_selector="", link_selector=""):
        self.id = str(id).strip()
        self.name = str(name).strip() or self.id
        self.url = str(url).strip()
        self.keywords = [k.strip().lower() for k in (keywords or []) if k.strip()]
        self.exclude_keywords = [k.strip().lower()
                                 for k in (exclude_keywords or []) if k.strip()]
        self.event_selector = (event_selector or "").strip()
        self.title_selector = (title_selector or "").strip()
        self.link_selector = (link_selector or "").strip()


def _sources_from_env() -> list[Source] | None:
    """Legacy single-source override via FPF_URL / MATCH_KEYWORDS / *_SELECTOR."""
    if not any(os.environ.get(k) for k in
               ("FPF_URL", "MATCH_KEYWORDS", "EVENT_SELECTOR")):
        return None
    kw = os.environ.get("MATCH_KEYWORDS", "portugal")
    return [Source(
        id="fpf",
        name="Seleção (FPF)",
        url=os.environ.get("FPF_URL", "https://bilheteira.fpf.pt/"),
        keywords=[k for k in kw.split(",")],
        event_selector=os.environ.get("EVENT_SELECTOR", ""),
        title_selector=os.environ.get("TITLE_SELECTOR", ""),
        link_selector=os.environ.get("LINK_SELECTOR", ""),
    )]


def load_sources() -> list[Source]:
    override = _sources_from_env()
    if override:
        return override
    path = os.environ.get("SOURCES_FILE", DEFAULT_SOURCES_FILE).strip()
    try:
        with open(path, "r", encoding="utf-8") as fh:
            raw = json.load(fh)
        sources = [Source(**item) for item in raw if item.get("url")]
        if sources:
            return sources
        log.warning("Sources file %s is empty; using built-in default.", path)
    except FileNotFoundError:
        log.info("No sources file at %s; using built-in default.", path)
    except (json.JSONDecodeError, TypeError) as err:
        log.error("Bad sources file %s (%s); using built-in default.", path, err)
    return [Source(id="fpf", name="Seleção (FPF)",
                   url="https://bilheteira.fpf.pt/", keywords=["portugal"])]


class Config:
    def __init__(self) -> None:
        self.state_file = os.environ.get("STATE_FILE", "state.json").strip()
        self.telegram_token = os.environ.get("TELEGRAM_BOT_TOKEN", "").strip()
        self.telegram_chat = os.environ.get("TELEGRAM_CHAT_ID", "").strip()
        self.sources = load_sources()


# --------------------------------------------------------------------------- #
# State                                                                       #
# --------------------------------------------------------------------------- #


def load_state(path: str) -> dict:
    try:
        with open(path, "r", encoding="utf-8") as fh:
            data = json.load(fh)
    except (FileNotFoundError, json.JSONDecodeError):
        data = {}
    data.setdefault("notified", {})  # event_id -> {title,url,first_notified,last_seen}
    data.setdefault("last_night_check_utc", None)
    data.setdefault("failures", {})  # source_id -> consecutive failure count
    return data


def save_state(path: str, state: dict) -> None:
    tmp = f"{path}.tmp"
    with open(tmp, "w", encoding="utf-8") as fh:
        json.dump(state, fh, ensure_ascii=False, indent=2, sort_keys=True)
    os.replace(tmp, path)


# --------------------------------------------------------------------------- #
# Scheduling window                                                           #
# --------------------------------------------------------------------------- #


def should_act(now_lisbon: datetime, state: dict) -> tuple[bool, bool]:
    """Return (act, is_night). Enforces the day/night cadence, DST-correct."""
    hour = now_lisbon.hour
    is_night = hour < 7  # 00:00-06:59 Lisbon
    if not is_night:
        return True, False
    last = _parse_iso(state.get("last_night_check_utc"))
    if last is not None:
        elapsed_min = (_now_utc() - last).total_seconds() / 60.0
        if elapsed_min < NIGHT_MIN_INTERVAL_MIN:
            log.info(
                "Night run skipped: only %.0f min since last night check (< %d).",
                elapsed_min,
                NIGHT_MIN_INTERVAL_MIN,
            )
            return False, True
    return True, True


# --------------------------------------------------------------------------- #
# Fetch                                                                       #
# --------------------------------------------------------------------------- #


def fetch(url: str) -> str:
    headers = {
        "User-Agent": USER_AGENT,
        "Accept-Language": "pt-PT,pt;q=0.9,en;q=0.8",
        "Accept": "text/html,application/xhtml+xml",
    }
    last_err: Exception | None = None
    for attempt in range(1, REQUEST_RETRIES + 1):
        try:
            resp = requests.get(url, headers=headers, timeout=REQUEST_TIMEOUT)
            resp.raise_for_status()
            return resp.text
        except requests.RequestException as err:  # noqa: PERF203
            last_err = err
            wait = REQUEST_BACKOFF ** attempt
            log.warning("Fetch attempt %d/%d failed: %s", attempt, REQUEST_RETRIES, err)
            if attempt < REQUEST_RETRIES:
                time.sleep(wait)
    raise RuntimeError(f"Could not fetch {url}: {last_err}")


# --------------------------------------------------------------------------- #
# Parsing                                                                     #
# --------------------------------------------------------------------------- #


class Event:
    __slots__ = ("id", "title", "url", "date", "status", "context")

    def __init__(self, id_, title, url, date, status, context):
        self.id = id_
        self.title = title
        self.url = url
        self.date = date
        self.status = status
        self.context = context

    def __repr__(self) -> str:
        return f"<Event {self.status} {self.title!r} {self.date} {self.url}>"


def classify_status(context_text: str, has_buy_link: bool) -> str:
    """AVAILABLE | SOLD_OUT | SOON | UNKNOWN from surrounding text."""
    if _contains_any(context_text, SOLD_OUT_WORDS):
        return "SOLD_OUT"
    if _contains_any(context_text, SOON_WORDS):
        return "SOON"
    if has_buy_link or _contains_any(context_text, BUY_WORDS):
        return "AVAILABLE"
    return "UNKNOWN"


def _event_id(url: str, title: str) -> str:
    """Stable id: prefer the URL path (query stripped), else the title."""
    if url:
        p = urlparse(url)
        path = p.path.rstrip("/")
        if path and path != "/":
            return f"{p.netloc}{path}".lower()
    return "title:" + re.sub(r"[^a-z0-9]+", "-", title.lower()).strip("-")


def _looks_like_event_link(href: str) -> bool:
    low = href.lower()
    if low.startswith(("mailto:", "tel:", "javascript:", "#")):
        return False
    return any(hint in low for hint in EVENT_URL_HINTS)


_CARD_CLASS_HINTS = ("card", "event", "evento", "match", "jogo", "item",
                     "produto", "product", "tile", "box")
_BUY_ONLY_RE = re.compile(r"^(comprar|compra|adquirir|bilhetes?|detalhes?|ver|"
                          r"buy|tickets?|more|info)\b", re.IGNORECASE)


def _find_card(node):
    """Return a small ancestor 'card' element around an anchor."""
    container = node
    for _ in range(4):
        parent = container.parent
        if parent is None:
            break
        container = parent
        cls = " ".join(container.get("class", []) or []).lower()
        if any(k in cls for k in _CARD_CLASS_HINTS):
            break
    return container


def _card_title(card, anchor_text: str) -> str:
    """Best-effort event title: a heading in the card, else the anchor text."""
    heading = card.find(["h1", "h2", "h3", "h4", "h5"])
    if heading:
        htext = _norm_ws(heading.get_text(" ", strip=True))
        if htext:
            return htext
    # Fall back to the anchor text unless it's just a call-to-action label.
    if anchor_text and not _BUY_ONLY_RE.match(anchor_text):
        return anchor_text
    return ""


def parse_events_precise(soup: BeautifulSoup, base_url: str, src: "Source") -> list[Event]:
    events: list[Event] = []
    for card in soup.select(src.event_selector):
        title_el = card.select_one(src.title_selector) if src.title_selector else card
        title = _norm_ws(title_el.get_text(" ", strip=True)) if title_el else ""
        link_el = card.select_one(src.link_selector) if src.link_selector else card.find("a", href=True)
        url = urljoin(base_url, link_el["href"]) if link_el and link_el.has_attr("href") else ""
        context = _norm_ws(card.get_text(" ", strip=True))
        has_buy = bool(link_el and _contains_any(link_el.get_text(" ", strip=True), BUY_WORDS))
        if not title:
            continue
        events.append(
            Event(_event_id(url, title), title, url, _extract_date(context),
                  classify_status(context, has_buy), context[:400])
        )
    return events


def parse_events_heuristic(soup: BeautifulSoup, base_url: str) -> list[Event]:
    events: list[Event] = []
    seen: set[str] = set()
    for a in soup.find_all("a", href=True):
        href = a["href"]
        if not _looks_like_event_link(href):
            continue
        url = urljoin(base_url, href)
        anchor_text = _norm_ws(a.get_text(" ", strip=True))
        card = _find_card(a)
        context = _norm_ws(card.get_text(" ", strip=True))
        title = _card_title(card, anchor_text) or context[:80]
        if not title:
            continue
        eid = _event_id(url, title)
        if eid in seen:
            continue
        seen.add(eid)
        has_buy = _contains_any(anchor_text, BUY_WORDS)
        events.append(
            Event(eid, title, url, _extract_date(context),
                  classify_status(context, has_buy), context[:400])
        )
    return events


def parse_events(page_html: str, base_url: str, src: "Source") -> list[Event]:
    soup = BeautifulSoup(page_html, "html.parser")
    if src.event_selector:
        events = parse_events_precise(soup, base_url, src)
        if events:
            return events
        log.warning("event_selector %r matched nothing; falling back to heuristic.",
                    src.event_selector)
    return parse_events_heuristic(soup, base_url)


def matches_keywords(event: Event, src: "Source") -> bool:
    """True if the event passes the source's include AND exclude filters."""
    hay = f"{event.title} {event.context}".lower()
    if src.exclude_keywords and any(k in hay for k in src.exclude_keywords):
        return False
    if not src.keywords:  # no include keywords => watch every event on this source
        return True
    return any(k in hay for k in src.keywords)


# --------------------------------------------------------------------------- #
# Telegram                                                                    #
# --------------------------------------------------------------------------- #


def telegram_send(cfg: Config, text: str) -> bool:
    if not cfg.telegram_token or not cfg.telegram_chat:
        log.error("Telegram token/chat id not configured; cannot send message.")
        return False
    api = f"https://api.telegram.org/bot{cfg.telegram_token}/sendMessage"
    payload = {
        "chat_id": cfg.telegram_chat,
        "text": text,
        "parse_mode": "HTML",
        "disable_web_page_preview": False,
    }
    for attempt in range(1, 4):
        try:
            resp = requests.post(api, data=payload, timeout=REQUEST_TIMEOUT)
            if resp.status_code == 200:
                return True
            log.warning("Telegram send failed (%s): %s", resp.status_code, resp.text[:300])
        except requests.RequestException as err:
            log.warning("Telegram send error attempt %d: %s", attempt, err)
        time.sleep(2 * attempt)
    return False


def _esc(text: str) -> str:
    return (text.replace("&", "&amp;").replace("<", "&lt;").replace(">", "&gt;"))


def format_notification(event: Event, source_name: str) -> str:
    lines = [f"\U0001F3AB <b>Bilhetes à venda!</b> — {_esc(source_name)}",
             "", f"<b>{_esc(event.title)}</b>"]
    if event.date:
        lines.append(f"\U0001F4C5 {_esc(event.date)}")
    if event.url:
        lines.append("")
        lines.append(f'\U0001F517 <a href="{_esc(event.url)}">Comprar agora</a>')
    return "\n".join(lines)


# --------------------------------------------------------------------------- #
# GitHub Actions output helper                                                #
# --------------------------------------------------------------------------- #


def set_output(name: str, value: str) -> None:
    out = os.environ.get("GITHUB_OUTPUT")
    if not out:
        return
    try:
        with open(out, "a", encoding="utf-8") as fh:
            fh.write(f"{name}={value}\n")
    except OSError as err:
        log.warning("Could not write GITHUB_OUTPUT: %s", err)


# --------------------------------------------------------------------------- #
# Modes                                                                       #
# --------------------------------------------------------------------------- #


def run_diagnostic(cfg: Config, dump_file: str | None) -> int:
    for src in cfg.sources:
        print(f"\n{'=' * 70}\nSOURCE: {src.name} [{src.id}] -> {src.url}\n{'=' * 70}")
        try:
            page = fetch(src.url)
        except Exception as err:  # noqa: BLE001
            print(f"FETCH FAILED: {err}")
            continue
        print(f"Fetched {len(page)} bytes")
        if dump_file:
            out = f"{src.id}-{dump_file}"
            with open(out, "w", encoding="utf-8") as fh:
                fh.write(page)
            print(f"Raw HTML written to {out}")
        if not parse_events(page, src.url, src):
            _diag_hints(page)
        events = parse_events(page, src.url, src)
        print(f"\nParsed {len(events)} candidate event link(s):\n")
        for ev in events:
            star = "  <-- keyword match" if matches_keywords(ev, src) else ""
            print(f"[{ev.status:9}] {ev.title[:70]!r} | {ev.date} | {ev.url}{star}")
        matched = [e for e in events if matches_keywords(e, src)]
        kw = src.keywords or "(all events)"
        print(f"\nKeywords {kw}: {len(matched)} match; "
              f"available now: {sum(1 for e in matched if e.status == 'AVAILABLE')}")
    return 0


def _diag_hints(page: str) -> None:
    """When 0 events parse, print clues about how the page loads its data."""
    soup = BeautifulSoup(page, "html.parser")
    print("\n--- 0 events: inspecting page ---")
    # SPA / framework markers
    markers = ["__NEXT_DATA__", "window.__INITIAL_STATE__", "__NUXT__",
               "ng-version", "data-reactroot", "id=\"root\"", "id=\"app\"",
               "<app-root", "vue", "Blazor", "stimulus"]
    found = [m for m in markers if m.lower() in page.lower()]
    print("SPA markers:", found or "none obvious")
    # script sources (often reveal the API host / framework)
    srcs = [s.get("src") for s in soup.find_all("script", src=True)]
    print(f"{len(srcs)} external scripts; first few:")
    for s in srcs[:8]:
        print("   ", s)
    # anything that looks like an API / data endpoint
    hits = sorted(set(re.findall(r'["\'](/[^"\']*(?:api|json|event|bilhet|ticket)[^"\']*)["\']',
                                 page, re.IGNORECASE)))
    print(f"candidate data paths ({len(hits)}):")
    for h in hits[:20]:
        print("   ", h)
    absurls = sorted(set(re.findall(r'https?://[^\s"\'<>]*(?:api|graphql)[^\s"\'<>]*',
                                    page, re.IGNORECASE)))
    for u in absurls[:10]:
        print("    URL:", u)
    # a readable slice of the body text
    text = _norm_ws(soup.get_text(" ", strip=True))
    print("body text (first 400 chars):", text[:400] or "(empty)")
    print("--- end inspection ---\n")


_HOST_NOISE = ("angular.io", "google.com", "gstatic.com", "googleapis.com",
               "w3.org", "cloudflare.com", "schema.org", "github.com",
               "jquery.com", "mozilla.org", "npmjs.com", "microsoft.com",
               "bootstrapcdn.com", "jsdelivr.net", "unpkg.com", "sentry.io",
               "fontawesome.com", "youtube.com", "facebook.com", "example.com")


def _probe_get(url: str) -> None:
    """GET a candidate endpoint and print status/type/snippet (never raises)."""
    headers = {"User-Agent": USER_AGENT,
               "Accept": "application/json, text/plain, */*",
               "Accept-Language": "pt-PT,pt;q=0.9,en;q=0.8"}
    print(f"\n=== GET {url} ===")
    try:
        r = requests.get(url, headers=headers, timeout=REQUEST_TIMEOUT)
    except requests.RequestException as err:
        print("  request error:", err)
        return
    ctype = r.headers.get("content-type", "?")
    print(f"  status={r.status_code}  type={ctype}  len={len(r.text)}")
    print("  body (first 700 chars):", _norm_ws(r.text)[:700] or "(empty)")


def _probe_grep(url: str, term: str) -> None:
    """Download url and print context windows around each occurrence of term."""
    print(f"\n=== GREP {term!r} in {url} ===")
    try:
        body = fetch(url)
    except Exception as err:  # noqa: BLE001
        print("  fetch failed:", err)
        return
    idxs = [m.start() for m in re.finditer(re.escape(term), body)]
    print(f"  {len(idxs)} occurrence(s) in {len(body)} bytes")
    for i in idxs[:12]:
        snippet = body[max(0, i - 160):i + 160].replace("\n", " ")
        print("   …", snippet, "…")


def run_probe(cfg: Config) -> int:
    """Scan each source's JS bundles for API hosts / data endpoints.

    If PROBE_URL is set, just GET that URL and dump the response instead.
    """
    direct = os.environ.get("PROBE_URL", "").strip()
    grep = os.environ.get("PROBE_GREP", "").strip()
    if direct:
        for u in direct.split(","):
            u = u.strip()
            if not u:
                continue
            if grep:
                _probe_grep(u, grep)
            else:
                _probe_get(u)
        return 0

    host_re = re.compile(r'https?://([a-z0-9.\-]+)', re.IGNORECASE)
    path_re = re.compile(r'["\'`](/[a-zA-Z][a-zA-Z0-9_\-./]{2,}(?:/[a-zA-Z0-9_\-.]+){1,})["\'`]')
    for src in cfg.sources:
        print(f"\n{'=' * 70}\nPROBE: {src.name} [{src.id}] -> {src.url}\n{'=' * 70}")
        try:
            page = fetch(src.url)
        except Exception as err:  # noqa: BLE001
            print(f"FETCH FAILED: {err}")
            continue
        soup = BeautifulSoup(page, "html.parser")
        scripts = [urljoin(src.url, s["src"])
                   for s in soup.find_all("script", src=True)]
        hosts: dict[str, int] = {}
        paths: dict[str, int] = {}
        for js_url in scripts:
            if urlparse(js_url).netloc != urlparse(src.url).netloc:
                continue  # only same-origin app bundles
            try:
                body = fetch(js_url)
            except Exception as err:  # noqa: BLE001
                print(f"  (could not fetch {js_url}: {err})")
                continue
            print(f"  scanned {js_url} ({len(body)} bytes)")
            for h in host_re.findall(body):
                if not any(n in h.lower() for n in _HOST_NOISE):
                    hosts[h] = hosts.get(h, 0) + 1
            for p in path_re.findall(body):
                paths[p] = paths.get(p, 0) + 1
        print(f"\n  Non-noise hosts referenced ({len(hosts)}):")
        for h, n in sorted(hosts.items(), key=lambda kv: -kv[1])[:30]:
            print(f"      {n:5}x  {h}")
        interesting = {p: n for p, n in paths.items() if re.search(
            r'(api|event|evento|bilhet|ticket|sess|jogo|game|match|calendar|'
            r'agenda|list|catalog|product|show)', p, re.IGNORECASE)}
        print(f"  Interesting paths ({len(interesting)} of {len(paths)}):")
        for p, n in sorted(interesting.items(), key=lambda kv: -kv[1])[:40]:
            print(f"      {n:5}x  {p}")
    return 0


def run_chatid(cfg: Config) -> int:
    """Print chat ids seen in recent updates (message the bot first)."""
    if not cfg.telegram_token:
        print("TELEGRAM_BOT_TOKEN is not set.")
        return 1
    api = f"https://api.telegram.org/bot{cfg.telegram_token}/getUpdates"
    resp = requests.get(api, timeout=REQUEST_TIMEOUT)
    data = resp.json()
    if not data.get("ok"):
        print(f"Telegram API error: {data}")
        return 1
    seen: dict[str, str] = {}
    for upd in data.get("result", []):
        msg = upd.get("message") or upd.get("channel_post") or {}
        chat = msg.get("chat") or {}
        if "id" in chat:
            name = chat.get("title") or " ".join(
                filter(None, [chat.get("first_name"), chat.get("last_name")])
            ) or chat.get("username") or chat.get("type", "")
            seen[str(chat["id"])] = name
    if not seen:
        print("No chats found. Send a message to the bot in Telegram first, "
              "then run this again.")
        return 1
    print("Chats found (set TELEGRAM_CHAT_ID to the id you want):")
    for cid, name in seen.items():
        print(f"  chat_id = {cid}   ({name})")
    return 0


def run_test(cfg: Config) -> int:
    names = ", ".join(s.name for s in cfg.sources)
    ok = telegram_send(
        cfg,
        "✅ <b>Ticket monitor</b>\nTest message — credentials work.\n"
        f"Watching: {_esc(names)}",
    )
    print("Telegram test message sent." if ok else "Telegram test FAILED.")
    return 0 if ok else 1


def _process_source(cfg: Config, src: "Source", state: dict, now_iso: str) -> bool:
    """Check one source; return True if state changed."""
    notified = state["notified"]
    failures = state["failures"]
    dirty = False
    try:
        page = fetch(src.url)
        events = parse_events(page, src.url, src)
    except Exception as err:  # noqa: BLE001 - handle any failure uniformly
        log.error("[%s] fetch/parse failed: %s", src.id, err)
        failures[src.id] = failures.get(src.id, 0) + 1
        _maybe_alert_failure(cfg, src, failures[src.id], err)
        return True  # persist the failure counter

    if failures.get(src.id):
        failures[src.id] = 0
        dirty = True

    matched = [e for e in events if matches_keywords(e, src)]
    log.info("[%s] parsed %d events, %d match.", src.id, len(events), len(matched))

    for ev in matched:
        key = f"{src.id}:{ev.id}"
        entry = notified.get(key)
        if ev.status == "AVAILABLE":
            if entry is None:
                if telegram_send(cfg, format_notification(ev, src.name)):
                    log.info("[%s] notified: %s", src.id, ev.title)
                    notified[key] = {
                        "source": src.id,
                        "title": ev.title,
                        "url": ev.url,
                        "first_notified": now_iso,
                        "last_seen": now_iso,
                    }
                    dirty = True
                else:
                    log.error("[%s] notify failed for %s; retry next run.",
                              src.id, ev.title)
            else:
                entry["last_seen"] = now_iso
                dirty = True
        elif entry is not None:
            entry["last_seen"] = now_iso  # still listed, not buyable -> keep fresh
            dirty = True
    return dirty


def run_normal(cfg: Config) -> int:
    state = load_state(cfg.state_file)
    now_lisbon = datetime.now(LISBON)
    act, is_night = should_act(now_lisbon, state)
    if not act:
        return 0

    dirty = False
    if is_night:
        state["last_night_check_utc"] = _now_utc().isoformat()
        dirty = True

    now_iso = _now_utc().isoformat()
    for src in cfg.sources:
        if _process_source(cfg, src, state, now_iso):
            dirty = True

    if _prune_state(state, now_iso):
        dirty = True

    if dirty:
        save_state(cfg.state_file, state)
        set_output("state_changed", "true")
    return 0


def _prune_state(state: dict, now_iso: str) -> bool:
    now = _parse_iso(now_iso) or _now_utc()
    changed = False
    for eid in list(state["notified"].keys()):
        last_seen = _parse_iso(state["notified"][eid].get("last_seen"))
        if last_seen is None:
            continue
        if (now - last_seen).total_seconds() > FORGET_AFTER_DAYS * 86400:
            del state["notified"][eid]
            changed = True
    return changed


def _maybe_alert_failure(cfg: Config, src: "Source", n: int, err: Exception) -> None:
    if n == FAILURE_ALERT_THRESHOLD or (
        n > FAILURE_ALERT_THRESHOLD and n % FAILURE_REALERT_EVERY == 0
    ):
        telegram_send(
            cfg,
            f"⚠️ <b>Ticket monitor</b> — {_esc(src.name)}\n"
            f"Could not read the site {n} runs in a row.\n"
            f"<code>{_esc(str(err))[:300]}</code>",
        )


# --------------------------------------------------------------------------- #
# Entry point                                                                 #
# --------------------------------------------------------------------------- #


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="FPF ticket monitor")
    parser.add_argument("--mode",
                        choices=("normal", "diagnostic", "test", "chatid", "probe"),
                        default="normal")
    parser.add_argument("--dump-file", default="page.html",
                        help="Diagnostic mode writes <source_id>-<dump-file>.")
    args = parser.parse_args(argv)

    logging.basicConfig(
        level=logging.INFO,
        format="%(asctime)s %(levelname)s %(message)s",
        stream=sys.stderr,
    )
    cfg = Config()

    if args.mode == "diagnostic":
        return run_diagnostic(cfg, args.dump_file)
    if args.mode == "probe":
        return run_probe(cfg)
    if args.mode == "chatid":
        return run_chatid(cfg)
    if args.mode == "test":
        return run_test(cfg)
    return run_normal(cfg)


if __name__ == "__main__":
    raise SystemExit(main())
