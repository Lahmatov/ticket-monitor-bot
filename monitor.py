#!/usr/bin/env python3
"""
FPF ticket monitor -> Telegram notifier.

Watches the Portuguese Football Federation ticketing site
(https://bilheteira.fpf.pt/) for Portugal national-team matches and sends a
Telegram message as soon as a match becomes buyable.

Runs inside a GitHub Actions job. With ``--loop-minutes N`` the job stays
alive for N minutes and checks whenever the cadence below says a check is due
(GitHub's own cron is too unreliable to drive the cadence by itself); without
it, one invocation checks once and exits. Matches that were already played
are hidden.

Cadence (enforced here, not by cron, so it is correct across DST):
  * Daytime in Lisbon (07:00-00:00): about every 40 minutes.
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

# Minimum spacing between checks (enforced here, not by cron).
DAY_MIN_INTERVAL_MIN = 40     # ~40 min during the day
NIGHT_MIN_INTERVAL_MIN = 120  # ~2h at night (Lisbon 00:00-07:00)

# --loop mode: how often the long-running job wakes up to see if a check is due.
LOOP_POLL_SEC = 60

# A match is hidden once it kicked off more than this long ago (some ticket
# APIs keep a game "open" for a while after it was played).
PAST_GRACE_HOURS = 3

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
                 event_selector="", title_selector="", link_selector="",
                 api_url="", api_type="html", browse_url="",
                 wait_selector="", wait_ms=0, parser=""):
        self.id = str(id).strip()
        self.name = str(name).strip() or self.id
        self.url = str(url).strip()
        self.keywords = [k.strip().lower() for k in (keywords or []) if k.strip()]
        self.exclude_keywords = [k.strip().lower()
                                 for k in (exclude_keywords or []) if k.strip()]
        self.event_selector = (event_selector or "").strip()
        self.title_selector = (title_selector or "").strip()
        self.link_selector = (link_selector or "").strip()
        # api_type: "html" (scrape), "json" (fetch api_url), or "browser"
        # (render the page with a headless browser, then scrape the DOM).
        self.api_url = (api_url or "").strip()
        self.api_type = (api_type or "html").strip().lower()
        self.browse_url = (browse_url or "").strip() or self.url
        self.wait_selector = (wait_selector or "").strip()
        self.wait_ms = int(wait_ms or 0)
        # Optional site-specific DOM parser (e.g. "sporting").
        self.parser = (parser or "").strip().lower()


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
        # Send a summary of every check (even when nothing is on sale).
        self.report_every_run = os.environ.get("REPORT_EVERY_RUN", "").strip().lower() \
            in ("1", "true", "yes", "on")
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
    data.setdefault("last_check_utc", None)  # min-interval gate (day/night)
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
    """Return (act, is_night). Enforces the day/night min-interval, DST-correct."""
    is_night = now_lisbon.hour < 7  # 00:00-06:59 Lisbon
    interval = NIGHT_MIN_INTERVAL_MIN if is_night else DAY_MIN_INTERVAL_MIN
    last = _parse_iso(state.get("last_check_utc"))
    if last is not None:
        elapsed_min = (_now_utc() - last).total_seconds() / 60.0
        if elapsed_min < interval:
            log.debug("Run skipped: only %.0f min since last check (< %d).",
                     elapsed_min, interval)
            return False, is_night
    return True, is_night


# --------------------------------------------------------------------------- #
# Fetch                                                                       #
# --------------------------------------------------------------------------- #


def fetch(url: str, accept: str = "text/html,application/xhtml+xml",
          json_body: dict | None = None, extra_headers: dict | None = None) -> str:
    """GET url (or POST json_body) with retries; return the response text."""
    headers = {
        "User-Agent": USER_AGENT,
        "Accept-Language": "pt-PT,pt;q=0.9,en;q=0.8",
        "Accept": accept,
        **(extra_headers or {}),
    }
    last_err: Exception | None = None
    for attempt in range(1, REQUEST_RETRIES + 1):
        try:
            if json_body is not None:
                resp = requests.post(url, json=json_body, headers=headers,
                                     timeout=REQUEST_TIMEOUT)
            else:
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
    __slots__ = ("id", "title", "url", "date", "status", "context", "extra", "start")

    def __init__(self, id_, title, url, date, status, context, extra="", start=None):
        self.id = id_
        self.title = title
        self.url = url
        self.date = date
        self.status = status
        self.context = context
        self.extra = extra  # optional secondary line (competition, time, …)
        self.start = start  # aware datetime of kick-off, if known

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


_JSON_TITLE_KEYS = ("name", "title", "designation", "eventname", "description",
                    "designacao", "designação", "nome", "evento")
_JSON_DATE_KEYS = ("date", "eventdate", "startdate", "datestart", "sessiondate",
                   "data", "datahora", "dataevento", "datainicio")
_JSON_ID_KEYS = ("id", "eventid", "code", "codigo", "slug", "guid")
_JSON_URL_KEYS = ("url", "link", "detailurl", "ligacao", "href")
_JSON_STATUS_KEYS = ("status", "state", "estado", "availability", "disponibilidade",
                     "onsale", "available", "disponivel", "salesopen", "isonsale",
                     "situacao")


def _first_str(d: dict, keys) -> str:
    for k, v in d.items():
        if k.lower() in keys and isinstance(v, str) and v.strip():
            return v.strip()
    return ""


_JSON_SOLD_OUT_KEYS = ("issoldout", "soldout", "esgotado", "isesgotado")


def _json_status(item: dict) -> str:
    # Explicit sold-out flag wins (FPF: "isSoldOut": true).
    for k, v in item.items():
        if k.lower() in _JSON_SOLD_OUT_KEYS and v is True:
            return "SOLD_OUT"
    for k, v in item.items():
        if k.lower() not in _JSON_STATUS_KEYS:
            continue
        if isinstance(v, bool):
            return "AVAILABLE" if v else "SOLD_OUT"
        if isinstance(v, str):
            s = classify_status(v, has_buy_link=False)
            if s != "UNKNOWN":
                return s
    # No explicit status: this endpoint lists sellable/announced events, so
    # presence means it's worth notifying about.
    return "AVAILABLE"


def _iter_json_items(data):
    if isinstance(data, list):
        return [x for x in data if isinstance(x, dict)]
    if isinstance(data, dict):
        for key in ("data", "items", "events", "eventos", "result", "results",
                    "value", "list", "d"):
            for k, v in data.items():
                if k.lower() == key and isinstance(v, list):
                    return [x for x in v if isinstance(x, dict)]
        # a single event object
        return [data]
    return []


def parse_json_events(data, src: "Source") -> list[Event]:
    events: list[Event] = []
    for item in _iter_json_items(data):
        title = _first_str(item, _JSON_TITLE_KEYS)
        if not title:
            # build from home/away teams if present
            home = _first_str(item, ("hometeam", "home", "equipacasa", "casa"))
            away = _first_str(item, ("awayteam", "away", "equipavisitante", "fora"))
            if home or away:
                title = f"{home} x {away}".strip(" x")
        context = _norm_ws(json.dumps(item, ensure_ascii=False).lower())
        if not title:
            title = context[:80]
        date = _first_str(item, _JSON_DATE_KEYS)
        rel = _first_str(item, _JSON_URL_KEYS)
        url = urljoin(src.url, rel) if rel else src.url
        eid = _first_str(item, _JSON_ID_KEYS) or _event_id(url, title)
        comp = _first_str(item, ("competition", "competicao", "competição",
                                 "stage", "phase", "venue", "local", "stadium",
                                 "estadio", "location"))
        start = _parse_start(date)
        shown = _fmt_iso_datetime(date) if start else date
        events.append(Event(str(eid), title, url, shown or None,
                            _json_status(item), context[:400], extra=comp,
                            start=start))
    return events


def render_with_browser(url: str, wait_selector: str = "", wait_ms: int = 0,
                        capture: bool = False):
    """Render a JS page with headless Chromium and return the final HTML.

    If capture=True, also return a list of (url, status, content_type, body)
    for API-looking XHR/fetch responses seen during the load (for diagnostics),
    as a tuple (html, captures).
    """
    from playwright.sync_api import sync_playwright  # lazy: only browser sources

    launch: dict = {"headless": True, "args": ["--no-sandbox",
                                               "--disable-dev-shm-usage"]}
    exe = os.environ.get("PW_CHROMIUM", "").strip()
    if exe:
        launch["executable_path"] = exe
    captures: list = []

    def _on_response(resp):
        try:
            ct = resp.headers.get("content-type", "")
            u = resp.url
            interesting = "json" in ct or any(
                k in u.lower() for k in ("api", "game", "event", "bilhet",
                                         "ticket", "sess", "sport", "graphql"))
            if not interesting or u.endswith((".js", ".css", ".png", ".jpg",
                                              ".svg", ".woff", ".woff2")):
                return
            body = ""
            if "json" in ct:
                try:
                    body = resp.text()[:600]
                except Exception:  # noqa: BLE001
                    body = "(body unavailable)"
            captures.append((u, resp.status, ct, body))
        except Exception:  # noqa: BLE001 - never let capture break render
            pass

    with sync_playwright() as p:
        browser = p.chromium.launch(**launch)
        try:
            page = browser.new_page(user_agent=USER_AGENT, locale="pt-PT")
            if capture:
                page.on("response", _on_response)
            page.goto(url, wait_until="networkidle", timeout=45000)
            if wait_selector:
                try:
                    page.wait_for_selector(wait_selector, timeout=15000)
                except Exception:  # noqa: BLE001 - best effort
                    pass
            if wait_ms:
                page.wait_for_timeout(wait_ms)
            html = page.content()
            return (html, captures) if capture else html
        finally:
            browser.close()


def _fmt_iso_datetime(value: str) -> str:
    """'2026-09-09T20:00:00' -> '09.09 20:00'; passthrough on failure."""
    try:
        dt = datetime.fromisoformat(value)
        return dt.strftime("%d.%m %H:%M")
    except (ValueError, TypeError):
        return value or ""


def _parse_start(value) -> datetime | None:
    """ISO date/time -> aware datetime; naive values are Lisbon local time."""
    if not isinstance(value, str) or not value.strip():
        return None
    try:
        dt = datetime.fromisoformat(value.strip().replace("Z", "+00:00"))
    except ValueError:
        return None
    return dt if dt.tzinfo else dt.replace(tzinfo=LISBON)


def drop_past(events: list[Event], now: datetime | None = None) -> list[Event]:
    """Remove matches that were already played; keep undated ones. Sort by date."""
    now = now or _now_utc()
    cutoff_sec = PAST_GRACE_HOURS * 3600
    kept = [e for e in events
            if e.start is None or (now - e.start).total_seconds() <= cutoff_sec]
    if len(kept) != len(events):
        log.info("Dropped %d already-played match(es).", len(events) - len(kept))
    far = datetime.max.replace(tzinfo=timezone.utc)
    return sorted(kept, key=lambda e: e.start or far)


def parse_sporting_api(data, src: "Source") -> list[Event]:
    """Parse tickets.sporting.pt /api/match/allopengames JSON (all open games)."""
    games = []
    if isinstance(data, dict):
        d = data.get("data")
        if isinstance(d, dict) and isinstance(d.get("openGames"), list):
            games = d["openGames"]
        elif isinstance(data.get("openGames"), list):
            games = data["openGames"]
    events: list[Event] = []
    for g in games:
        if not isinstance(g, dict):
            continue
        # Football only (drops futsal/handball/other modalities).
        if str(g.get("modality", "")).strip().lower() not in ("futebol", "football"):
            continue
        home = _norm_ws(str((g.get("homeTeam") or {}).get("name", "")))
        away = _norm_ws(str((g.get("awayTeam") or {}).get("name", "")))
        title = " x ".join(t for t in (home, away) if t) or "Sporting CP"
        # "disabledReasonDesc" is the label on the site's disabled buy button
        # ("Brevemente disponível", "Esgotado", …). allowSale stays true even
        # then, so a reason means "not buyable right now".
        reason = _norm_ws(str(g.get("disabledReasonDesc") or ""))
        if g.get("soldOut") or _contains_any(reason, SOLD_OUT_WORDS):
            status = "SOLD_OUT"
        elif reason or not g.get("allowSale"):
            status = "SOON"
        else:
            status = "AVAILABLE"
        comp = _norm_ws(str(g.get("competition", "")))
        if g.get("member") and not g.get("public"):
            comp = f"{comp} · members (sócios) only" if comp else "members (sócios) only"
        if status == "SOON" and reason:
            label = "coming soon" if "brevemente" in reason.lower() else reason
            comp = f"{comp} · site: {label}" if comp else f"site: {label}"
        when = _fmt_iso_datetime(str(g.get("date", "")))
        eid = str(g.get("id") or _event_id("", f"{title}-{g.get('date','')}"))
        context = _norm_ws(f"{title} {comp} {g.get('modality','')}")
        events.append(Event(eid, title, src.browse_url or src.url, when or None,
                            status, context, extra=comp,
                            start=_parse_start(g.get("date"))))
    return events


FCPORTO_QUERY = """
query getHomeMatches($pageSize: Int!, $matchDate: DateFilter!, $sport: SportId) {
  matchesByDate(filters: {limitMatchDates: $pageSize, sport: $sport, matchDate: $matchDate}) {
    date
    matches {
      id
      sport
      competition { name sport }
      competitionPhase
      homeTeam { shortName fullName }
      awayTeam { shortName fullName }
      localStartsAt
      localSaleStartsAt
      status
    }
  }
}
"""

# bilhetes.fcporto.pt match.status -> our status (unknown values -> UNKNOWN,
# shown raw in the report so they can be mapped here).
_FCPORTO_STATUS = {
    "SOLD_OUT": "SOLD_OUT",
    "ON_SALE": "AVAILABLE", "AVAILABLE": "AVAILABLE", "OPEN": "AVAILABLE",
    "SELLING": "AVAILABLE", "ACTIVE": "AVAILABLE", "PUBLISHED": "AVAILABLE",
    "SOON": "SOON", "COMING_SOON": "SOON", "NOT_STARTED": "SOON",
    "SCHEDULED": "SOON", "UPCOMING": "SOON", "PRE_SALE": "SOON",
    "CLOSED": "SOLD_OUT", "SALE_CLOSED": "SOLD_OUT", "ENDED": "SOLD_OUT",
}


def fetch_fcporto(src: "Source") -> str:
    """POST the GraphQL query the bilhetes.fcporto.pt home page uses."""
    today = datetime.now(LISBON).strftime("%Y-%m-%d")
    body = {"query": FCPORTO_QUERY,
            "variables": {"pageSize": 12, "matchDate": {"from": today},
                          "sport": "FOOTBALL"}}
    return fetch(src.api_url, accept="application/json", json_body=body,
                 extra_headers={"Origin": "https://bilhetes.fcporto.pt",
                                "Referer": "https://bilhetes.fcporto.pt/"})


def parse_fcporto(data, src: "Source") -> list[Event]:
    """Parse the matchesByDate GraphQL response; FC Porto first team only."""
    if not isinstance(data, dict):
        return []
    if data.get("errors"):
        raise RuntimeError(f"GraphQL error: {str(data['errors'])[:200]}")
    days = (data.get("data") or {}).get("matchesByDate") or []
    events: list[Event] = []
    now = _now_utc()
    for day in days:
        for g in (day or {}).get("matches") or []:
            if not isinstance(g, dict):
                continue
            if str(g.get("sport") or "").upper() not in ("FOOTBALL", ""):
                continue
            home = _norm_ws(str((g.get("homeTeam") or {}).get("shortName") or ""))
            away = _norm_ws(str((g.get("awayTeam") or {}).get("shortName") or ""))
            # First team only: one side must be exactly "FC Porto" (the B and
            # women's teams carry a suffix).
            if "fc porto" not in (home.lower(), away.lower()):
                continue
            title = " x ".join(t for t in (home, away) if t)
            raw = str(g.get("status") or "").upper()
            status = _FCPORTO_STATUS.get(raw, "UNKNOWN")
            sale_start = _parse_start(g.get("localSaleStartsAt"))
            if status == "AVAILABLE" and sale_start and sale_start > now:
                status = "SOON"
            comp = _norm_ws(" · ".join(
                x for x in (str((g.get("competition") or {}).get("name") or ""),
                            str(g.get("competitionPhase") or "")) if x))
            notes = [comp] if comp else []
            if status == "SOON" and sale_start and sale_start > now:
                notes.append("sale opens " + sale_start.astimezone(LISBON).strftime("%d.%m %H:%M"))
            if status == "UNKNOWN":
                notes.append(f"site status: {raw or '?'}")
            start = _parse_start(g.get("localStartsAt"))
            eid = str(g.get("id") or _event_id("", f"{title}-{g.get('localStartsAt')}"))
            events.append(Event(eid, title, f"https://bilhetes.fcporto.pt/jogos/{eid}",
                                start.astimezone(LISBON).strftime("%d.%m %H:%M") if start else None,
                                status, _norm_ws(f"{title} {comp} {raw}"),
                                extra=" · ".join(notes), start=start))
    return events


_PT_MONTHS = {"jan": 1, "fev": 2, "mar": 3, "abr": 4, "mai": 5, "jun": 6,
              "jul": 7, "ago": 8, "set": 9, "out": 10, "nov": 11, "dez": 12}
_PT_DATE_RE = re.compile(
    r"(\d{1,2})\s*(?:de\s+)?([a-zç]{3})[a-zç]*\.?,?\s*(?:de\s+\d{4}\s*)?"
    r"(?:às|as|-|,)?\s*(\d{1,2})\s*[h:]\s*(\d{2})", re.IGNORECASE)


def _parse_pt_datetime(text: str, now: datetime | None = None) -> datetime | None:
    """'Dom 11 Out 18h00' / '20 de outubro às 20:00' -> aware Lisbon datetime.

    The year is not shown on these sites: pick the one that puts the match
    closest to now (a date >60 days in the past means next year).
    """
    m = _PT_DATE_RE.search(text or "")
    if not m:
        return None
    month = _PT_MONTHS.get(m.group(2).lower()[:3])
    if not month:
        return None
    now = (now or _now_utc()).astimezone(LISBON)
    try:
        dt = datetime(now.year, month, int(m.group(1)), int(m.group(3)),
                      int(m.group(4)), tzinfo=LISBON)
    except ValueError:
        return None
    if (now - dt).days > 60:
        dt = dt.replace(year=dt.year + 1)
    return dt


# Benfica status badge (div.button-type-container) -> (status, note)
_BENFICA_BADGES = (
    ("esgotado", "SOLD_OUT", ""),
    ("mercado secund", "RESALE", ""),
    ("por iniciar", "SOON", ""),
    ("exclusivo", "AVAILABLE", None),  # None -> use the badge text as the note
)
_BENFICA_BADGE_EN = {
    "exclusivo a sócios e adeptos registados": "members & registered fans only",
    "exclusivo a sócios com quotas em dia": "paid-up members only",
    "exclusivo a sócios com red pass": "Red Pass members only",
}


def parse_benfica(html: str, src: "Source") -> list[Event]:
    """Parse slbenfica.pt/pt-pt/bilhetes (server-rendered match cards).

    Only the "Equipa A" tab is used (the page also lists women's, B team,
    U23 and Youth League games).
    """
    soup = BeautifulSoup(html, "html.parser")
    events: list[Event] = []
    for card in soup.select("section.game-module"):
        tab = card.find_parent(class_="tab-nav")
        if tab is not None and "equipaA" not in (tab.get("class") or []):
            continue  # another team's tab
        kind = _norm_ws(card.select_one(".type-game").get_text(" ")) \
            if card.select_one(".type-game") else ""
        if kind and kind.lower() != "futebol":
            continue
        link = None
        for a in card.select(".buttons-tickets a[href]"):
            href = a["href"]
            if "/loja/bilhetes/jogos/" in href and not href.endswith("#"):
                link = a
                break
        if tab is None and (link is None or not re.search(r"/jogos/compra(v2)?/", link["href"])):
            continue  # no tab info: keep only first-team ticket links
        teams = [_norm_ws(h.get_text(" ")) for h in card.select(".team h3.hidden-xs")]
        title = " x ".join(t for t in teams if t) or "SL Benfica"
        comp = _norm_ws(card.select_one(".type-liga").get_text(" ")) \
            if card.select_one(".type-liga") else ""
        when_el = card.select_one(".game_bar h5")
        when_txt = _norm_ws(when_el.get_text(" ")) if when_el else ""
        start = _parse_pt_datetime(when_txt)

        badge = ""
        box = card.select_one(".button-type-container")
        if box is not None:  # commented-out <p>s are Comments, not tags
            badge = " ".join(_norm_ws(p.get_text(" ")) for p in box.find_all("p"))
        status, note = "", ""
        for needle, st, nt in _BENFICA_BADGES:
            if needle in badge.lower():
                status = st
                note = _BENFICA_BADGE_EN.get(badge.lower(), badge) if nt is None else nt
                break
        if not status:
            buttons = card.select_one(".buttons-tickets")
            hidden = buttons is not None and "none" in (buttons.get("style") or "")
            status = "AVAILABLE" if link is not None and not hidden else "SOON"
        extra = " · ".join(x for x in (comp, note) if x)
        url = link["href"] if link is not None else src.url
        eid = url.rstrip("/").rsplit("/", 1)[-1] if link is not None \
            else _event_id("", f"{title}-{when_txt}")
        events.append(Event(eid, title, url,
                            start.strftime("%d.%m %H:%M") if start else (when_txt or None),
                            status, _norm_ws(f"{title} {comp} {badge}"), extra=extra,
                            start=start))
    return events


def parse_sporting_dom(html: str, src: "Source") -> list[Event]:
    """Parse tickets.sporting.pt rendered DOM (Angular 'game' cards)."""
    soup = BeautifulSoup(html, "html.parser")
    events: list[Event] = []
    for cont in soup.select(".game-clubs-container"):
        names: list[str] = []
        for club in cont.select(".game-club"):
            sp = club.find("span")
            txt = _norm_ws(sp.get_text(" ", strip=True)) if sp else ""
            if txt:
                names.append(txt)
        if len(names) < 2:
            continue
        title = f"{names[0]} x {names[1]}"
        time_el = cont.select_one(".game-time span")
        time_txt = _norm_ws(time_el.get_text()) if time_el else ""
        # Climb to the match card: the smallest ancestor that includes this
        # match's buy/sold button, without swallowing a sibling match.
        card = cont
        for _ in range(8):
            parent = card.parent
            if parent is None or len(parent.select(".game-clubs-container")) > 1:
                break
            card = parent
            if card.select_one(".p-button-label, button"):
                break
        card_text = _norm_ws(card.get_text(" ", strip=True))
        label_el = card.select_one(".p-button-label")
        label = _norm_ws(label_el.get_text()) if label_el else card_text
        status = classify_status(label, has_buy_link=("comprar" in label.lower()))
        comp_el = card.select_one(".competition, .game-competition")
        comp = _norm_ws(comp_el.get_text(" ", strip=True)) if comp_el else ""
        date = _extract_date(card_text)
        when = ", ".join(x for x in (date, time_txt) if x) or None
        context = _norm_ws(f"{title} {comp} {time_txt} {card_text}")[:400]
        eid = _event_id("", f"{title}-{comp}")
        events.append(Event(eid, title, src.browse_url, when, status, context,
                            extra=comp))
    return events


def load_events(src: "Source") -> list[Event]:
    """Fetch and parse upcoming events (already-played matches are dropped)."""
    return drop_past(_load_events_raw(src))


def _load_events_raw(src: "Source") -> list[Event]:
    """Fetch and parse events for a source (JSON API, browser render, or HTML)."""
    if src.api_type == "json" and src.api_url:
        return parse_source_json(json.loads(fetch_source_json(src)), src)
    if src.api_type == "browser":
        html = render_with_browser(src.browse_url, src.wait_selector, src.wait_ms)
        if src.parser == "sporting":
            return parse_sporting_dom(html, src)
        return parse_events(html, src.browse_url, src)
    page = fetch(src.url)
    return parse_html_source(page, src)


def fetch_source_json(src: "Source") -> str:
    if src.parser == "fcporto":
        return fetch_fcporto(src)
    return fetch(src.api_url, accept="application/json, text/plain, */*")


def parse_source_json(data, src: "Source") -> list[Event]:
    if src.parser == "sporting_api":
        return parse_sporting_api(data, src)
    if src.parser == "fcporto":
        return parse_fcporto(data, src)
    return parse_json_events(data, src)


def parse_html_source(page: str, src: "Source") -> list[Event]:
    if src.parser == "benfica":
        return parse_benfica(page, src)
    return parse_events(page, src.url, src)


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
    lines = [f"\U0001F3AB <b>Tickets on sale!</b> — {_esc(source_name)}",
             "", f"<b>{_esc(event.title)}</b>"]
    if event.extra:
        lines.append(f"\U0001F3C6 {_esc(event.extra)}")
    if event.date:
        lines.append(f"\U0001F4C5 {_esc(event.date)}")
    if event.url:
        lines.append("")
        lines.append(f'\U0001F517 <a href="{_esc(event.url)}">Buy now</a>')
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
        target = src.api_url if (src.api_type == "json" and src.api_url) else src.url
        print(f"\n{'=' * 70}\nSOURCE: {src.name} [{src.id}] ({src.api_type}) -> {target}\n{'=' * 70}")
        if src.api_type == "json" and src.api_url:
            try:
                raw = fetch_source_json(src)
            except Exception as err:  # noqa: BLE001
                print(f"FETCH FAILED: {err}")
                continue
            print(f"Fetched {len(raw)} bytes of JSON; head: {raw[:200]}")
            try:
                events = parse_source_json(json.loads(raw), src)
            except Exception as err:  # noqa: BLE001
                print(f"JSON parse failed: {err}")
                continue
            print(f"\nParsed {len(events)} event(s):\n")
        elif src.api_type == "browser":
            try:
                page, caps = render_with_browser(src.browse_url, src.wait_selector,
                                                 src.wait_ms, capture=True)
            except Exception as err:  # noqa: BLE001
                print(f"RENDER FAILED: {err}")
                continue
            print(f"Rendered {len(page)} bytes")
            print(f"\n--- {len(caps)} API-looking network responses ---")
            for (u, status, ct, body) in caps[:25]:
                print(f"[{status}] {ct[:40]} {u}")
                if body:
                    print("    body:", _norm_ws(body)[:300])
            print("--- end network ---")
            if dump_file:
                out = f"{src.id}-{dump_file}"
                with open(out, "w", encoding="utf-8") as fh:
                    fh.write(page)
                print(f"Rendered HTML written to {out}")
            if src.parser == "sporting":
                events = parse_sporting_dom(page, src)
            else:
                events = parse_events(page, src.browse_url, src)
            if not events:
                _diag_hints(page)
                _dump_html_context(page, ["Esgotado", "Comprar", "Betclic",
                                          "SPORTING", "Bilhet", "Jogo Fora",
                                          "20:15"])
            print(f"\nParsed {len(events)} candidate event link(s):\n")
        else:
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
            events = parse_html_source(page, src)
            if not events:
                _diag_hints(page)
            print(f"\nParsed {len(events)} candidate event link(s):\n")
        upcoming = drop_past(events)
        for ev in events:
            star = "  <-- keyword match" if matches_keywords(ev, src) else ""
            if ev not in upcoming:
                star = "  (already played -> hidden)"
            print(f"[{ev.status:9}] {ev.title[:70]!r} | {ev.date} | {ev.extra} | {ev.url}{star}")
        matched = [e for e in upcoming if matches_keywords(e, src)]
        kw = src.keywords or "(all events)"
        print(f"\nKeywords {kw}: {len(matched)} match; "
              f"available now: {sum(1 for e in matched if e.status == 'AVAILABLE')}")
    return 0


def _dump_html_context(html: str, markers) -> None:
    """Print raw-HTML windows around the first hit of each marker (to read the
    DOM structure / class names of match cards in a rendered SPA)."""
    print("\n--- HTML context around markers ---")
    for mk in markers:
        i = html.lower().find(mk.lower())
        if i < 0:
            print(f"[{mk}] not found")
            continue
        window = html[max(0, i - 260):i + 140]
        print(f"[{mk}] …{window}…")
    print("--- end context ---\n")


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
    print("  body (first 2500 chars):", _norm_ws(r.text)[:2500] or "(empty)")


_CHUNK_RE = re.compile(r'["\'(](?:\./|/)?((?:chunk|[a-z0-9\-]+)-[A-Z0-9]{8}\.js)["\')]')


def _probe_grep(url: str, terms: str, _seen: set | None = None) -> None:
    """Download url and print context around each occurrence of each term.

    terms is comma-separated; matching is case-insensitive. For a .js bundle,
    lazily-loaded chunks it references (esbuild "chunk-XXXXXXXX.js") are
    scanned too; files with no hits are summarised in one line.
    """
    seen = _seen if _seen is not None else set()
    if url in seen or len(seen) >= 150:
        return
    seen.add(url)
    try:
        body = fetch(url)
    except Exception as err:  # noqa: BLE001
        print(f"\n=== GREP in {url}: fetch failed: {err} ===")
        return
    found = []
    for term in terms.split(","):
        term = term.strip()
        if not term:
            continue
        idxs = [m.start() for m in re.finditer(re.escape(term), body, re.IGNORECASE)]
        if idxs:
            found.append((term, idxs))
    if found:
        print(f"\n=== GREP in {url} ({len(body)} bytes) ===")
        for term, idxs in found:
            print(f"  [{term}] {len(idxs)} hit(s)")
            for i in idxs[:6]:
                snippet = body[max(0, i - 150):i + 150].replace("\n", " ")
                print("     …", snippet, "…")
    else:
        print(f"  (no hits in {url}, {len(body)} bytes)")
    if url.endswith(".js"):
        for name in sorted(set(_CHUNK_RE.findall(body))):
            _probe_grep(urljoin(url, name), terms, seen)


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


_STATUS_LABEL = {
    "AVAILABLE": "🟢 on sale",
    "SOLD_OUT": "🔴 sold out",
    "SOON": "🟡 not on sale yet",
    "RESALE": "🟠 resale only (official secondary market)",
    "UNKNOWN": "⚪️ status unclear",
}


def _summary_lines(src: "Source", matched: list) -> list[str]:
    """Human-readable report lines for one source (for the per-run heartbeat)."""
    lines = [f"<b>{_esc(src.name)}</b>: {len(matched)} match(es)"]
    if not matched:
        lines.append("• no upcoming matches")
        return lines
    for ev in matched:
        parts = [f"{_STATUS_LABEL.get(ev.status, ev.status)}: {ev.title}"]
        if ev.extra:
            parts.append(ev.extra)
        if ev.date:
            parts.append(ev.date)
        lines.append("• " + _esc(" · ".join(parts)))
    return lines


def _process_source(cfg: Config, src: "Source", state: dict,
                    now_iso: str) -> tuple[bool, list[str]]:
    """Check one source; return (state_changed, report_lines)."""
    notified = state["notified"]
    failures = state["failures"]
    dirty = False
    try:
        events = load_events(src)
    except Exception as err:  # noqa: BLE001 - handle any failure uniformly
        log.error("[%s] fetch/parse failed: %s", src.id, err)
        failures[src.id] = failures.get(src.id, 0) + 1
        _maybe_alert_failure(cfg, src, failures[src.id], err)
        return True, [f"<b>{_esc(src.name)}</b>: ⚠️ could not read the site "
                      f"({_esc(str(err)[:80])})"]

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
            # Not buyable any more: forget it, so tickets coming back (returns,
            # a new sale phase) trigger a fresh alert.
            del notified[key]
            dirty = True
    return dirty, _summary_lines(src, matched)


def run_normal(cfg: Config) -> int:
    state = load_state(cfg.state_file)
    now_lisbon = datetime.now(LISBON)
    act, _is_night = should_act(now_lisbon, state)
    if not act:
        return 0

    state["last_check_utc"] = _now_utc().isoformat()  # for the min-interval gate
    dirty = True

    now_iso = _now_utc().isoformat()
    report: list[str] = []
    for src in cfg.sources:
        changed, lines = _process_source(cfg, src, state, now_iso)
        dirty = dirty or changed
        report.extend(lines)

    if cfg.report_every_run:
        header = f"🔎 <b>Ticket check</b> · {now_lisbon.strftime('%H:%M %d.%m')}"
        telegram_send(cfg, header + "\n\n" + "\n".join(report))

    if _prune_state(state, now_iso):
        dirty = True

    if dirty:
        save_state(cfg.state_file, state)
        set_output("state_changed", "true")
    return 0


def run_loop(cfg: Config, minutes: float) -> int:
    """Stay alive for `minutes`, running a check whenever one is due.

    GitHub's cron fires every few hours at best, so instead of relying on it
    the job itself keeps the ~40 min / ~2 h cadence via should_act().
    """
    deadline = time.monotonic() + minutes * 60
    log.info("Loop mode: running for %.0f min.", minutes)
    while True:
        try:
            run_normal(cfg)
        except Exception:  # noqa: BLE001 - one bad check must not end the loop
            log.exception("Check failed; will retry on the next tick.")
        if time.monotonic() + LOOP_POLL_SEC >= deadline:
            break
        time.sleep(LOOP_POLL_SEC)
    log.info("Loop mode: done.")
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
    parser.add_argument("--loop-minutes", type=float, default=0,
                        help="normal mode: keep running this long, checking "
                             "whenever the day/night interval is due.")
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
    if args.loop_minutes > 0:
        return run_loop(cfg, args.loop_minutes)
    return run_normal(cfg)


if __name__ == "__main__":
    raise SystemExit(main())
