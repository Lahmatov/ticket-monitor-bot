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
  * Daytime in Lisbon (07:00-00:00): every 20-40 minutes (random).
  * Night in Lisbon   (00:00-07:00): every 100-140 minutes (random).

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
import random
import time
import unicodedata
from datetime import datetime, timezone
from urllib.parse import parse_qsl, urljoin, urlparse
from zoneinfo import ZoneInfo

import requests
from bs4 import BeautifulSoup

# --------------------------------------------------------------------------- #
# Configuration                                                               #
# --------------------------------------------------------------------------- #

LISBON = ZoneInfo("Europe/Lisbon")

# Minimum spacing between checks (enforced here, not by cron).
# Gap between checks is drawn at random from these ranges (minutes) after
# every check, so the sites don't see a clockwork pattern.
DAY_INTERVAL_RANGE_MIN = (20, 40)     # 07:00-00:00 Lisbon
NIGHT_INTERVAL_RANGE_MIN = (100, 140)  # 00:00-07:00 Lisbon

# --loop mode: how often the long-running job wakes up to see if a check is due.
LOOP_POLL_SEC = 60
# --loop mode: a run may end early to escape an IP ban only after this long.
ROTATE_MIN_ELAPSED_MIN = 20

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
                 wait_selector="", wait_ms=0, parser="", emoji="", event_url="",
                 member_alerts=False, club=False, team="", team_name="",
                 sport="football"):
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
        self.emoji = (emoji or "").strip()  # shown before the team's heading
        # Per-event buy link template for generic JSON sources, e.g.
        # "https://bilheteira.fpf.pt/checkOut/{id}".
        self.event_url = (event_url or "").strip()
        # The owner is a club member (sócio) here: members-only sales alert
        # the owner too, not just public sales.
        self.member_alerts = bool(member_alerts)
        # A club with members (sócios): offered in the onboarding's
        # membership question.
        self.club = bool(club)
        # Several sources can belong to one team (one per sport); onboarding
        # asks for sports and teams, a user receives the sources matching both.
        self.team = (team or "").strip() or self.id
        self.team_name = (team_name or "").strip() or self.name
        self.sport = (sport or "football").strip().lower()


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
        # One or more recipients: "123" or "123,456" (owner first).
        self.telegram_chats = [c for c in re.split(r"[\s,;]+",
                                                   os.environ.get("TELEGRAM_CHAT_ID", ""))
                               if c]
        self.telegram_chat = self.telegram_chats[0] if self.telegram_chats else ""
        self.subscribers: list[str] = []  # approved via the bot (from state)
        # ACCESS_MODE: "open" (default) = anyone who sends /start subscribes
        # at once, the owner just gets a notice; "approval" = the owner must
        # tap Allow first.
        self.open_access = (os.environ.get("ACCESS_MODE", "open").strip().lower()
                            != "approval")
        # REPORT_MODE: "changes" (default) = message only when a match's status
        # changes or a new match appears; "every" = full summary every check.
        # (Legacy REPORT_EVERY_RUN=1 means "every".)
        mode = os.environ.get("REPORT_MODE", "").strip().lower()
        if not mode:
            legacy = os.environ.get("REPORT_EVERY_RUN", "").strip().lower()
            mode = "every" if legacy in ("1", "true", "yes", "on") else "changes"
        self.report_mode = mode if mode in ("changes", "every") else "changes"
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
    data.setdefault("subscribers", {})  # chat_id -> {name, since}: approved by owner
    data.setdefault("pending", {})  # chat_id -> {name, requested}: awaiting owner
    data.setdefault("blocked", {})  # chat_id -> {name, since}: removed by the owner
    data.setdefault("prefs", {})  # chat_id -> {teams: [src ids], member: [src ids]}
    data.setdefault("prefs_draft", {})  # chat_id -> same, while onboarding
    data.setdefault("sale_phases", {})  # "src:game" -> {title, url, phases, ...}
    data.setdefault("phase_sent", {})  # reminder key -> when sent
    data.setdefault("awaiting", {})  # chat_id -> "members" while we wait for a reply
    data.setdefault("tg_offset", 0)  # next Telegram update_id to read
    return data


def save_state(path: str, state: dict) -> None:
    tmp = f"{path}.tmp"
    with open(tmp, "w", encoding="utf-8") as fh:
        json.dump(state, fh, ensure_ascii=False, indent=2, sort_keys=True)
    os.replace(tmp, path)


# --------------------------------------------------------------------------- #
# Scheduling window                                                           #
# --------------------------------------------------------------------------- #


def pick_next_gaps(state: dict) -> None:
    """Draw the random day/night gaps to wait after the check just made."""
    state["next_gap_day_min"] = round(random.uniform(*DAY_INTERVAL_RANGE_MIN), 1)
    state["next_gap_night_min"] = round(random.uniform(*NIGHT_INTERVAL_RANGE_MIN), 1)


def should_act(now_lisbon: datetime, state: dict) -> tuple[bool, bool]:
    """Return (act, is_night). Enforces the random day/night gap, DST-correct."""
    is_night = now_lisbon.hour < 7  # 00:00-06:59 Lisbon
    lo, hi = NIGHT_INTERVAL_RANGE_MIN if is_night else DAY_INTERVAL_RANGE_MIN
    key = "next_gap_night_min" if is_night else "next_gap_day_min"
    try:
        interval = float(state.get(key) or hi)
    except (TypeError, ValueError):
        interval = hi
    interval = min(max(interval, lo), hi)  # stale/odd stored values stay in range
    last = _parse_iso(state.get("last_check_utc"))
    if last is not None:
        elapsed_min = (_now_utc() - last).total_seconds() / 60.0
        if elapsed_min < interval:
            log.debug("Run skipped: only %.0f min since last check (< %.0f).",
                      elapsed_min, interval)
            return False, is_night
    return True, is_night


# --------------------------------------------------------------------------- #
# Fetch                                                                       #
# --------------------------------------------------------------------------- #


# Responses already fetched during the current check. Several sources share
# one site/API (one source per sport), so each URL is downloaded once per
# check. Cleared at the start of every check; failures are not cached.
_FETCH_MEMO: dict[tuple, "str | Exception"] = {}


def fetch(url: str, accept: str = "text/html,application/xhtml+xml",
          json_body: dict | None = None, extra_headers: dict | None = None,
          form_body: dict | None = None) -> str:
    """GET url (or POST json_body / form_body) with retries; return the text."""
    key = (url, accept, json.dumps(json_body, sort_keys=True) if json_body else "",
           json.dumps(form_body, sort_keys=True) if form_body else "")
    if key in _FETCH_MEMO:
        hit = _FETCH_MEMO[key]
        if isinstance(hit, Exception):
            raise hit  # failed earlier in this check: don't hammer the site again
        return hit
    try:
        text = _fetch_uncached(url, accept, json_body, extra_headers, form_body)
    except Exception as err:
        _FETCH_MEMO[key] = err
        raise
    _FETCH_MEMO[key] = text
    return text


def _fetch_uncached(url: str, accept: str, json_body: dict | None,
                    extra_headers: dict | None, form_body: dict | None = None) -> str:
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
            elif form_body is not None:
                resp = requests.post(url, data=form_body, headers=headers,
                                     timeout=REQUEST_TIMEOUT)
            else:
                resp = requests.get(url, headers=headers, timeout=REQUEST_TIMEOUT)
            if resp.status_code in (401, 403, 429):
                body = _norm_ws(resp.text[:400])
                if any(m in body.lower() for m in _BLOCK_MARKERS + ("forbidden",)):
                    # A firewall answer: retrying from the same IP won't help.
                    raise SiteBlockedError(
                        f"site blocked this server's IP (HTTP {resp.status_code}: {body[:80]})")
            resp.raise_for_status()
            if "charset" not in resp.headers.get("content-type", "").lower():
                resp.encoding = "utf-8"  # requests would assume ISO-8859-1
            return resp.text.lstrip("\ufeff")  # some sites prepend a UTF-8 BOM
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
    __slots__ = ("id", "title", "url", "date", "status", "context", "extra", "start",
                 "venue", "phases")

    def __init__(self, id_, title, url, date, status, context, extra="", start=None,
                 venue=""):
        self.id = id_
        self.title = title
        self.url = url
        self.date = date
        self.status = status
        self.context = context
        self.extra = extra  # optional secondary line (competition, time, …)
        self.start = start  # aware datetime of kick-off, if known
        self.venue = venue or ""  # stadium, if the site says
        self.phases: list[dict] = []  # Sporting sale phases (who may buy when)

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


def _first_id(item: dict) -> str:
    """First id-like value (string or integer), e.g. FPF's "eventID": 1630."""
    for k, v in item.items():
        if k.lower() in _JSON_ID_KEYS and isinstance(v, (str, int)) \
                and not isinstance(v, bool) and str(v).strip():
            return str(v).strip()
    return ""


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
        raw_id = _first_id(item)
        if src.event_url and raw_id and not rel:
            url = src.event_url.format(id=raw_id)  # direct checkout link
        eid = raw_id or _event_id(url, title)
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


FPF_BUY_URL = "https://bilheteira.fpf.pt/checkout/{code}"
# Youth / women's / futsal / beach national teams (Tags like "CZE,POR,SUB21",
# competitions like "CAMP. EUROPA S21 ..."): not the senior men's team.
_FPF_NOT_A_TEAM_TAG = re.compile(r"^(SUB\d*|U\d+|FEM\w*|PRAIA|BEACH)$", re.I)
_FPF_NOT_A_TEAM_COMP = re.compile(r"\bS\d{2}\b|\bsub[- ]?\d{2}|\bU\d{2}\b|femin|praia", re.I)


def _fmt_sale_opens(dt: datetime) -> str:
    """'sale opens Fri 6 Nov, 00:00' (Lisbon) - month spelled out so it can't
    be mistaken for today's dd.mm date."""
    d = dt.astimezone(LISBON)
    return f"sale opens {d.strftime('%a')} {d.day} {d.strftime('%b')}, {d.strftime('%H:%M')}"


# EventSalesStatusEnum on the FPF site (may arrive as name or number).
_FPF_SALES_STATUS = {"onsale": "OnSale", "1": "OnSale",
                     "comingsoon": "ComingSoon", "2": "ComingSoon",
                     "closed": "Closed", "3": "Closed"}


def parse_fpf_odata(data, src: "Source") -> list[Event]:
    """Parse score2-external-api.fpf.pt .../odata/Events (new FPF site, 2026-10).

    Senior men's national team matches only. Status mirrors the site's own
    canBuyTicket(): SalesStatus OnSale and not IsSoldOut -> on sale;
    ComingSoon -> soon ("To be announced soon"); Closed -> sale closed.
    Older responses carried a sale window (SaleStartDate/SaleEndDate)
    instead; without either signal the status is UNKNOWN, never "on sale".
    """
    items = data.get("value") if isinstance(data, dict) else data
    if not isinstance(items, list):
        raise RuntimeError("unexpected FPF response (no 'value' list)")
    now = _now_utc()
    events: list[Event] = []
    for it in items:
        if not isinstance(it, dict) or str(it.get("Type") or "Match") != "Match":
            continue
        tags = [t.strip() for t in str(it.get("Tags") or "").split(",") if t.strip()]
        comp = _norm_ws(str(it.get("CompetitionName") or ""))
        if any(_FPF_NOT_A_TEAM_TAG.match(t) for t in tags) or _FPF_NOT_A_TEAM_COMP.search(comp):
            continue
        # The FPF sells football and futsal; each source keeps its own sport.
        is_futsal = (any(t.upper() == "FUTSAL" for t in tags)
                     or "futsal" in f"{comp} {it.get('Name') or ''}".lower())
        if is_futsal != (src.sport == "futsal"):
            continue
        home = _norm_ws(str(it.get("HomeTeamName") or ""))
        away = _norm_ws(str(it.get("AwayTeamName") or ""))
        title = " x ".join(t for t in (home, away) if t) or _norm_ws(str(it.get("Name") or ""))
        sale_start = _parse_start(it.get("SaleStartDate"))
        sale_end = _parse_start(it.get("SaleEndDate"))
        sales = _FPF_SALES_STATUS.get(str(it.get("SalesStatus") or "").strip().lower())
        note = ""
        if sales == "ComingSoon":
            status = "SOON"
            if sale_start and now < sale_start:
                note = _fmt_sale_opens(sale_start)
        elif sales == "Closed":
            status, note = "SOLD_OUT", "online sale closed"
        elif sales == "OnSale":
            status = "SOLD_OUT" if it.get("IsSoldOut") else "AVAILABLE"
        elif it.get("SalesStatus") not in (None, ""):
            status = "UNKNOWN"
            note = f"site status: {it.get('SalesStatus')}"
        # Legacy shape: no SalesStatus, a sale window instead.
        elif it.get("IsSoldOut"):
            status = "SOLD_OUT"
        elif sale_start and now < sale_start:
            status = "SOON"
            note = _fmt_sale_opens(sale_start)
        elif sale_end and now > sale_end:
            status, note = "SOLD_OUT", "online sale closed"
        elif sale_start:
            status = "AVAILABLE"
        else:
            status, note = "UNKNOWN", "no sale info from FPF"
        phase = _norm_ws(str(it.get("CompetitionPhase") or ""))
        extra = " · ".join(x for x in (comp, phase, note) if x)
        start = _parse_start(it.get("StartDate"))
        code = str(it.get("Code") or "").strip()
        # FPF's Code is not stable (a new GUID shows up between requests), so
        # identify the match by its teams and kick-off; Code only builds the link.
        stable = (f"{it.get('HomeTeamCode3') or home}-{it.get('AwayTeamCode3') or away}"
                  f"-{str(it.get('StartDate') or '')[:16]}").lower()
        events.append(Event(stable,
                            title,
                            FPF_BUY_URL.format(code=code) if code else src.url,
                            start.astimezone(LISBON).strftime("%d.%m %H:%M") if start else None,
                            status, _norm_ws(f"{title} {comp} {' '.join(tags)}"),
                            extra=extra, start=start,
                            venue=_norm_ws(str(it.get("Location") or ""))))
    return events


SPORTING_BUY_URL = "https://tickets.sporting.pt/pt/evento/{token}"
SPORTING_GAME_API = ("https://tickets.sporting.pt/api/match/opengames"
                     "?gamecode={token}&queueItToken=null")


def _sporting_games(data, modality: str = "futebol") -> list[dict]:
    """Upcoming games of one modality ("futebol", "voleibol", ...) from an
    allopengames response."""
    games = []
    if isinstance(data, dict):
        d = data.get("data")
        if isinstance(d, dict) and isinstance(d.get("openGames"), list):
            games = d["openGames"]
        elif isinstance(data.get("openGames"), list):
            games = data["openGames"]
    cutoff = _now_utc().timestamp() - PAST_GRACE_HOURS * 3600
    out = []
    for g in games:
        if not isinstance(g, dict):
            continue
        # One modality only (football drops futsal/handball/...).
        mod = _norm_ws(str(g.get("modality") or "")).lower()
        if mod != modality and not (modality == "futebol" and mod == "football"):
            continue
        start = _parse_start(g.get("date"))
        if start is not None and start.timestamp() < cutoff:
            continue
        out.append(g)
    return out


# tickets.sporting.pt "modality" per sport (one source per sport).
_SPORTING_MODALITY = {"football": "futebol", "volleyball": "voleibol",
                      "basketball": "basquetebol", "futsal": "futsal",
                      "roller_hockey": "hóquei", "handball": "andebol"}


def _sporting_modality(src: "Source") -> str:
    return _SPORTING_MODALITY.get(src.sport, src.sport)


def fetch_sporting_details(data, modality: str = "futebol") -> dict:
    """token -> the game's own page data (GET opengames?gamecode=...).

    This is what the site loads when you open a match; unlike the listing it
    reflects whether the purchase flow is really open (the listing kept
    saying "Brevemente disponível" for a game that was on sale). Failures
    are skipped; the parser then falls back to the listing.
    """
    details = {}
    for g in _sporting_games(data, modality):
        token = str(g.get("token") or "").strip()
        if not token:
            continue
        try:
            body = json.loads(fetch(SPORTING_GAME_API.format(token=token),
                                    accept="application/json, text/plain, */*"))
            d = body.get("data") if isinstance(body, dict) else None
            if isinstance(d, dict) and body.get("success", True):
                details[token] = d
        except Exception as err:  # noqa: BLE001 - one game must not sink the source
            log.warning("[sporting] game %s detail failed: %s", token, err)
    return details


def _sporting_status(g: dict, detail: dict | None) -> tuple[str, str]:
    """(status, note) for one game, preferring the game page's own data."""
    if detail is not None:
        reason = _norm_ws(str(detail.get("disabledReasonDesc") or ""))
        if detail.get("soldOut") or _contains_any(reason, SOLD_OUT_WORDS):
            return "SOLD_OUT", ""
        if reason:
            return "SOON", "site: " + ("coming soon" if "brevemente" in reason.lower()
                                       else reason)
        public = bool(detail.get("allowPublicTickets"))
        member = bool(detail.get("allowMemberTickets"))
        if detail.get("allowSale") and (public or member):
            note = "virtual queue active" if detail.get("queueItRedirectUrl") else ""
            # Only sócios can buy: not something a non-member can act on.
            return ("AVAILABLE" if public else "MEMBERS"), note
        return "SOON", ""
    # Fallback: listing only. Its disabledReasonDesc proved unreliable, so a
    # listed reason makes the status "unclear" rather than "not on sale".
    reason = _norm_ws(str(g.get("disabledReasonDesc") or ""))
    if g.get("soldOut") or _contains_any(reason, SOLD_OUT_WORDS):
        return "SOLD_OUT", ""
    if reason:
        return "UNKNOWN", f"listing says: {reason}"
    if not g.get("allowSale"):
        return "SOON", ""
    return ("MEMBERS" if g.get("member") and not g.get("public") else "AVAILABLE"), ""


# tickets.sporting.pt only exposes a venueId; the site itself just says
# "Jogo Fora" for away games, so only Alvalade can be named.
_SPORTING_VENUES = {1: "Estádio José Alvalade, Lisboa",
                    12: "Pavilhão João Rocha, Lisboa"}


# Away games: tickets.sporting.pt names no stadium (venueId 6 = any away
# ground). Home grounds of Liga Portugal clubs, keyed by a word of the club's
# name as Sporting spells it (accents stripped, upper case).
_PT_CLUB_GROUNDS = {
    "BENFICA": "Estádio da Luz, Lisboa",
    "FC PORTO": "Estádio do Dragão, Porto",
    "BRAGA": "Estádio Municipal de Braga",
    "VITORIA SC": "Estádio D. Afonso Henriques, Guimarães",
    "GIL VICENTE": "Estádio Cidade de Barcelos",
    "FAMALICAO": "Estádio Municipal 22 de Junho, Famalicão",
    "RIO AVE": "Estádio do Rio Ave FC, Vila do Conde",
    "ESTORIL": "Estádio António Coimbra da Mota, Estoril",
    "AROUCA": "Estádio Municipal de Arouca",
    "SANTA CLARA": "Estádio de São Miguel, Ponta Delgada",
    "NACIONAL": "Estádio da Madeira, Funchal",
    "ESTRELA": "Estádio José Gomes, Amadora",
    "TONDELA": "Estádio João Cardoso, Tondela",
    "MARITIMO": "Estádio do Marítimo, Funchal",
    "VISEU": "Estádio do Fontelo, Viseu",
}
# Host cities as the sale rules spell them in Portuguese.
_PT_CITY_EN = {"LONDRES": "London", "MUNIQUE": "Munich", "MILAO": "Milan",
               "NAPOLES": "Naples", "TURIM": "Turin", "ROMA": "Rome",
               "VARSOVIA": "Warsaw", "CRACOVIA": "Kraków", "ATENAS": "Athens",
               "BRUXELAS": "Brussels", "COLONIA": "Cologne", "VIENA": "Vienna",
               "PRAGA": "Prague", "COPENHAGA": "Copenhagen", "ESTOCOLMO": "Stockholm",
               "ISTAMBUL": "Istanbul", "MARSELHA": "Marseille", "HAMBURGO": "Hamburg",
               "GELSENKIRCHEN": "Gelsenkirchen", "LEVERKUSEN": "Leverkusen",
               "AMESTERDAO": "Amsterdam", "SEVILHA": "Seville", "BARCELONA": "Barcelona",
               "MADRID": "Madrid", "PARIS": "Paris", "LIVERPOOL": "Liverpool",
               "MANCHESTER": "Manchester", "GLASGOW": "Glasgow", "DUBLIN": "Dublin"}
_GROUND_RE = re.compile(r"\b((?:Est[aá]dio|Stadium|Stadion|Stade|Arena|Pavilh[aã]o)"
                        r"(?:\s+(?:d[aeo]s?|of|de la|du)?\s*[A-ZÀ-Ý][\w'À-ÿ.-]+){1,4})")
_GROUND_EN_RE = re.compile(r"\b((?:[A-ZÀ-Ý][\w'À-ÿ.-]+\s+){1,3}(?:Stadium|Arena|Stadion))\b")
_ARRIVAL_RE = re.compile(r"chegada a\s+([A-ZÀ-Ý][\wÀ-ÿ-]+(?:\s+[A-ZÀ-Ý][\wÀ-ÿ-]+)?)")


def _fold(text: str) -> str:
    """Upper case without accents ("Vitória" -> "VITORIA")."""
    return "".join(c for c in unicodedata.normalize("NFKD", text)
                   if not unicodedata.combining(c)).upper()


def _sporting_venue(g: dict, sport: str = "football") -> str:
    home = _norm_ws(str((g.get("homeTeam") or {}).get("name") or ""))
    if "SPORTING" in home.upper():
        try:
            return _SPORTING_VENUES.get(int(g.get("venueId")), "")
        except (TypeError, ValueError):
            return ""
    # Away: the sale rules sometimes name the ground or the host city.
    rules = _norm_ws(BeautifulSoup(str(g.get("accessConditions") or ""),
                                   "html.parser").get_text(" "))
    for rx in (_GROUND_EN_RE, _GROUND_RE):  # "Emirates Stadium", "Estádio do X"
        m = rx.search(rules)
        if m and "Alvalade" not in m.group(1) and "João Rocha" not in m.group(1):
            return f"away · {m.group(1)}"
    m = _ARRIVAL_RE.search(rules)
    if m:
        city = m.group(1)
        return f"away · {_PT_CITY_EN.get(_fold(city), city)}"
    if sport == "football":
        folded = f" {_fold(home)} "
        for key, ground in _PT_CLUB_GROUNDS.items():
            if f" {key} " in folded:
                return f"away · {ground}"
    return "away game"


# --------------------------------------------------------------------------- #
# Sporting sale phases: the listing's accessConditions spell out who may buy #
# when ("Sócios há 10 anos ou mais / 29 de Outubro | quinta-feira | 13h00 às #
# 13h59"). Parsed into phases, then matched against each user's sócios.      #
# --------------------------------------------------------------------------- #

_PT_MONTHS_FULL = {"janeiro": 1, "fevereiro": 2, "marco": 3, "abril": 4, "maio": 5,
              "junho": 6, "julho": 7, "agosto": 8, "setembro": 9, "outubro": 10,
              "novembro": 11, "dezembro": 12}
_PHASE_LINE_RE = re.compile(
    r"^(\d{1,2})\s*(?:de\s+)?([A-Za-zçÇ]+)\s*\|[^|]*\|\s*"
    r"(?:a\s+partir\s+das\s+)?(\d{1,2})h(\d{2})"
    r"(?:\s*(?:às|as|-)\s*(\d{1,2})h(\d{2})(?:\s*(?:de|do dia)\s+(\d{1,2})\s*(?:de\s+)?([A-Za-zçÇ]+))?)?",
    re.I)


def _sale_month(word: str) -> int:
    return _PT_MONTHS_FULL.get(_fold(word).lower(), 0)


def parse_sale_phases(html: str, game_start: datetime | None = None) -> list[dict]:
    """[{label, start, end}] from a Sporting accessConditions blob (Lisbon
    times as ISO strings, end may be None). A phase is a bold label line
    followed by a "dd Mês | weekday | HHhMM às HHhMM" line."""
    if not html:
        return []
    soup = BeautifulSoup(str(html), "html.parser")
    lines = [_norm_ws(p.get_text(" ")) for p in soup.find_all(["p", "li"])]
    lines = [ln for ln in lines if ln] or [_norm_ws(x) for x in soup.get_text("\n").split("\n")]
    ref = (game_start or _now_utc()).astimezone(LISBON)
    phases, label = [], ""
    for ln in lines:
        m = _PHASE_LINE_RE.match(ln)
        if not m:
            if len(ln) < 120 and not ln.lower().startswith(("a compra", "a venda", "-", "*")):
                label = ln  # candidate label for the next date line
            continue
        day, mon = int(m.group(1)), _sale_month(m.group(2))
        if not mon or not label:
            continue
        # The sale happens before the game: pick the year that puts it there.
        year = ref.year if mon <= ref.month else ref.year - 1
        try:
            start = datetime(year, mon, day, int(m.group(3)), int(m.group(4)), tzinfo=LISBON)
        except ValueError:
            continue
        end = None
        if m.group(5):
            e_day, e_mon = day, mon
            if m.group(7) and _sale_month(m.group(8) or ""):
                e_day, e_mon = int(m.group(7)), _sale_month(m.group(8))
            try:
                end = datetime(year, e_mon, e_day, int(m.group(5)), int(m.group(6)), tzinfo=LISBON)
            except ValueError:
                end = None
            if end is not None and end <= start:
                end = None  # "14h00 às 10h59": runs on into a later day
        phases.append({"label": label, "start": start.isoformat(),
                       "end": end.isoformat() if end else None})
        label = ""
    return phases


def _phase_rules(label: str) -> list[dict]:
    """A label can list several groups ("Sócios há 75 anos ou mais e Lion
    Seats sem Gamebox"): one rule per group."""
    low = _fold(label).lower()
    rules = []
    for part in re.split(r"\s+e\s+(?=lion|socios|todos)", low):
        r = {"all": "todos os socios" in part or ("socios sem gamebox" in part)}
        m = re.search(r"ha\s+(\d+)\s+anos\s+ou\s+mais", part)
        r["min_years"] = int(m.group(1)) if m else None
        m = re.search(r"gamebox\s+(\d+)\s+a\s+(\d+)\s+anos|gamebox\s+(\d+)\s+anos", part)
        r["gb_years"] = ((int(m.group(1)), int(m.group(2))) if m and m.group(1)
                         else (int(m.group(3)), 99) if m else None)
        r["lion"] = "lion seat" in part
        no_gb = "sem gamebox" in part or "sem gb" in part
        r["gamebox"] = (None if no_gb else
                        "national" if "national" in part
                        else "modalidades" if "modalidades" in part
                        else "any" if re.search(r"\b(gb|gamebox)\b", part) else None)
        r["extra"] = "resident" in part or "residentes" in part  # e.g. residents abroad
        rules.append(r)
    return rules


def _person_years(person: dict, at: datetime) -> float:
    since = str(person.get("since") or "")
    try:
        d = datetime.fromisoformat(since) if len(since) > 4 else datetime(int(since), 7, 1)
    except ValueError:
        return 0.0
    return (at.replace(tzinfo=None) - d.replace(tzinfo=None)).days / 365.25


def person_qualifies(label: str, person: dict, at: datetime) -> bool:
    gb = str(person.get("gamebox") or "")
    years = _person_years(person, at)
    for r in _phase_rules(label):
        if r["extra"]:
            continue  # extra conditions we can't know (residence abroad...)
        gb_ok = None  # does the person meet this group's Gamebox condition?
        if r["gamebox"]:
            gb_ok = bool(gb) and (r["gamebox"] == "any" or r["gamebox"] in gb) and (
                r["gb_years"] is None or r["gb_years"][0] <= years <= r["gb_years"][1])
        if r["lion"]:
            if person.get("lion") and gb_ok is not False:
                return True
            continue  # a Lion Seats group: nobody else
        if gb_ok:
            return True
        if r["gamebox"]:
            continue
        if r["min_years"] is not None:
            if years >= r["min_years"]:
                return True
            continue
        if r["all"]:
            return True
    return False


def person_window(phases: list[dict], person: dict, now: datetime) -> dict | None:
    """The earliest phase this sócio may buy in that hasn't ended yet."""
    for ph in sorted(phases, key=lambda p: p["start"]):
        end = _parse_iso(ph.get("end"))
        if end is not None and end < now:
            continue
        if person_qualifies(ph["label"], person, _parse_iso(ph["start"]) or now):
            return ph
    return None


def parse_sporting_api(data, src: "Source", details: dict | None = None) -> list[Event]:
    """Parse tickets.sporting.pt allopengames JSON (+ per-game page data)."""
    details = details or {}
    events: list[Event] = []
    for g in _sporting_games(data, _sporting_modality(src)):
        home = _norm_ws(str((g.get("homeTeam") or {}).get("name", "")))
        away = _norm_ws(str((g.get("awayTeam") or {}).get("name", "")))
        title = " x ".join(t for t in (home, away) if t) or "Sporting CP"
        token = str(g.get("token") or "").strip()
        status, note = _sporting_status(g, details.get(token))
        notes = [_norm_ws(str(g.get("competition", "")))]
        # The listing's member/public flags lag behind the game page: once the
        # page says public tickets are on sale, don't call it members-only.
        if g.get("member") and not g.get("public") and status not in ("MEMBERS", "AVAILABLE"):
            notes.append("members (sócios) only")
        notes.append(note)
        comp = " · ".join(n for n in notes if n)
        when = _fmt_iso_datetime(str(g.get("date", "")))
        eid = str(g.get("id") or _event_id("", f"{title}-{g.get('date','')}"))
        url = SPORTING_BUY_URL.format(token=token) if token else (src.browse_url or src.url)
        venue = _sporting_venue(g, src.sport)
        context = _norm_ws(f"{title} {comp} {g.get('modality','')}")
        ev = Event(eid, title, url, when or None, status, context,
                   extra=comp, start=_parse_start(g.get("date")), venue=venue)
        ev.phases = parse_sale_phases(g.get("accessConditions"), ev.start)
        events.append(ev)
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
      allowPublicPurchase
      onlineSale
      venue { name }
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
    "FINISHED": "SOLD_OUT",  # MatchStatus enum: FINISHED, OPEN, SCHEDULED, SOLD_OUT
}


_FCPORTO_SPORT = {"football": "FOOTBALL", "volleyball": "VOLLEYBALL",
                  "basketball": "BASKETBALL", "futsal": "FUTSAL",
                  "roller_hockey": "ROLLER_HOCKEY", "handball": "HANDBALL"}


def fetch_fcporto(src: "Source") -> str:
    """POST the GraphQL query the bilhetes.fcporto.pt home page uses."""
    today = datetime.now(LISBON).strftime("%Y-%m-%d")
    body = {"query": FCPORTO_QUERY,
            "variables": {"pageSize": 12, "matchDate": {"from": today},
                          "sport": _FCPORTO_SPORT.get(src.sport, "FOOTBALL")}}
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
            if str(g.get("sport") or "").upper() not in (
                    _FCPORTO_SPORT.get(src.sport, "FOOTBALL"), ""):
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
            if status == "AVAILABLE" and g.get("onlineSale") is False:
                status = "UNKNOWN"  # open, but not sold online
            elif status == "AVAILABLE" and g.get("allowPublicPurchase") is False:
                status = "MEMBERS"
            comp = _norm_ws(" · ".join(
                x for x in (str((g.get("competition") or {}).get("name") or ""),
                            str(g.get("competitionPhase") or "")) if x))
            notes = [comp] if comp else []
            if status == "SOON" and sale_start and sale_start > now:
                notes.append(_fmt_sale_opens(sale_start))
            if status == "UNKNOWN":
                notes.append("not sold online (box office only?)" if raw == "OPEN"
                             else f"site status: {raw or '?'}")
            start = _parse_start(g.get("localStartsAt"))
            eid = str(g.get("id") or _event_id("", f"{title}-{g.get('localStartsAt')}"))
            # "/comprar" is the purchase flow behind the match page's buy button.
            events.append(Event(eid, title, f"https://bilhetes.fcporto.pt/jogos/{eid}/comprar",
                                start.astimezone(LISBON).strftime("%d.%m %H:%M") if start else None,
                                status, _norm_ws(f"{title} {comp} {raw}"),
                                extra=" · ".join(notes), start=start,
                                venue=_norm_ws(str((g.get("venue") or {}).get("name") or ""))))
    return events


_PT_MONTHS = {"jan": 1, "fev": 2, "mar": 3, "abr": 4, "mai": 5, "jun": 6,
              "jul": 7, "ago": 8, "set": 9, "out": 10, "nov": 11, "dez": 12}
_PT_DATE_RE = re.compile(
    r"(\d{1,2})\s*(?:de\s+)?([a-zç]{3})[a-zç]*\.?,?\s*(?:de\s+\d{4}\s*)?"
    r"(?:às|as|-|,)?\s*(\d{1,2})\s*[h:]\s*(\d{2})", re.IGNORECASE)


def _parse_pt_datetime(text: str, now: datetime | None = None) -> datetime | None:
    """'Dom 11 Out 18h00' / '20 de outubro às 20:00' -> aware Lisbon datetime.

    The year is not shown on these sites: pick the year that puts the match
    closest to now (stale cards from last season then read as already played).
    """
    m = _PT_DATE_RE.search(text or "")
    if not m:
        return None
    month = _PT_MONTHS.get(m.group(2).lower()[:3])
    if not month:
        return None
    now = (now or _now_utc()).astimezone(LISBON)
    candidates = []
    for year in (now.year - 1, now.year, now.year + 1):
        try:
            candidates.append(datetime(year, month, int(m.group(1)), int(m.group(3)),
                                       int(m.group(4)), tzinfo=LISBON))
        except ValueError:  # e.g. 29 Feb in a non-leap year
            continue
    if not candidates:
        return None
    return min(candidates, key=lambda d: abs((d - now).total_seconds()))


# Benfica status badge (div.button-type-container) -> (status, note)
_BENFICA_BADGES = (
    ("esgotado", "SOLD_OUT", ""),
    ("mercado secund", "RESALE", ""),
    ("por iniciar", "SOON", ""),
    ("exclusivo", "MEMBERS", None),  # None -> use the badge text as the note
)
_BENFICA_BADGE_EN = {
    "exclusivo a sócios e adeptos registados": "members & registered fans only",
    "exclusivo a sócios com quotas em dia": "paid-up members only",
    "exclusivo a sócios com red pass": "Red Pass members only",
}


# slbenfica.pt card label (".type-game") per sport.
_BENFICA_SPORT = {"football": "futebol", "volleyball": "voleibol",
                  "basketball": "basquetebol", "futsal": "futsal",
                  "roller_hockey": "hóquei", "handball": "andebol"}


def parse_benfica(html: str, src: "Source") -> list[Event]:
    """Parse slbenfica.pt/pt-pt/bilhetes (server-rendered match cards).

    Football: only the "Equipa A" tab (the page also lists women's, B team,
    U23 and Youth League games). Other sports: the "Modalidades" tab, cards
    labelled with the sport (men's team: no "Feminino").
    """
    soup = BeautifulSoup(html, "html.parser")
    events: list[Event] = []
    want = _BENFICA_SPORT.get(src.sport, src.sport)
    for card in soup.select("section.game-module"):
        kind = _norm_ws(card.select_one(".type-game").get_text(" ")) \
            if card.select_one(".type-game") else ""
        tab = card.find_parent(class_="tab-nav")
        if src.sport != "football":
            k = kind.lower()
            if (card.find_parent(class_="modalidadesTickets") is None
                    or not k.startswith(want) or "feminin" in k or "cadeira" in k):
                continue
        else:
            if tab is not None and "equipaA" not in (tab.get("class") or []):
                continue  # another team's tab
            if kind and kind.lower() != "futebol":
                continue
        link = None
        for a in card.select(".buttons-tickets a[href]"):
            href = a["href"]
            if "/loja/bilhetes/jogos/" in href and not href.endswith("#"):
                link = a
                break
        if (src.sport == "football" and tab is None
                and (link is None or not re.search(r"/jogos/compra(v2)?/", link["href"]))):
            continue  # no tab info: keep only first-team ticket links
        teams = [_norm_ws(h.get_text(" ")) for h in card.select(".team h3.hidden-xs")]
        title = " x ".join(t for t in teams if t) or "SL Benfica"
        comp = _norm_ws(card.select_one(".type-liga").get_text(" ")) \
            if card.select_one(".type-liga") else ""
        venue_el = card.select_one(".game_bar h6")
        venue = _norm_ws(venue_el.get_text(" ")) if venue_el else ""
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
                            start=start, venue=venue))
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
        return parse_source_json(loads_json(fetch_source_json(src), src), src)
    if src.api_type == "browser":
        html = render_with_browser(src.browse_url, src.wait_selector, src.wait_ms)
        if src.parser == "sporting":
            return parse_sporting_dom(html, src)
        return parse_events(html, src.browse_url, src)
    page = fetch(src.url)
    check_unavailable(page)
    return parse_html_source(page, src)


class SiteBlockedError(RuntimeError):
    """The site answered with an anti-bot / IP-ban page instead of data."""


class SiteMaintenanceError(RuntimeError):
    """The site shows a "back soon" / maintenance page instead of data."""


# Seen on tickets.sporting.pt (whole site + API): <title>Voltamos em breve!</title>
_MAINTENANCE_MARKERS = ("voltamos em breve", "voltaremos em breve", "em manutenção",
                        "em manutencao", "site em manutenção", "under maintenance",
                        "maintenance mode", "be right back", "we'll be back soon",
                        "we will be back soon", "volvemos pronto")


def check_unavailable(raw: str) -> None:
    """Raise SiteMaintenanceError / SiteBlockedError if raw is such a page."""
    if not raw or raw.lstrip()[:1] in ("{", "["):
        return  # JSON: real data
    soup = BeautifulSoup(raw, "html.parser")
    title = _norm_ws(soup.title.get_text(" ")) if soup.title else ""
    text = _norm_ws(soup.get_text(" "))[:3000]
    head = f"{title} {text[:400]}".lower()
    if any(m in head for m in _MAINTENANCE_MARKERS):
        raise SiteMaintenanceError(f"site is down for maintenance: {(title or text)[:80]}")
    if any(m in text.lower() for m in _BLOCK_MARKERS):
        raise SiteBlockedError(f"site blocked this server's IP: {text[:120]}")


_BLOCK_MARKERS = ("ip address has been banned", "access denied", "you have been blocked",
                  "attention required", "cf-browser-verification", "request blocked",
                  "request was blocked", "captcha")


def loads_json(raw: str, src: "Source"):
    """json.loads with a readable error: says what the site sent instead."""
    try:
        return json.loads(raw)
    except ValueError:
        check_unavailable(raw)
        text = _norm_ws(BeautifulSoup(raw or "", "html.parser").get_text(" "))
        raise RuntimeError(
            f"expected JSON, got {('empty response' if not (raw or '').strip() else repr(text[:120]))}"
        ) from None


# --------------------------------------------------------------------------- #
# smartfan.tickets: ticketing of the volleyball (FPV) and basketball (FPB)    #
# federations, among many clubs. Its site posts form-encoded operations to    #
# one proxy endpoint; GetActiveGames lists every game with tickets out.       #
# --------------------------------------------------------------------------- #

SMARTFAN_BUY_URL = "https://smartfan.tickets/comprar-bilhetes?ev={id}"
# Sport.Name in GetActiveGames; names not seen live yet are matched loosely.
_SMARTFAN_SPORT = {"football": ("FOOTBALL",), "volleyball": ("VOLLEYBALL",),
                   "basketball": ("BASKETBALL",), "futsal": ("FUTSAL",),
                   "roller_hockey": ("HOCKEY", "HOQUEI", "HÓQUEI"),
                   "handball": ("HANDBALL", "ANDEBOL")}


def fetch_smartfan(src: "Source") -> str:
    return fetch(src.api_url, accept="application/json, text/plain, */*",
                 form_body={"API": "SalesAPI", "Operation": "GetActiveGames"},
                 extra_headers={"Origin": "https://smartfan.tickets",
                                "Referer": "https://smartfan.tickets/home"})


def _smartfan_time(value) -> datetime | None:
    """smartfan dates are Lisbon local time, "23/10/2026 20:30"."""
    try:
        return datetime.strptime(str(value or "").strip(),
                                 "%d/%m/%Y %H:%M").replace(tzinfo=LISBON)
    except ValueError:
        return None


def parse_smartfan(data, src: "Source") -> list[Event]:
    """Games of this source's sport where one side is exactly the source's
    team (e.g. "Portugal"); women's/youth games go via exclude_keywords."""
    value = (((data or {}).get("ReplyExtraData") or {}).get("Value") or {}) \
        if isinstance(data, dict) else {}
    if isinstance(data, dict) and data.get("OpInfoStatus") not in (None, "OK"):
        raise ValueError(f"smartfan replied {data.get('OpInfoStatus')!r}")
    want_sport = _SMARTFAN_SPORT.get(src.sport, (src.sport.upper(),))
    want_team = src.team_name.strip().lower()
    now = _now_utc()
    events: list[Event] = []
    for g in value.get("Games") or []:
        if not isinstance(g, dict):
            continue
        sport = str((g.get("Sport") or {}).get("Name") or "").upper()
        if not any(w in sport for w in want_sport) or (
                src.sport == "football" and "FUTSAL" in sport):
            continue
        home = _norm_ws(str((g.get("HomeTeam") or {}).get("Name") or ""))
        away = _norm_ws(str((g.get("VisitingTeam") or {}).get("Name") or ""))
        if want_team not in (home.lower(), away.lower()):
            continue
        title = " x ".join(t for t in (home, away) if t) or src.team_name
        comp = _norm_ws(str(g.get("Competition") or ""))
        start = _smartfan_time(g.get("Date"))
        sale_start = _smartfan_time(g.get("SaleStartDate"))
        on_sale = bool(g.get("withHomeTktSales") or g.get("withAwayTktSales"))
        note = ""
        if g.get("isSoldOut"):
            status = "SOLD_OUT"
        elif sale_start and sale_start > now:
            status, note = "SOON", _fmt_sale_opens(sale_start)
        elif on_sale:
            status = "AVAILABLE"
        else:
            status = "SOON"
        gid = str(g.get("Id") or _event_id("", f"{title}-{g.get('Date', '')}"))
        extra = " · ".join(x for x in (comp, note) if x)
        events.append(Event(gid, title, SMARTFAN_BUY_URL.format(id=gid),
                            start.strftime("%d.%m %H:%M") if start else None,
                            status, _norm_ws(f"{title} {comp}"), extra=extra,
                            start=start, venue=_norm_ws(str(g.get("Location") or ""))))
    return events


# --------------------------------------------------------------------------- #
# 3cket.com: official ticketing of the Millennium Estoril Open. Each edition  #
# is an event whose alias carries the year; /api/events/<alias> answers 400   #
# until the organiser creates it. schedule.available_at = sales open.         #
# --------------------------------------------------------------------------- #

THREECKET_API = "https://3cket.com/api/events/{alias}"
THREECKET_BUY_URL = "https://3cket.com/pt/event/{alias}"
_THREECKET_ALIAS_RE = re.compile(r"3cket\.com/(?:[a-z]{2}/)?event/([A-Za-z0-9-]+)")


def _threecket_event(alias: str) -> dict | None:
    """The event's JSON, or None if 3cket has no such event (400/404)."""
    url = THREECKET_API.format(alias=alias)
    for attempt in (1, 2):
        try:
            resp = requests.get(url, timeout=REQUEST_TIMEOUT, headers={
                "User-Agent": USER_AGENT, "Accept": "application/json"})
        except requests.RequestException as err:
            if attempt == 2:
                raise RuntimeError(f"3cket {alias}: {err}") from err
            time.sleep(3)
            continue
        if resp.status_code in (400, 404):
            return None  # edition not created yet
        if resp.status_code == 200:
            data = loads_json(resp.text, None)
            return data if isinstance(data, dict) else None
        if attempt == 2:
            raise RuntimeError(f"3cket {alias}: HTTP {resp.status_code}")
        time.sleep(3)
    return None


def fetch_threecket(src: "Source") -> str:
    """JSON list of this tournament's 3cket editions (this year and next,
    plus any edition the official site links to)."""
    aliases: list[str] = []
    try:  # the official site's "buy" buttons name the current edition
        aliases += _THREECKET_ALIAS_RE.findall(fetch(src.url))
    except Exception as err:  # noqa: BLE001 - the 3cket check still works
        log.warning("[%s] official site unreadable: %s", src.id, err)
    year = datetime.now(LISBON).year
    aliases += [src.event_url.format(year=y) for y in (year, year + 1)]
    seen, events = set(), []
    for alias in aliases:
        alias = alias.lower()
        if alias in seen:
            continue
        seen.add(alias)
        ev = _threecket_event(alias)
        if ev is not None:
            events.append(ev)
    return json.dumps(events)


def parse_threecket(data, src: "Source") -> list[Event]:
    """One Event per published, not-yet-finished edition; if there is none,
    one "next edition" placeholder (status SOON) so the report shows the
    tournament is watched and its appearance reads as a change."""
    now = _now_utc()
    events: list[Event] = []
    for ev in data if isinstance(data, list) else []:
        if str(ev.get("status")) != "published" or str(ev.get("visibility")) != "public":
            continue
        sched = ev.get("schedule") or {}
        start, end = _parse_start(sched.get("start")), _parse_start(sched.get("end"))
        if end is not None and end < now:
            continue  # this edition is over
        opens = _parse_start(sched.get("available_at")) or \
            _parse_start(ev.get("next_tickets_available_at"))
        if opens is not None and opens > now:
            status, note = "SOON", _fmt_sale_opens(opens)
        else:
            status, note = "AVAILABLE", ""
        alias = str(ev.get("alias") or "")
        when = ""
        if start and end:
            s_, e_ = start.astimezone(LISBON), end.astimezone(LISBON)
            when = f"{s_:%d.%m}–{e_:%d.%m.%Y}"
        loc = ev.get("location") or {}
        venue = _norm_ws(str(loc.get("name") or loc.get("title") or "")) \
            if isinstance(loc, dict) else ""
        title = _norm_ws(str(ev.get("name") or src.team_name))
        # start = the last day: the tournament stays listed while it runs
        events.append(Event(alias or str(ev.get("id")), title,
                            THREECKET_BUY_URL.format(alias=alias) if alias else src.url,
                            when or None, status, title, extra=note,
                            start=end, venue=venue))
    if not events:
        events.append(Event("next-edition", f"{src.team_name} (next edition)", src.url,
                            None, "SOON", src.team_name,
                            extra="ticket sales not open yet"))
    return events


# --------------------------------------------------------------------------- #
# portugalf1gp.com: official ticket shop of the Formula 1 Grande Prémio de     #
# Portugal. Its API wants the site's public client token (the same for every  #
# visitor) plus Origin/Referer. product-categories names the GA & grandstands #
# event; event-detail/<slug> holds dates, prices and the sale state.          #
# --------------------------------------------------------------------------- #

F1PT_API = "https://api.portugalf1gp.com/api/v2"
F1PT_SITE = "https://portugalf1gp.com"
F1PT_TOKEN = "e9aac1f2f0b6c07d6be070ed14829de684264278359148d6a582ca65a50934d2"


def _f1pt_get(path: str) -> dict:
    raw = fetch(f"{F1PT_API}/{path}", accept="application/json",
                extra_headers={"token": F1PT_TOKEN, "Authorization": "Bearer",
                               "Origin": F1PT_SITE, "Referer": F1PT_SITE + "/",
                               "Content-Type": "application/json"})
    data = loads_json(raw, None)
    if not isinstance(data, dict) or data.get("status") != "success":
        raise RuntimeError(f"portugalf1gp API: {str(data)[:120]}")
    return data.get("data") or {}


def fetch_f1pt(src: "Source") -> str:
    cats = _f1pt_get("product-categories/moto-grand-prix?lang=en&visible_in=ptgp&page=1")
    slug = ""
    for c in cats.get("data") or []:
        url = str(c.get("url") or "")
        if c.get("slug") == "ga-grandstands" and url.startswith("events/"):
            slug = url.split("/", 1)[1]
    if not slug:  # fall back to this year's / next year's naming
        slug = src.event_url.format(year=datetime.now(LISBON).year + 1)
    event = _f1pt_get(f"event-detail/{slug}?lang=en&visible_in=ptgp")
    return json.dumps({"categories": cats.get("data") or [], "event": event})


def parse_f1pt(data, src: "Source") -> list[Event]:
    """The race weekend as one event. AVAILABLE only on an explicit open
    signal (checkout enabled / an on-sale status); the site's own status
    word is shown otherwise, so a change of it reads as a change."""
    ev = (data or {}).get("event") or {}
    if not ev:
        return []
    status_raw = str(ev.get("status") or "").lower()
    msg = _norm_ws(BeautifulSoup(str(ev.get("early_bird_message") or ""),
                                 "html.parser").get_text(" "))
    msg = re.sub(r"No pre-sale access[^.]*\.\s*", "", msg, flags=re.I).strip()
    # Everything that might be a sale switch, for the diagnostic log.
    log.info("[%s] sale fields: %s", src.id, {
        k: v for k, v in ev.items()
        if any(w in k.lower() for w in ("sale", "book", "checkout", "status", "open",
                                        "early_bird_type", "tbc"))})
    sold_out = status_raw in ("sold_out", "soldout")
    if ev.get("is_checkout_enabled") is True or status_raw in ("on_sale", "onsale", "live",
                                                              "active", "open"):
        status = "AVAILABLE"
    elif sold_out:
        status = "SOLD_OUT"
    else:
        status = "UNKNOWN"
    cats = {c.get("slug"): c for c in (data or {}).get("categories") or []}
    ga = cats.get("ga-grandstands") or {}
    price = ""
    try:
        total = float(ev.get("event_start_price") or 0) + float(ev.get("event_start_price_vat") or 0)
        price = f"from €{total:.0f}" if total else ""
    except (TypeError, ValueError):
        pass
    notes = [x for x in (price, f"site status: {status_raw}" if status == "UNKNOWN" else "",
                         msg, (str(ga.get("cta_label") or "").lower() or "")) if x]
    start = datetime.fromtimestamp(int(ev["start_date_time"]), timezone.utc) \
        if str(ev.get("start_date_time") or "").isdigit() else None
    end = datetime.fromtimestamp(int(ev["end_date_time"]), timezone.utc) \
        if str(ev.get("end_date_time") or "").isdigit() else None
    when = ""
    if start and end:
        when = f"{start.astimezone(LISBON):%d.%m}–{end.astimezone(LISBON):%d.%m.%Y}"
        if ev.get("tbc"):
            when += " (TBC)"
    slug = str(ev.get("slug") or "")
    title = _norm_ws(str(ev.get("title") or src.team_name)).title()
    return [Event(slug or "race", title, f"{F1PT_SITE}/en/events/{slug}" if slug else src.url,
                  when or None, status, title, extra=" · ".join(notes), start=end,
                  venue="Autódromo Internacional do Algarve, Portimão")]


def fetch_source_json(src: "Source") -> str:
    if src.parser == "f1pt":
        return fetch_f1pt(src)
    if src.parser == "threecket":
        return fetch_threecket(src)
    if src.parser == "fcporto":
        return fetch_fcporto(src)
    if src.parser == "smartfan":
        return fetch_smartfan(src)
    return fetch(src.api_url, accept="application/json, text/plain, */*")


def parse_source_json(data, src: "Source") -> list[Event]:
    if src.parser == "sporting_api":
        return parse_sporting_api(data, src, details=fetch_sporting_details(
            data, _sporting_modality(src)))
    if src.parser == "fcporto":
        return parse_fcporto(data, src)
    if src.parser == "fpf_odata":
        return parse_fpf_odata(data, src)
    if src.parser == "smartfan":
        return parse_smartfan(data, src)
    if src.parser == "threecket":
        return parse_threecket(data, src)
    if src.parser == "f1pt":
        return parse_f1pt(data, src)
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


# Chats that answered 403 (blocked the bot / deleted account); the next
# Telegram poll drops them from the subscribers.
_GONE_CHATS: set[str] = set()


def telegram_send(cfg: Config, text: str, preview: bool = True,
                  chats: list[str] | None = None) -> bool:
    """Send to every recipient (default: all TELEGRAM_CHAT_ID entries).

    True if at least one recipient got it, so one blocked/removed recipient
    can't make the owner's alerts repeat forever.
    """
    if chats is None:
        chats = cfg.telegram_chats + [c for c in cfg.subscribers
                                      if c not in cfg.telegram_chats]
    if not cfg.telegram_token or not chats:
        log.error("Telegram token/chat id not configured; cannot send message.")
        return False
    return any([_telegram_send_one(cfg, chat, text, preview) for chat in chats])


def _telegram_send_one(cfg: Config, chat: str, text: str, preview: bool) -> bool:
    api = f"https://api.telegram.org/bot{cfg.telegram_token}/sendMessage"
    payload = {
        "chat_id": chat,
        "text": text,
        "parse_mode": "HTML",
        "disable_web_page_preview": not preview,
    }
    for attempt in range(1, 4):
        try:
            resp = requests.post(api, data=payload, timeout=REQUEST_TIMEOUT)
            if resp.status_code == 200:
                return True
            # Recipient blocked the bot / never pressed Start: retrying won't help.
            if resp.status_code in (400, 403):
                if resp.status_code == 403:
                    _GONE_CHATS.add(str(chat))
                log.warning("Telegram: chat ...%s rejected the message (%s): %s",
                            str(chat)[-3:], resp.status_code, resp.text[:200])
                return False
            log.warning("Telegram send failed (%s): %s", resp.status_code, resp.text[:300])
        except requests.RequestException as err:
            log.warning("Telegram send error attempt %d: %s", attempt, err)
        time.sleep(2 * attempt)
    return False


def _esc(text: str) -> str:
    return (text.replace("&", "&amp;").replace("<", "&lt;").replace(">", "&gt;"))


def format_notification(event: Event, source_name: str,
                        members: bool = False) -> str:
    head = ("\U0001F535 <b>Members' sale open!</b>" if members
            else "\U0001F3AB <b>Tickets on sale!</b>")
    lines = [f"{head} — {_esc(source_name)}", "", f"<b>{_esc(event.title)}</b>"]
    if event.extra:
        lines.append(f"\U0001F3C6 {_esc(event.extra)}")
    if event.date:
        lines.append(f"\U0001F4C5 {_esc(event.date)}")
    if event.venue:
        lines.append(f"\U0001F3DF {_esc(event.venue)}")
    if event.url:
        lines.append("")
        lines.append(f'\U0001F517 <a href="{_esc(event.url)}">Buy tickets</a>')
    if members:
        lines += ["", "<i>Only club members (sócios) can buy right now. Everyone "
                      "gets a separate alert when the public sale opens.</i>"]
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
                events = parse_source_json(loads_json(raw, src), src)
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
            print(f"[{ev.status:9}] {ev.title[:70]!r} | {ev.date} | {ev.extra} | "
                  f"{ev.venue or '-'} | {ev.url}{star}")
            for ph in ev.phases:
                print(f"      phase {ph['start'][5:16]} -> {(ph['end'] or '')[5:16] or '…':11} "
                      f"| {ph['label']}")
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


def _probe_css(url: str, selector: str) -> None:
    """Print each element matching a CSS selector: its ancestors' classes
    (to see which tab/section it sits in) and its text."""
    try:
        soup = BeautifulSoup(fetch(url), "html.parser")
    except Exception as err:  # noqa: BLE001
        print(f"\n=== CSS in {url}: fetch failed: {err} ===")
        return
    found = soup.select(selector)
    print(f"\n=== CSS {selector!r} in {url}: {len(found)} match(es) ===")
    for el in found[:60]:
        chain = []
        for a in el.parents:
            if a.name in (None, "[document]", "html", "body"):
                continue
            cls = ".".join(a.get("class") or [])
            chain.append(f"{a.name}{'#' + a['id'] if a.get('id') else ''}"
                         f"{'.' + cls if cls else ''}")
        print("  @", " < ".join(chain[:6]))
        print("   ", _norm_ws(el.get_text(" "))[:300],
              f"[href={el.get('href')}]" if el.get("href") else "",
              f"[class={'.'.join(el.get('class') or [])}]")


_CHUNK_RE = re.compile(r'["\'(](?:\./|/)?((?:chunk|[a-z0-9\-]+)-[A-Z0-9]{8}\.js)["\')]')


# How much text after each hit _probe_grep shows ("term@2000" widens it).
_PROBE_AFTER = 150


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
                snippet = body[max(0, i - 150):i + _PROBE_AFTER].replace("\n", " ")
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
    post = os.environ.get("PROBE_POST", "").strip()
    if direct and post:  # POST a body (JSON, or "form:a=1&b=2") and dump the reply
        print(f"\n=== POST {direct} ===")
        origin = {"Origin": f"https://{urlparse(direct).netloc}"}
        try:
            if post.startswith("form:"):
                body = fetch(direct, accept="application/json", extra_headers=origin,
                             form_body=dict(parse_qsl(post[5:])))
            else:
                body = fetch(direct, accept="application/json",
                             json_body=json.loads(post), extra_headers=origin)
        except Exception as err:  # noqa: BLE001
            body = f"request error: {err}"
        body = _norm_ws(body)
        if not grep:
            print(body[:4000])
            return 0
        print(f"({len(body)} chars)")
        for term in filter(None, (t.strip() for t in grep.split(","))):
            hits = [m.start() for m in re.finditer(re.escape(term), body, re.IGNORECASE)]
            print(f"  [{term}] {len(hits)} hit(s)")
            for i in hits[:10]:
                print("     …", body[max(0, i - 300):i + 500], "…")
        return 0
    if direct:
        for u in direct.split(","):
            u = u.strip()
            if not u:
                continue
            if grep.startswith("css:"):
                _probe_css(u, grep[4:])
            elif grep:
                global _PROBE_AFTER
                grep, _, width = grep.partition("@")
                _PROBE_AFTER = int(width) if width.isdigit() else 150
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
    # The repo (and so this log) is public: never print full ids or names
    # here. If an owner chat is configured, send the full list there instead.
    print(f"Chats found: {len(seen)}")
    for cid, name in seen.items():
        known = " (already a recipient)" if cid in cfg.telegram_chats else ""
        print(f"  chat_id = ...{cid[-3:]}{known}")
    if cfg.telegram_chat:
        lines = ["👥 <b>Who has written to the bot</b>", ""]
        for cid, name in seen.items():
            mark = " ✅ already gets messages" if cid in cfg.telegram_chats else ""
            lines.append(f"• {_esc(name)} — <code>{cid}</code>{mark}")
        lines += ["", "To add someone: GitHub → repo Settings → Secrets and variables → "
                      "Actions → <b>TELEGRAM_CHAT_ID</b> → Update, and list the ids "
                      "separated by commas, yours first (e.g. <code>"
                      f"{_esc(cfg.telegram_chat)},123456789</code>)."]
        ok = telegram_send(cfg, "\n".join(lines), preview=False,
                           chats=[cfg.telegram_chat])  # owner only
        print("Full list sent to the owner's Telegram." if ok
              else "Could not send the list to Telegram.")
    else:
        print("Set TELEGRAM_CHAT_ID (your own id) to receive the full list in Telegram.")
    return 0


# --------------------------------------------------------------------------- #
# Access: /start subscribes (open mode) or asks the owner (approval mode)    #
# --------------------------------------------------------------------------- #


def _tg(cfg: Config, method: str, http_timeout: float = REQUEST_TIMEOUT, **params):
    """Call a Telegram Bot API method; return its "result" or None."""
    try:
        resp = requests.post(f"https://api.telegram.org/bot{cfg.telegram_token}/{method}",
                             json=params, timeout=http_timeout)
        data = resp.json()
    except (requests.RequestException, ValueError) as err:
        log.warning("Telegram %s failed: %s", method, err)
        return None
    if not data.get("ok"):
        log.warning("Telegram %s error: %s", method, str(data)[:200])
        return None
    return data.get("result")


def _chat_name(chat: dict) -> str:
    name = " ".join(filter(None, [chat.get("first_name"), chat.get("last_name")]))
    if chat.get("username"):
        name = f"{name} (@{chat['username']})" if name else f"@{chat['username']}"
    return name or str(chat.get("id"))


def _ask_owner(cfg: Config, cid: str, name: str) -> None:
    _tg(cfg, "sendMessage", chat_id=cfg.telegram_chat, parse_mode="HTML",
        text=f"🙋 <b>{_esc(name)}</b> wants to receive the ticket bot's messages.",
        reply_markup={"inline_keyboard": [[
            {"text": "✅ Allow", "callback_data": f"allow:{cid}"},
            {"text": "❌ Deny", "callback_data": f"deny:{cid}"}]]})


def _tell_owner_joined(cfg: Config, cid: str, name: str) -> None:
    _tg(cfg, "sendMessage", chat_id=cfg.telegram_chat, parse_mode="HTML",
        text=f"🆕 <b>{_esc(name)}</b> subscribed to the ticket bot.",
        reply_markup={"inline_keyboard": [[
            {"text": "🚫 Remove & block", "callback_data": f"remove:{cid}"}]]})


def _subscribe(cfg: Config, state: dict, cid: str, name: str) -> None:
    state["pending"].pop(cid, None)
    state["subscribers"][cid] = {"name": name, "since": _now_utc().isoformat()}
    _tg(cfg, "sendMessage", chat_id=cid,
        text="✅ You're subscribed! You'll get a message as soon as tickets go on "
             "sale or a match's status changes. Send /status any time for the "
             "overview, /settings to change your teams, /stop to unsubscribe.")
    _start_onboarding(cfg, state, cid, fresh=True)


# --------------------------------------------------------------------------- #
# Per-user preferences: which teams to follow, where the user is a sócio      #
# --------------------------------------------------------------------------- #


def _all_chats(cfg: Config) -> list[str]:
    return cfg.telegram_chats + [c for c in cfg.subscribers if c not in cfg.telegram_chats]


SPORTS = {"football": "⚽ Football", "futsal": "🥅 Futsal",
          "volleyball": "🏐 Volleyball", "basketball": "🏀 Basketball",
          "handball": "🤾 Handball", "roller_hockey": "🏑 Roller hockey",
          "tennis": "🎾 Tennis", "motorsport": "🏎 Formula 1"}


def _teams_of(cfg: Config) -> dict[str, "Source"]:
    """team id -> its first source (for the team's emoji / name / club flag)."""
    out: dict[str, "Source"] = {}
    for src in cfg.sources:
        out.setdefault(src.team, src)
    return out


def _team_label(src: "Source") -> str:
    return f"{src.emoji} {src.team_name}".strip()


def _sports_of(cfg: Config) -> list[str]:
    return [sp for sp in SPORTS if any(src.sport == sp for src in cfg.sources)]


def _prefs(cfg: Config, state: dict, cid: str) -> dict:
    """The user's choices -> also the list of sources they receive.

    Defaults (nothing chosen yet): football, every team; membership only for
    the owner, on teams whose sources are marked member_alerts. Choices made
    before sports existed ({teams, member} with source ids = team ids) mean
    football.
    """
    p = (state.get("prefs") or {}).get(cid) or {}
    teams_all = list(_teams_of(cfg))
    sports = [sp for sp in _sports_of(cfg) if sp in p.get("sports", ["football"])]
    teams = [t for t in teams_all if t in p["teams"]] if "teams" in p else teams_all
    if "member" in p:
        member = p["member"]
    elif cid == cfg.telegram_chat:
        member = [src.team for src in cfg.sources if src.member_alerts]
    else:
        member = []
    return {"sports": sports, "teams": teams,
            "member": [t for t in teams_all if t in member and t in teams],
            "sources": [src.id for src in cfg.sources
                        if src.sport in sports and src.team in teams]}


def _recipients(cfg: Config, state: dict, sid: str, members: bool = False) -> list[str]:
    """Who gets alerts for source `sid` (members=True: its members' sales)."""
    team = next((src.team for src in cfg.sources if src.id == sid), sid)
    out = []
    for c in _all_chats(cfg):
        p = _prefs(cfg, state, c)
        if sid in p["sources"] and (not members or team in p["member"]):
            out.append(c)
    return out


def _toggle_rows(items: list[tuple[str, str]], sel: list[str], prefix: str) -> list:
    return [[{"text": f"{'✅' if key in sel else '⬜️'} {label}",
              "callback_data": f"{prefix}:{key}"}] for key, label in items]


def _sports_keyboard(cfg: Config, sel: list[str]) -> dict:
    rows = _toggle_rows([(sp, SPORTS[sp]) for sp in _sports_of(cfg)], sel, "s")
    rows.append([{"text": "Next ➡️", "callback_data": "snext"}])
    return {"inline_keyboard": rows}


def _available_teams(cfg: Config, sports: list[str]) -> list["Source"]:
    """Teams that have a source in one of `sports` (e.g. no national team
    for volleyball)."""
    return [src for team, src in _teams_of(cfg).items()
            if any(s.team == team and s.sport in sports for s in cfg.sources)]


def _teams_keyboard(cfg: Config, sports: list[str], sel: list[str]) -> dict:
    rows = _toggle_rows([(src.team, _team_label(src))
                         for src in _available_teams(cfg, sports)], sel, "t")
    rows.append([{"text": "Next ➡️", "callback_data": "tnext"}])
    return {"inline_keyboard": rows}


def _members_keyboard(cfg: Config, teams: list[str], sel: list[str]) -> dict:
    rows = _toggle_rows([(t, _team_label(src)) for t, src in _teams_of(cfg).items()
                         if src.club and t in teams], sel, "m")
    rows.append([{"text": "Done ✔️", "callback_data": "mdone"}])
    return {"inline_keyboard": rows}


_SPORTS_Q = ("⚙️ <b>Which sports do you want ticket alerts for?</b>\n"
             "Tap to select, then press Next.")
_TEAMS_Q = ("👥 <b>Which teams / tournaments?</b>\n"
            "Tap to select, then press Next.")
_MEMBERS_Q = ("🎟 <b>Are you a club member (sócio)?</b>\n"
              "Clubs often sell to members first. Tick the clubs where you're a "
              "member to be alerted about those sales too - or just press Done.")


def _start_onboarding(cfg: Config, state: dict, cid: str, fresh: bool = False) -> None:
    if fresh:
        cur = {"sports": [], "teams": [], "member": []}
    else:
        p = _prefs(cfg, state, cid)
        cur = {"sports": p["sports"], "teams": p["teams"], "member": p["member"]}
    state["prefs_draft"][cid] = cur
    _tg(cfg, "sendMessage", chat_id=cid, parse_mode="HTML", text=_SPORTS_Q,
        reply_markup=_sports_keyboard(cfg, cur["sports"]))


def _finish_onboarding(cfg: Config, state: dict, cid: str, draft: dict,
                       message_id) -> None:
    state["prefs"][cid] = {**(state["prefs"].get(cid) or {}),
                           **{k: draft[k] for k in ("sports", "teams", "member")}}
    state["prefs_draft"].pop(cid, None)
    teams = _teams_of(cfg)
    names = lambda ids: ", ".join(_team_label(teams[t]) for t in teams  # noqa: E731
                                  if t in ids) or "none"
    sports = ", ".join(SPORTS[sp] for sp in SPORTS if sp in draft["sports"])
    text = (f"✅ <b>All set!</b>\nSports: {_esc(sports)}\n"
            f"Teams: {_esc(names(draft['teams']))}\n"
            f"Members' sale alerts: {_esc(names(draft['member']))}\n\n"
            "Change this any time with /settings.")
    if message_id:
        _tg(cfg, "editMessageText", chat_id=cid, message_id=message_id,
            parse_mode="HTML", text=text)
    else:
        _tg(cfg, "sendMessage", chat_id=cid, parse_mode="HTML", text=text)
    _send_status(cfg, state, cid)
    if "sporting" in draft["member"] and not _members_of(state, cid):
        _ask_members(cfg, state, cid)


def _handle_prefs_callback(cfg: Config, state: dict, cb: dict) -> None:
    """Taps on the onboarding / /settings keyboards (any recipient):
    sports -> teams -> memberships."""
    msg = cb.get("message") or {}
    cid = str((msg.get("chat") or {}).get("id") or (cb.get("from") or {}).get("id"))
    data = str(cb.get("data") or "")
    answer = lambda t="": _tg(cfg, "answerCallbackQuery",  # noqa: E731
                              callback_query_id=cb.get("id"), text=t)
    if cid not in cfg.telegram_chats and cid not in state["subscribers"]:
        answer("Send /start to subscribe first.")
        return
    draft = state["prefs_draft"].get(cid)
    if draft is None:  # e.g. an old keyboard: continue from the saved choices
        p = _prefs(cfg, state, cid)
        draft = {"sports": p["sports"], "teams": p["teams"], "member": p["member"]}
    draft.setdefault("sports", ["football"])  # draft from before sports existed
    state["prefs_draft"][cid] = draft
    mid = msg.get("message_id")
    edit = lambda text, markup: _tg(  # noqa: E731
        cfg, "editMessageText", chat_id=cid, message_id=mid, parse_mode="HTML",
        text=text, reply_markup=markup)
    action, _, key = data.partition(":")
    valid = {"s": set(_sports_of(cfg)), "t": set(_teams_of(cfg)),
             "m": {t for t, src in _teams_of(cfg).items() if src.club}}
    if action in valid and key in valid[action]:
        field = {"s": "sports", "t": "teams", "m": "member"}[action]
        sel = draft[field]
        if key in sel:
            sel.remove(key)
        else:
            sel.append(key)
        if action == "s":
            markup = _sports_keyboard(cfg, sel)
        elif action == "t":
            draft["member"] = [t for t in draft["member"] if t in sel]
            markup = _teams_keyboard(cfg, draft["sports"], sel)
        else:
            markup = _members_keyboard(cfg, draft["teams"], sel)
        answer()
        _tg(cfg, "editMessageReplyMarkup", chat_id=cid, message_id=mid,
            reply_markup=markup)
    elif data in ("tnext", "mdone") and not draft["sports"]:
        answer("Pick a sport first.")  # an old keyboard skipped that step
        edit(_SPORTS_Q, _sports_keyboard(cfg, draft["sports"]))
    elif data == "snext":
        if not draft["sports"]:
            answer("Pick at least one sport.")
            return
        answer()
        avail = [src.team for src in _available_teams(cfg, draft["sports"])]
        draft["teams"] = [t for t in draft["teams"] if t in avail]
        edit(_TEAMS_Q, _teams_keyboard(cfg, draft["sports"], draft["teams"]))
    elif data == "tnext":
        avail = [src.team for src in _available_teams(cfg, draft["sports"])]
        draft["teams"] = [t for t in draft["teams"] if t in avail]
        if not draft["teams"]:
            answer("Pick at least one team.")
            return
        answer()
        draft["member"] = [t for t in draft["member"] if t in draft["teams"]]
        teams = _teams_of(cfg)
        if not any(teams[t].club for t in draft["teams"]):
            draft["member"] = []
            _finish_onboarding(cfg, state, cid, draft, mid)
            return
        edit(_MEMBERS_Q, _members_keyboard(cfg, draft["teams"], draft["member"]))
    elif data == "mdone":
        answer()
        _finish_onboarding(cfg, state, cid, draft, mid)
    else:
        answer()


def _list_for_owner(cfg: Config, state: dict) -> None:
    subs, blocked = state["subscribers"], state["blocked"]
    if not subs and not blocked:
        _tg(cfg, "sendMessage", chat_id=cfg.telegram_chat,
            text="Nobody else receives the bot's messages yet.")
        return
    rows = [[{"text": f"❌ Remove {v.get('name', k)}"[:60], "callback_data": f"remove:{k}"}]
            for k, v in subs.items()]
    rows += [[{"text": f"↩️ Unblock {v.get('name', k)}"[:60],
               "callback_data": f"unblock:{k}"}] for k, v in blocked.items()]
    lines = [f"👥 <b>Receiving the bot's messages ({len(subs)}):</b>"]
    lines += [f"• {_esc(v.get('name', k))}" for k, v in subs.items()] or ["• nobody"]
    if blocked:
        lines += ["", f"🚫 <b>Blocked ({len(blocked)}):</b>"]
        lines += [f"• {_esc(v.get('name', k))}" for k, v in blocked.items()]
    _tg(cfg, "sendMessage", chat_id=cfg.telegram_chat, parse_mode="HTML",
        text="\n".join(lines), reply_markup={"inline_keyboard": rows})


def _handle_message(cfg: Config, state: dict, msg: dict) -> None:
    chat = msg.get("chat") or {}
    if chat.get("type") != "private":
        return  # requests only from private chats
    cid, name = str(chat.get("id")), _chat_name(chat)
    raw_text = (msg.get("text") or "").strip()
    text = raw_text.lower()
    say = lambda t: _tg(cfg, "sendMessage", chat_id=cid, text=t)  # noqa: E731
    known = cid in cfg.telegram_chats or cid in state["subscribers"]
    if known and text == "/members":
        _ask_members(cfg, state, cid)
        return
    if known and raw_text and not raw_text.startswith("/") and \
            state.setdefault("awaiting", {}).get(cid) == "members":
        _handle_members_reply(cfg, state, cid, raw_text)
        return
    if text == "/status" and (cid in cfg.telegram_chats or cid in state["subscribers"]):
        _send_status(cfg, state, cid)
        return
    if text == "/settings" and (cid in cfg.telegram_chats or cid in state["subscribers"]):
        _start_onboarding(cfg, state, cid)
        return
    if cid in cfg.telegram_chats:  # the owner (or a fixed recipient)
        if cid == cfg.telegram_chat and text in ("/list", "/subscribers"):
            _list_for_owner(cfg, state)
        return
    if cid in state["blocked"]:
        say("Sorry, this bot isn't available for you.")
        return
    if text == "/stop":
        state["prefs"].pop(cid, None)
        state["prefs_draft"].pop(cid, None)
        if state["subscribers"].pop(cid, None) is not None:
            say("You're unsubscribed. Send /start to subscribe again.")
            _tg(cfg, "sendMessage", chat_id=cfg.telegram_chat,
                text=f"ℹ️ {name} unsubscribed.")
        state["pending"].pop(cid, None)
        return
    if cid in state["subscribers"]:
        say("✅ You already receive the ticket updates. Send /status for the "
            "current overview, /settings to change your teams, /stop to "
            "unsubscribe.")
    elif cfg.open_access:
        if text.split(maxsplit=1)[:1] != ["/start"]:
            say("👋 Hi! This bot sends Portuguese football ticket alerts. "
                "Send /start to subscribe.")
            return
        _subscribe(cfg, state, cid, name)
        _tell_owner_joined(cfg, cid, name)
    elif cid in state["pending"]:
        say("⏳ Your request is waiting for the owner's approval.")
    else:
        state["pending"][cid] = {"name": name, "requested": _now_utc().isoformat()}
        say("👋 Hi! This bot sends Portuguese football ticket alerts (Portugal, "
            "Sporting, Benfica, Porto). Your request was sent to the owner - "
            "you'll get a message here once it's approved.")
        _ask_owner(cfg, cid, name)


def _report_messages(cfg: Config, state: dict, teams: list[str]) -> list[str]:
    """The latest check's overview, limited to `teams`."""
    rep_ = state.get("last_report") or {}
    blocks = rep_.get("blocks") or {}
    if not blocks:
        return []
    sts = [st for sid in teams for st in (rep_.get("statuses") or {}).get(sid, [])]
    header = f"🔎 <b>Ticket check</b> · {rep_.get('time', '')}\n{_totals_line(sts)}"
    return _pack_messages(header, [blocks[sid] for sid in teams if sid in blocks])


def _send_status(cfg: Config, state: dict, cid: str) -> None:
    """Reply with the summary of the latest check (the user's teams only)."""
    summary = _report_messages(cfg, state, _prefs(cfg, state, cid)["sources"])
    if not summary:
        telegram_send(cfg, "No check has finished yet - try again in a few minutes.",
                      chats=[cid])
        return
    for msg in summary:
        telegram_send(cfg, msg, preview=False, chats=[cid])
    if _members_of(state, cid):
        plan = _windows_text(cfg, state, cid, _now_utc())
        if plan:
            telegram_send(cfg, plan, preview=False, chats=[cid])


# --------------------------------------------------------------------------- #
# Personal Sporting sale windows: each user lists their sócios (/members);   #
# for every game with a phased sale the bot works out when each of them may  #
# buy and reminds them 30 min before and when their window opens.            #
# --------------------------------------------------------------------------- #

REMIND_BEFORE_MIN = 30
_MEMBERS_HELP = (
    "🦁 <b>Your Sporting sócios</b>\n"
    "Sporting sells in phases by seniority (\"Sócios há 10 anos ou mais\"...), "
    "Gamebox and Lion Seats. Tell me who buys and I'll tell each of you when "
    "your window opens.\n\n"
    "Reply with one line per sócio: <b>name</b>, the <b>year</b> (or date) they "
    "became a sócio, and if it applies <i>gamebox national</i>, "
    "<i>gamebox modalidades</i> or <i>lion seat</i>. Example:\n"
    "<code>Me 2024\nSon 2026-08\nDad 1995 gamebox national</code>\n\n"
    "Send <code>none</code> to clear the list.")
_MEMBER_LINE_RE = re.compile(
    r"^(?P<name>.+?)[\s,:;-]+(?P<since>\d{4}(?:-\d{1,2}(?:-\d{1,2})?)?|\d{1,2}[./]\d{1,2}[./]\d{4}"
    r"|\d{1,2}[./]\d{4})\b(?P<rest>.*)$")


def _members_of(state: dict, cid: str) -> list[dict]:
    return list(((state.get("prefs") or {}).get(cid) or {}).get("sporting_members") or [])


def _ask_members(cfg: Config, state: dict, cid: str) -> None:
    state.setdefault("awaiting", {})[cid] = "members"
    have = _members_of(state, cid)
    now_list = ("\n\nNow: " + "; ".join(_member_str(p) for p in have)) if have else ""
    _tg(cfg, "sendMessage", chat_id=cid, parse_mode="HTML", text=_MEMBERS_HELP + now_list)


def _member_str(p: dict) -> str:
    extra = [x for x in (f"gamebox {p['gamebox']}" if p.get("gamebox") else "",
                         "lion seat" if p.get("lion") else "") if x]
    return f"{p['name']} (since {p['since']}{', ' + ', '.join(extra) if extra else ''})"


def parse_members(text: str) -> list[dict] | None:
    """Lines "Name 2024 [gamebox national|modalidades] [lion seat]" -> list;
    None if a line can't be read."""
    out = []
    for raw in text.splitlines():
        line = _norm_ws(raw)
        if not line:
            continue
        m = _MEMBER_LINE_RE.match(line)
        if not m:
            return None
        since = m.group("since")
        d = re.match(r"^(\d{1,2})[./](\d{1,2})[./](\d{4})$", since)
        if d:
            since = f"{d.group(3)}-{int(d.group(2)):02d}-{int(d.group(1)):02d}"
        d = re.match(r"^(\d{1,2})[./](\d{4})$", since)
        if d:
            since = f"{d.group(2)}-{int(d.group(1)):02d}"
        if re.match(r"^\d{4}-\d{1,2}$", since):
            y, mo = since.split("-")
            since = f"{y}-{int(mo):02d}-01"
        year = int(since[:4])
        if not 1900 <= year <= datetime.now(LISBON).year:
            return None
        rest = _fold(m.group("rest")).lower()
        gb = ("national" if "national" in rest and ("gamebox" in rest or "gb" in rest)
              else "modalidades" if "modalidades" in rest else
              "any" if re.search(r"\b(gamebox|gb)\b", rest) else "")
        out.append({"name": m.group("name").strip()[:30], "since": since,
                    "gamebox": gb, "lion": "lion" in rest})
    return out


def _handle_members_reply(cfg: Config, state: dict, cid: str, raw: str) -> None:
    say = lambda t: _tg(cfg, "sendMessage", chat_id=cid, parse_mode="HTML", text=t)  # noqa: E731
    prefs = state.setdefault("prefs", {}).setdefault(cid, {})
    if _norm_ws(raw).lower() in ("none", "no", "нет", "clear"):
        prefs.pop("sporting_members", None)
        state["awaiting"].pop(cid, None)
        say("OK, no Sporting sócios saved. /members to set them again.")
        return
    people = parse_members(raw)
    if not people:
        say("I couldn't read that. One line per sócio, e.g. <code>Me 2024</code> "
            "or <code>Son 2026-08</code>. Try again or send <code>none</code>.")
        return
    prefs["sporting_members"] = people
    state["awaiting"].pop(cid, None)
    lines = ["✅ Saved: " + "; ".join(_member_str(p) for p in people)]
    plan = _windows_text(cfg, state, cid, _now_utc())
    lines.append(plan or "No Sporting game with a phased sale right now - I'll tell "
                         "you each person's window as soon as one is announced.")
    say("\n\n".join(lines))


def _fmt_when(iso: str) -> str:
    d = _parse_iso(iso)
    return f"{d.astimezone(LISBON):%a %d %b, %H:%M}" if d else "?"


def _user_games(cfg: Config, state: dict, cid: str) -> list[tuple[str, dict]]:
    srcs = set(_prefs(cfg, state, cid)["sources"])
    games = state.get("sale_phases") or {}
    return [(k, g) for k, g in games.items() if g.get("source") in srcs and g.get("phases")]


def _windows_text(cfg: Config, state: dict, cid: str, now: datetime) -> str:
    """Per game: when each of the user's sócios may buy (future windows only)."""
    people = _members_of(state, cid)
    blocks = []
    for _key, g in sorted(_user_games(cfg, state, cid), key=lambda kv: kv[1].get("start") or ""):
        rows = []
        for p in people:
            w = person_window(g["phases"], p, now)
            if w is None:
                rows.append(f"• {_esc(p['name'])}: no phase matches - check the rules")
            else:
                started = (_parse_iso(w["start"]) or now) <= now
                rows.append(f"• {_esc(p['name'])}: {'open now' if started else _fmt_when(w['start'])}"
                            f" <i>({_esc(w['label'])})</i>")
        if rows:
            link = f'<a href="{_esc(g["url"])}">{_esc(g["title"])}</a>'
            blocks.append(f"{link} · {_esc(g.get('date') or '')}\n" + "\n".join(rows))
    if not blocks:
        return ""
    return "🗓 <b>Your Sporting sale windows</b>\n\n" + "\n\n".join(blocks)


def sale_window_reminders(cfg: Config, state: dict, now: datetime) -> bool:
    """Plan / 30-min / opening messages per user and game. Cheap (no
    fetching), so it runs every loop tick. True if anything was sent."""
    sent_any = False
    sent = state.setdefault("phase_sent", {})
    snapshot = state.get("snapshot") or {}
    for cid in _all_chats(cfg):
        people = _members_of(state, cid)
        if not people or "sporting" not in _prefs(cfg, state, cid)["member"]:
            continue
        for key, g in _user_games(cfg, state, cid):
            src_id, _, gid = key.partition(":")
            if (snapshot.get(src_id) or {}).get(gid) == "SOLD_OUT":
                continue
            by_start: dict[str, list[str]] = {}
            labels: dict[str, str] = {}
            for p in people:
                w = person_window(g["phases"], p, now)
                if w:
                    by_start.setdefault(w["start"], []).append(p["name"])
                    labels[w["start"]] = w["label"]
            if not by_start:
                continue
            link = f'<a href="{_esc(g["url"])}">{_esc(g["title"])}</a> · {_esc(g.get("date") or "")}'
            plan_key = f"plan:{cid}:{key}"
            if plan_key not in sent and any((_parse_iso(st) or now) > now for st in by_start):
                rows = [f"• {_esc(', '.join(names))}: {_fmt_when(st)} <i>({_esc(labels[st])})</i>"
                        for st, names in sorted(by_start.items())]
                if telegram_send(cfg, "🗓 <b>Sporting sale windows</b> — " + link + "\n"
                                 + "\n".join(rows) + f"\n\nI'll remind you {REMIND_BEFORE_MIN} "
                                 "min before and when each window opens.",
                                 preview=False, chats=[cid]):
                    sent[plan_key] = now.isoformat()
                    sent_any = True
            for st, names in by_start.items():
                start = _parse_iso(st)
                if start is None:
                    continue
                who = _esc(" & ".join(names))
                mins = (start - now).total_seconds() / 60
                k_soon, k_open = f"soon:{cid}:{key}:{st}", f"open:{cid}:{key}:{st}"
                if 0 < mins <= REMIND_BEFORE_MIN and k_soon not in sent:
                    if telegram_send(cfg, f"⏰ <b>In {int(round(mins))} min</b> {who} can buy — "
                                     f"{link}\n<i>{_esc(labels[st])}</i>, from "
                                     f"{start.astimezone(LISBON):%H:%M}. Log in to "
                                     "tickets.sporting.pt now.", preview=False, chats=[cid]):
                        sent[k_soon] = now.isoformat()
                        sent_any = True
                if -90 <= mins <= 0 and k_open not in sent:
                    if telegram_send(cfg, f"🟢 <b>Your window is open</b>: {who} can buy now — "
                                     f"{link}\n<i>{_esc(labels[st])}</i>\n\n"
                                     f'🔗 <a href="{_esc(g["url"])}">Buy tickets</a>',
                                     preview=False, chats=[cid]):
                        sent[k_open] = now.isoformat()
                        sent[k_soon] = sent.get(k_soon) or now.isoformat()
                        sent_any = True
    return sent_any


def _handle_callback(cfg: Config, state: dict, cb: dict) -> None:
    data = str(cb.get("data") or "")
    if data in ("snext", "tnext", "mdone") or data[:2] in ("s:", "t:", "m:"):
        _handle_prefs_callback(cfg, state, cb)
        return
    owner_ok = str((cb.get("from") or {}).get("id")) == cfg.telegram_chat
    action, _, cid = str(cb.get("data") or "").partition(":")
    msg = cb.get("message") or {}
    if not owner_ok or action not in ("allow", "deny", "remove", "unblock") or not cid:
        _tg(cfg, "answerCallbackQuery", callback_query_id=cb.get("id"),
            text="Only the bot's owner can do that.")
        return
    info = (state["pending"].pop(cid, None) or state["subscribers"].get(cid)
            or state["blocked"].get(cid) or {})
    name = info.get("name", cid)
    if action in ("deny", "remove"):
        state["prefs"].pop(cid, None)
        state["prefs_draft"].pop(cid, None)
    if action == "unblock":
        state["blocked"].pop(cid, None)
        result = f"↩️ Unblocked: {name} (they can /start again)"
    elif action == "allow":
        state["blocked"].pop(cid, None)
        state["subscribers"][cid] = {"name": name, "since": _now_utc().isoformat()}
        _tg(cfg, "sendMessage", chat_id=cid,
            text="✅ Access granted! You'll get a message as soon as tickets go on "
                 "sale or a match's status changes. Send /status any time for the "
                 "full overview, /stop to unsubscribe.")
        result = f"✅ Allowed: {name}"
    elif action == "deny":
        state["subscribers"].pop(cid, None)
        _tg(cfg, "sendMessage", chat_id=cid,
            text="Sorry, the owner didn't approve the request.")
        result = f"❌ Denied: {name}"
    else:  # remove
        state["subscribers"].pop(cid, None)
        _tg(cfg, "sendMessage", chat_id=cid,
            text="The owner removed you from the ticket bot's recipients.")
        if cfg.open_access:  # otherwise they could just /start again
            state["blocked"][cid] = {"name": name, "since": _now_utc().isoformat()}
            result = f"🚫 Removed & blocked: {name}"
        else:
            result = f"🗑 Removed: {name}"
    _tg(cfg, "answerCallbackQuery", callback_query_id=cb.get("id"), text=result)
    if msg.get("message_id") and action not in ("remove", "unblock"):
        _tg(cfg, "editMessageText", chat_id=cfg.telegram_chat,
            message_id=msg["message_id"], text=result)
    else:
        _tg(cfg, "sendMessage", chat_id=cfg.telegram_chat, text=result)


def poll_access_requests(cfg: Config, wait: int = 0) -> None:
    """Read new Telegram updates. With `wait` > 0 Telegram holds the request
    up to that many seconds until something arrives (long polling), so the
    loop answers taps and commands within a second or two."""
    if not cfg.telegram_token or not cfg.telegram_chat:
        return
    state = load_state(cfg.state_file)
    changed = False
    gone = [c for c in _GONE_CHATS if c in state["subscribers"]]
    for cid in gone:  # they blocked the bot: stop sending to them
        info = state["subscribers"].pop(cid)
        _tg(cfg, "sendMessage", chat_id=cfg.telegram_chat,
            text=f"ℹ️ {info.get('name', cid)} blocked the bot - unsubscribed.")
        changed = True
    _GONE_CHATS.clear()
    if cfg.open_access and state["pending"]:
        # Requests left over from approval mode: let them in now.
        for cid, info in list(state["pending"].items()):
            _subscribe(cfg, state, cid, info.get("name", cid))
            _tell_owner_joined(cfg, cid, info.get("name", cid))
        changed = True
    updates = _tg(cfg, "getUpdates", http_timeout=wait + REQUEST_TIMEOUT,
                  offset=int(state.get("tg_offset") or 0), timeout=wait,
                  allowed_updates=["message", "callback_query"])
    if not updates and not changed:
        return
    for upd in updates or []:
        state["tg_offset"] = max(int(state.get("tg_offset") or 0),
                                 int(upd.get("update_id", 0)) + 1)
        try:
            if upd.get("callback_query"):
                _handle_callback(cfg, state, upd["callback_query"])
            elif upd.get("message"):
                _handle_message(cfg, state, upd["message"])
        except Exception:  # noqa: BLE001 - one odd update must not block the rest
            log.exception("Could not handle Telegram update %s", upd.get("update_id"))
    cfg.subscribers = list(state["subscribers"])
    save_state(cfg.state_file, state)
    set_output("state_changed", "true")


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
    "MEMBERS": "🔵 on sale to club members only",
    "SOLD_OUT": "🔴 sold out",
    "SOON": "🟡 not on sale yet",
    "RESALE": "🟠 resale only (official secondary market)",
    "UNKNOWN": "⚪️ status unclear",
}


# Order and wording of the per-check legend / totals line.
_STATUS_ORDER = ("AVAILABLE", "MEMBERS", "RESALE", "SOON", "SOLD_OUT", "UNKNOWN")
_STATUS_DOT = {s: _STATUS_LABEL[s].split(" ", 1)[0] for s in _STATUS_ORDER}
_STATUS_SHORT = {"AVAILABLE": "on sale", "MEMBERS": "members only",
                 "RESALE": "resale only", "SOON": "soon",
                 "SOLD_OUT": "sold out", "UNKNOWN": "unclear"}


def _source_heading(src: "Source") -> str:
    return f"{src.emoji + ' ' if src.emoji else ''}<b>{_esc(src.name.upper())}</b>"


def _summary_block(src: "Source", matched: list) -> str:
    """One team's section of the per-check report (heading + a line per match)."""
    lines = [_source_heading(src)]
    if not matched:
        lines.append("<i>no upcoming matches</i>")
        return "\n".join(lines)
    for ev in matched:
        dot = _STATUS_DOT.get(ev.status, "⚪️")
        when = f"<b>{_esc(ev.date)}</b>  " if ev.date else ""
        name = _esc(ev.title)
        if ev.url:  # tap the match to open its ticket page
            name = f'<a href="{_esc(ev.url)}">{name}</a>'
        lines.append(f"{dot} {when}{name}")
        details = _event_details(ev)
        if details:
            lines.append(f"      <i>{_esc(details)}</i>")
    return "\n".join(lines)


def _event_details(ev) -> str:
    """Second line under a match: competition / notes · 🏟 stadium."""
    venue = f"🏟 {ev.venue}" if getattr(ev, "venue", "") else ""
    return " · ".join(x for x in (ev.extra, venue) if x)


def _totals_line(statuses: list[str]) -> str:
    """'🟢 4 on sale · 🟡 7 soon · 🔴 3 sold out' (doubles as the legend)."""
    parts = [f"{_STATUS_DOT[s]} {statuses.count(s)} {_STATUS_SHORT[s]}"
             for s in _STATUS_ORDER if s in statuses]
    return " · ".join(parts) or "no upcoming matches"


TELEGRAM_MAX_CHARS = 3900  # Telegram's limit is 4096; keep a margin


def _pack_messages(header: str, blocks: list[str]) -> list[str]:
    """Join blocks (blank line between) into as few messages as fit the limit.

    A team's block is never split across messages unless it alone is too long.
    """
    messages, cur = [], header
    for block in blocks:
        while len(block) > TELEGRAM_MAX_CHARS:  # pathological: one huge block
            cut = block.rfind("\n", 0, TELEGRAM_MAX_CHARS)
            cut = cut if cut > 0 else TELEGRAM_MAX_CHARS
            messages.append(cur)
            cur, block = block[:cut], block[cut:].lstrip("\n")
        if len(cur) + 2 + len(block) > TELEGRAM_MAX_CHARS:
            messages.append(cur)
            cur = block
        else:
            cur = f"{cur}\n\n{block}" if cur else block
    if cur:
        messages.append(cur)
    return messages


# A site that keeps blocking GitHub's servers after this long (the loop
# switches servers meanwhile) is paused and retried every BAN_RETRY_MIN.
BAN_PAUSE_AFTER_MIN = 60
BAN_RETRY_MIN = 180


def _host(src: "Source") -> str:
    return urlparse(src.api_url or src.url).netloc.lower()


def _host_sources(cfg: Config, host: str) -> list["Source"]:
    return [s for s in cfg.sources if _host(s) == host]


def _process_source(cfg: Config, src: "Source", state: dict,
                    now_iso: str) -> tuple[bool, str, list[str], list | None]:
    """Check one source.

    Returns (state_changed, report_block, statuses, matched_events); the
    events are None when the site could not be read.
    """
    notified = state["notified"]
    failures = state["failures"]
    kinds = state.setdefault("fail_kind", {})
    blocked = state.setdefault("blocked_hosts", {})
    host = _host(src)
    now = _parse_iso(now_iso) or _now_utc()
    dirty = False
    pause = blocked.get(host) or {}
    paused_until = _parse_iso(pause.get("paused_until"))
    if paused_until and now < paused_until:
        kinds[src.id] = "paused"  # no server switching: every server is blocked
        block = (f"{_source_heading(src)}\n🚫 the site blocks our servers - next try "
                 f"{paused_until.astimezone(LISBON):%H:%M}")
        return False, block, [], None
    try:
        events = load_events(src)
    except Exception as err:  # noqa: BLE001 - handle any failure uniformly
        log.error("[%s] fetch/parse failed: %s", src.id, err)
        failures[src.id] = failures.get(src.id, 0) + 1
        kind = ("maintenance" if isinstance(err, SiteMaintenanceError)
                else "ban" if isinstance(err, SiteBlockedError) else "error")
        if kind == "ban":
            return True, _handle_ban(cfg, src, state, host, now, err), [], None
        if kind == "maintenance" and kinds.get(src.id) != "maintenance":
            telegram_send(  # owner only, once per maintenance window
                cfg, f"🛠 <b>{_esc(src.name)}</b>: the ticket site is down for "
                     f"maintenance (<i>{_esc(str(err).split(': ', 1)[-1])}</i>). "
                     "The bot keeps checking and will tell you when it's back - "
                     "sites often do this right before a big sale.",
                chats=[cfg.telegram_chat])
        kinds[src.id] = kind
        if kind != "maintenance":
            _maybe_alert_failure(cfg, src, failures[src.id], err)
        if kind == "maintenance":
            block = (f"{_source_heading(src)}\n🛠 site is down for maintenance - "
                     "checking until it's back")
        else:
            why = ("the site blocked this GitHub server's IP — switching to another "
                   "server automatically" if kind == "ban" else _esc(str(err)[:100]))
            block = (f"{_source_heading(src)}\n⚠️ could not read the site "
                     f"<i>({why})</i>")
        return True, block, [], None

    if failures.get(src.id) or kinds.get(src.id):
        failures[src.id] = 0
        if kinds.pop(src.id, None) == "maintenance":
            telegram_send(cfg, f"✅ <b>{_esc(src.name)}</b>: the ticket site is back "
                               "online.", chats=[cfg.telegram_chat])
        dirty = True
    gone = blocked.pop(host, None)
    if gone is not None:
        dirty = True
        if gone.get("notified"):
            names = ", ".join(s.name for s in _host_sources(cfg, host))
            telegram_send(cfg, f"✅ <b>{_esc(host)}</b> lets us in again - "
                               f"checks resumed ({_esc(names)}).",
                          chats=[cfg.telegram_chat])

    matched = [e for e in events if matches_keywords(e, src)]
    log.info("[%s] parsed %d events, %d match.", src.id, len(events), len(matched))

    phases_store = state.setdefault("sale_phases", {})
    for ev in matched:
        key = f"{src.id}:{ev.id}"
        if ev.phases:  # who may buy when: for the personal sale windows
            phases_store[key] = {"source": src.id, "title": ev.title, "url": ev.url,
                                 "date": ev.date or "", "phases": ev.phases,
                                 "start": ev.start.isoformat() if ev.start else None}
            dirty = True
        elif key in phases_store:
            del phases_store[key]
            dirty = True
        entry = notified.get(key)
        # "level" = the sale phase already alerted; entries from before
        # members alerts existed have none and were public alerts.
        level = (entry or {}).get("level", "AVAILABLE")
        members = (ev.status == "MEMBERS" and src.club
                   and bool(_recipients(cfg, state, src.id, members=True)))
        if ev.status == "AVAILABLE" or members:
            if entry is not None and (members or level == "AVAILABLE"):
                # Already alerted for this phase (or public sale fell back to
                # members-only, which the owner already knows about).
                entry["last_seen"] = now_iso
                entry["level"] = ev.status
                dirty = True
                continue
            # Members-only sales: only users who said they're members there.
            chats = _recipients(cfg, state, src.id, members=ev.status == "MEMBERS")
            if ev.status == "MEMBERS" and ev.phases:
                # Users who listed their sócios get their own window instead.
                chats = [c for c in chats if not _members_of(state, c)]
            if not chats or telegram_send(
                    cfg, format_notification(ev, src.name, ev.status == "MEMBERS"),
                    chats=chats):
                log.info("[%s] notified (%s): %s", src.id, ev.status, ev.title)
                notified[key] = {
                    "source": src.id,
                    "title": ev.title,
                    "url": ev.url,
                    "level": ev.status,
                    "first_notified": now_iso,
                    "last_seen": now_iso,
                }
                dirty = True
            else:
                log.error("[%s] notify failed for %s; retry next run.",
                          src.id, ev.title)
        elif entry is not None:
            # Not buyable any more: forget it, so tickets coming back (returns,
            # a new sale phase) trigger a fresh alert.
            del notified[key]
            dirty = True
    return dirty, _summary_block(src, matched), [e.status for e in matched], matched


def run_normal(cfg: Config) -> int:
    try:
        poll_access_requests(cfg)  # /start requests, owner's Allow/Deny taps
    except Exception:  # noqa: BLE001 - never let Telegram I/O stop a check
        log.exception("Access-request polling failed.")
    state = load_state(cfg.state_file)
    cfg.subscribers = list(state["subscribers"])
    try:  # personal sale-window reminders: every tick, minute-accurate
        if sale_window_reminders(cfg, state, _now_utc()):
            save_state(cfg.state_file, state)
            set_output("state_changed", "true")
    except Exception:  # noqa: BLE001 - never let reminders stop a check
        log.exception("Sale-window reminders failed.")
    now_lisbon = datetime.now(LISBON)
    act, _is_night = should_act(now_lisbon, state)
    if not act:
        return 0

    state["last_check_utc"] = _now_utc().isoformat()  # for the min-interval gate
    pick_next_gaps(state)
    dirty = True

    now_iso = _now_utc().isoformat()
    _FETCH_MEMO.clear()  # fresh data each check (shared by same-site sources)
    _ALERTED_HOSTS.clear()
    blocks: dict[str, str] = {}
    statuses: dict[str, list[str]] = {}
    found: dict[str, list | None] = {}
    for src in cfg.sources:
        changed, block, sts, events = _process_source(cfg, src, state, now_iso)
        dirty = dirty or changed
        blocks[src.id] = block
        statuses[src.id] = sts
        found[src.id] = events

    # Served by /status (filtered per user) and used for the reports below.
    state["last_report"] = {"time": now_lisbon.strftime("%H:%M %d.%m"),
                            "blocks": blocks, "statuses": statuses}
    state.pop("last_summary", None)  # pre-preferences format
    first_snapshot = "snapshot" not in state
    change_blocks = _diff_snapshot(cfg, state, found)
    if cfg.report_mode == "every":
        _send_by_teams(cfg, state, lambda teams: _report_messages(cfg, state, teams))
    elif first_snapshot:
        intro = ("ℹ️ <b>From now on you'll only get a message when something "
                 "changes</b> (tickets go on sale, a match sells out, a new match "
                 "appears...). Send /status any time for the full overview.\n\n")
        _send_by_teams(cfg, state, lambda teams: [
            (intro if i == 0 else "") + m
            for i, m in enumerate(_report_messages(cfg, state, teams))])
    elif change_blocks:
        head = f"🔔 <b>Changes</b> · {now_lisbon.strftime('%H:%M %d.%m')}"
        _send_by_teams(cfg, state, lambda teams: _pack_messages(
            head, [change_blocks[sid] for sid in teams if sid in change_blocks])
            if any(sid in change_blocks for sid in teams) else [])

    if _prune_state(state, now_iso):
        dirty = True

    if dirty:
        save_state(cfg.state_file, state)
        set_output("state_changed", "true")
    return 0


def _send_by_teams(cfg: Config, state: dict, build) -> None:
    """Send build(teams) to every recipient, each getting only their teams;
    recipients with the same teams share one build."""
    groups: dict[tuple, list[str]] = {}
    for cid in _all_chats(cfg):
        groups.setdefault(tuple(_prefs(cfg, state, cid)["sources"]), []).append(cid)
    for teams, chats in groups.items():
        for msg in build(list(teams)):
            telegram_send(cfg, msg, preview=False, chats=chats)  # no preview cards


def _event_line(ev, prefix: str) -> list[str]:
    when = f"<b>{_esc(ev.date)}</b>  " if ev.date else ""
    name = f'<a href="{_esc(ev.url)}">{_esc(ev.title)}</a>' if ev.url else _esc(ev.title)
    lines = [f"{prefix} {when}{name}"]
    details = _event_details(ev)
    if details:
        lines.append(f"      <i>{_esc(details)}</i>")
    return lines


def _diff_snapshot(cfg: Config, state: dict, found: dict) -> dict[str, str]:
    """Update state["snapshot"] and return per-team blocks of what changed.

    A change is a new match or a status change. Changes *to* "on sale" are
    left out: the dedicated "Tickets on sale!" alert already covers them.
    A source that could not be read keeps its previous snapshot, so a site
    hiccup doesn't look like every match vanished and came back.
    """
    old = state.get("snapshot") or {}
    new: dict[str, dict] = {}
    blocks: dict[str, str] = {}
    for src in cfg.sources:
        events = found.get(src.id)
        if events is None:
            if src.id in old:
                new[src.id] = old[src.id]
            continue
        before = old.get(src.id)
        new[src.id] = {e.id: e.status for e in events}
        if before is None:
            continue  # first time we see this source: baseline only
        lines = []
        for ev in events:
            prev = before.get(ev.id)
            if prev == ev.status or ev.status == "AVAILABLE":
                continue
            dot = _STATUS_DOT.get(ev.status, "⚪️")
            if prev is None:
                lines += _event_line(ev, f"🆕 {dot}")
            else:
                lines += _event_line(ev, f"{_STATUS_DOT.get(prev, '⚪️')} → {dot}")
        if lines:
            blocks[src.id] = "\n".join([_source_heading(src)] + lines)
    state["snapshot"] = new
    return blocks


def _should_rotate(state: dict, elapsed_min: float) -> str:
    """Name of a source worth leaving this machine for, or "".

    Sites like FPF ban individual GitHub runner IPs; a loop run keeps one IP
    for hours, so it would stay blind. Ending the run early hands over to a
    fresh run (usually on another machine/IP). A detected ban rotates after
    one failed check, other errors after two, a maintenance page never (it
    is down for everyone); never more often than every
    ROTATE_MIN_ELAPSED_MIN, so a real site outage can't cause a restart storm.
    """
    if elapsed_min < ROTATE_MIN_ELAPSED_MIN:
        return ""
    kinds = state.get("fail_kind") or {}
    for sid, n in (state.get("failures") or {}).items():
        kind = kinds.get(sid, "error")
        if kind in ("maintenance", "paused"):
            continue  # down for everyone / blocks every server: a new IP won't help
        if n >= (1 if kind == "ban" else 2):
            return sid
    return ""


def run_loop(cfg: Config, minutes: float) -> int:
    """Stay alive for `minutes`, running a check whenever one is due.

    GitHub's cron fires every few hours at best, so instead of relying on it
    the job itself keeps the random 20-40 min / 100-140 min cadence via should_act(). Ends
    early when a source keeps failing (see _should_rotate); the workflow then
    starts the next run on a different machine.
    """
    started = time.monotonic()
    deadline = started + minutes * 60
    log.info("Loop mode: running for %.0f min.", minutes)
    if cfg.telegram_token:  # command menu shown in Telegram's "/" button
        _tg(cfg, "setMyCommands", commands=[
            {"command": "status", "description": "Current ticket overview"},
            {"command": "settings", "description": "Choose teams / membership"},
            {"command": "members", "description": "Your Sporting sócios (sale windows)"},
            {"command": "start", "description": "Subscribe to ticket alerts"},
            {"command": "stop", "description": "Stop receiving messages"}])
    while True:
        try:
            run_normal(cfg)
        except Exception:  # noqa: BLE001 - one bad check must not end the loop
            log.exception("Check failed; will retry on the next tick.")
        sid = _should_rotate(load_state(cfg.state_file),
                             (time.monotonic() - started) / 60)
        if sid:
            log.warning("Loop mode: [%s] keeps failing here; ending early so "
                        "the next run starts on another machine (new IP).", sid)
            st = load_state(cfg.state_file)
            st["last_check_utc"] = None  # let the next run re-check right away
            save_state(cfg.state_file, st)
            set_output("state_changed", "true")
            break
        if time.monotonic() + LOOP_POLL_SEC >= deadline:
            break
        _wait_answering(cfg, LOOP_POLL_SEC)
    log.info("Loop mode: done.")
    return 0


def _wait_answering(cfg: Config, seconds: float) -> None:
    """Sleep `seconds`, answering Telegram messages/taps as they arrive."""
    until = time.monotonic() + seconds
    while (left := until - time.monotonic()) > 1:
        if not cfg.telegram_token:
            time.sleep(left)
            return
        t0 = time.monotonic()
        try:
            poll_access_requests(cfg, wait=int(min(left, 25)))
        except Exception:  # noqa: BLE001 - keep the loop alive
            log.exception("Telegram polling failed.")
        if time.monotonic() - t0 < 1:  # error / no long-poll: don't spin
            time.sleep(min(5, max(0, until - time.monotonic())))


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
    for key, g in list((state.get("sale_phases") or {}).items()):
        start = _parse_iso(g.get("start"))
        if start is not None and (now - start).total_seconds() > 86400:
            del state["sale_phases"][key]  # game played
            changed = True
    for key, when in list((state.get("phase_sent") or {}).items()):
        t = _parse_iso(when)
        if t is not None and (now - t).total_seconds() > 30 * 86400:
            del state["phase_sent"][key]
            changed = True
    return changed


def _handle_ban(cfg: Config, src: "Source", state: dict, host: str, now: datetime,
                err: Exception) -> str:
    """The site's firewall refused us. Meanwhile the loop switches servers;
    if that hasn't helped for BAN_PAUSE_AFTER_MIN, pause the site and retry
    every BAN_RETRY_MIN, telling the owner once (per site, not per source)."""
    kinds = state.setdefault("fail_kind", {})
    entry = state["blocked_hosts"].setdefault(host, {"since": now.isoformat()})
    since = _parse_iso(entry.get("since")) or now
    heading = _source_heading(src)
    if (now - since).total_seconds() < BAN_PAUSE_AFTER_MIN * 60:
        kinds[src.id] = "ban"  # -> the loop moves to another server
        return (f"{heading}\n⚠️ could not read the site <i>(it blocked this GitHub "
                "server - switching to another one automatically)</i>")
    retry = now.timestamp() + BAN_RETRY_MIN * 60
    entry["paused_until"] = datetime.fromtimestamp(retry, timezone.utc).isoformat()
    for s in _host_sources(cfg, host):
        kinds[s.id] = "paused"
    if not entry.get("notified"):
        entry["notified"] = True
        names = ", ".join(s.name for s in _host_sources(cfg, host))
        telegram_send(
            cfg, f"🚫 <b>{_esc(host)}</b> blocks GitHub's servers (all of them, for "
                 f"{int((now - since).total_seconds() // 60)} min now): "
                 f"<i>{_esc(str(err)[:120])}</i>\n"
                 f"Paused: {_esc(names)}. The bot retries every "
                 f"{BAN_RETRY_MIN // 60} h and tells you when it works again.",
            chats=[cfg.telegram_chat])
    return (f"{heading}\n🚫 the site blocks our servers - next try "
            f"{datetime.fromtimestamp(retry, LISBON):%H:%M}")


_ALERTED_HOSTS: set[str] = set()  # this check: one failure alert per site


def _maybe_alert_failure(cfg: Config, src: "Source", n: int, err: Exception) -> None:
    host = _host(src)
    if host in _ALERTED_HOSTS:
        return  # another source on the same site already reported it
    _ALERTED_HOSTS.add(host)
    if n == FAILURE_ALERT_THRESHOLD or (
        n > FAILURE_ALERT_THRESHOLD and n % FAILURE_REALERT_EVERY == 0
    ):
        telegram_send(  # technical alert: owner only
            cfg,
            f"⚠️ <b>Ticket monitor</b> — {_esc(src.name)}\n"
            f"Could not read the site {n} checks in a row.\n"
            f"<code>{_esc(str(err))[:300]}</code>",
            chats=[cfg.telegram_chat],
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
