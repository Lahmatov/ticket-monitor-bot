#!/usr/bin/env python3
"""One-off explorer: open ticket sites in Chromium and log every data (XHR /
fetch / JSON) response, the visible page text and event-looking links. Used
to discover the JSON endpoint behind a ticketing SPA. Not used by the monitor.

Env: EXPLORE_URLS - comma-separated URLs to open.
"""
import json
import os
import re

from playwright.sync_api import sync_playwright

BODY_CHARS = int(os.environ.get("BODY_CHARS", "700"))
LINK_RE = re.compile(os.environ.get("LINK_RE", r"bilhete|ticket|/event"), re.I)
ONLY_RE = re.compile(os.environ["ONLY_RE"], re.I) if os.environ.get("ONLY_RE") else None
URLS = [u.strip() for u in os.environ.get("EXPLORE_URLS", "").split(",") if u.strip()]
NOISE = ("google", "facebook", "doubleclick", "hotjar", "clarity", "analytics",
         "cookiebot", "onetrust", "gtm", "tiktok", "linkedin", "sentry", "fonts.",
         "applicationinsights", "newrelic", "cdn-cgi")


def short(body: str, n: int = 2000) -> str:
    try:
        data = json.loads(body)

        def strip(o):
            if isinstance(o, dict):
                return {k: ("<long…>" if isinstance(v, str) and len(v) > 200 else strip(v))
                        for k, v in o.items()}
            if isinstance(o, list):
                return [strip(x) for x in o[:15]]
            return o
        body = json.dumps(strip(data), ensure_ascii=False)
    except Exception:  # noqa: BLE001
        pass
    return re.sub(r"\s+", " ", body)[:n]


def explore(browser, url):
    print(f"\n{'#' * 78}\n### OPEN {url}\n{'#' * 78}", flush=True)
    page = browser.new_page(locale="pt-PT", viewport={"width": 1366, "height": 2400})
    captured = []

    def on_response(resp):
        u = resp.url
        rtype = resp.request.resource_type
        ctype = resp.headers.get("content-type", "")
        if any(n in u.lower() for n in NOISE):
            return
        if rtype not in ("xhr", "fetch") and "json" not in ctype:
            return
        try:
            body = resp.text()
        except Exception:  # noqa: BLE001
            body = "(no body)"
        post = ""
        if resp.request.method == "POST" and resp.request.post_data:
            post = "\n    POST BODY: " + re.sub(r"\s+", " ", resp.request.post_data)[:4000]
        if ONLY_RE and not ONLY_RE.search(u + post):
            return
        captured.append(f"[{resp.status}] {resp.request.method} {u}  ({ctype[:30]}, "
                        f"{len(body)}b){post}\n    {short(body, BODY_CHARS)}")

    page.on("response", on_response)
    try:
        page.goto(url, wait_until="networkidle", timeout=60000)
    except Exception as err:  # noqa: BLE001
        print("goto:", err)
    page.wait_for_timeout(5000)
    # scroll to trigger lazy loads
    for _ in range(4):
        page.mouse.wheel(0, 1500)
        page.wait_for_timeout(1000)
    print("\n### FINAL URL:", page.url)
    try:
        text = re.sub(r"\s+", " ", page.inner_text("body"))
    except Exception as err:  # noqa: BLE001
        text = f"(text failed: {err})"
    print("### PAGE TEXT:", text[:int(os.environ.get("TEXT_CHARS", "1500"))])
    print("### LINKS:")
    seen = set()
    for a in page.query_selector_all("a[href]"):
        href = a.get_attribute("href") or ""
        if href in seen:
            continue
        seen.add(href)
        if LINK_RE.search(href):
            print("   ", href[:150], "|", re.sub(r"\s+", " ", a.inner_text())[:60])
    n_cards = int(os.environ.get("CARD_DUMP", "3"))
    if n_cards:
        print(f"### CARD HTML (first {n_cards} cards around matching links):")
        dumped = 0
        for a in page.query_selector_all("a[href]"):
            if dumped >= n_cards or not LINK_RE.search(a.get_attribute("href") or ""):
                continue
            html = a.evaluate("""el => {
                let n = el;
                for (let i = 0; i < 8 && n.parentElement; i++) {
                    n = n.parentElement;
                    if ((n.innerText || '').length > 120) break;
                }
                const c = n.cloneNode(true);
                c.querySelectorAll('script,style,svg,img,picture,source').forEach(x => x.remove());
                c.querySelectorAll('*').forEach(x => {
                    for (const at of [...x.attributes])
                        if (!['class','href','id','disabled','data-status'].includes(at.name)) x.removeAttribute(at.name);
                });
                return c.outerHTML;
            }""")
            print("----- card", dumped + 1, "-----")
            print(re.sub(r"\s+", " ", html)[:int(os.environ.get("CARD_CHARS", "2500"))])
            dumped += 1
    print(f"### {len(captured)} data responses:")
    for c in captured:
        print(c)
    page.close()


with sync_playwright() as p:
    b = p.chromium.launch()
    for u in URLS:
        explore(b, u)
    b.close()
