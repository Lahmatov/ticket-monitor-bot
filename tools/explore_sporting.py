#!/usr/bin/env python3
"""One-off explorer: open tickets.sporting.pt in Chromium, click into a match
and log every API call the site makes (to learn where per-sector availability
comes from). Not used by the monitor itself.

Env: MATCH_TEXT (default "LASK") - text identifying the match card to open.
"""
import json
import os
import re

from playwright.sync_api import sync_playwright

BASE = "https://tickets.sporting.pt/pt"
MATCH = os.environ.get("MATCH_TEXT", "LASK")
seen = []


def short(body: str, n: int = 2500) -> str:
    try:
        data = json.loads(body)

        def strip(o):
            if isinstance(o, dict):
                return {k: ("<html…>" if isinstance(v, str) and len(v) > 300 else strip(v))
                        for k, v in o.items()}
            if isinstance(o, list):
                return [strip(x) for x in o[:40]]
            return o
        body = json.dumps(strip(data), ensure_ascii=False)
    except Exception:  # noqa: BLE001
        pass
    return re.sub(r"\s+", " ", body)[:n]


def on_response(resp):
    url = resp.url
    if "/api/" not in url and "api." not in url:
        return
    try:
        body = resp.text()
    except Exception:  # noqa: BLE001
        body = "(no body)"
    seen.append(url)
    print(f"\n[{resp.status}] {resp.request.method} {url}\n    {short(body)}", flush=True)


def page_text(page, n=1500):
    try:
        return re.sub(r"\s+", " ", page.inner_text("body"))[:n]
    except Exception as err:  # noqa: BLE001
        return f"(text failed: {err})"


with sync_playwright() as p:
    browser = p.chromium.launch()
    page = browser.new_page(locale="pt-PT", viewport={"width": 1366, "height": 2000})
    page.on("response", on_response)

    print(f"### STEP 1: open {BASE}")
    page.goto(BASE, wait_until="networkidle", timeout=60000)
    page.wait_for_timeout(3000)
    print("\n### PAGE TEXT:", page_text(page))

    # Collect candidate links/buttons near the match card.
    print("\n### LINKS on page:")
    for a in page.query_selector_all("a[href]")[:80]:
        href = a.get_attribute("href") or ""
        if any(k in href.lower() for k in ("jogo", "game", "match", "evento", "bilhete", "ticket")):
            print("   ", href, "|", re.sub(r"\s+", " ", a.inner_text())[:60])

    card = page.locator(f"text={MATCH}").first
    print(f"\n### STEP 2: click near '{MATCH}' (found={card.count()})")
    clicked = False
    if card.count():
        # climb to an ancestor that contains a clickable button
        for depth in range(1, 8):
            anc = card.locator("xpath=" + "/".join([".."] * depth))
            btns = anc.locator("button, a")
            if btns.count():
                for i in range(btns.count()):
                    t = re.sub(r"\s+", " ", btns.nth(i).inner_text() or "")
                    print(f"    depth {depth} button[{i}]: {t[:50]!r}")
                target = btns.last
                try:
                    target.click(timeout=10000)
                    clicked = True
                except Exception as err:  # noqa: BLE001
                    print("    click failed:", err)
                break
    page.wait_for_timeout(6000)
    print("\n### URL after click:", page.url, "clicked:", clicked)
    print("### PAGE TEXT:", page_text(page, 3000))

    # Try clicking further into a sector/ticket selection if present.
    for label in ("Comprar", "Bilhetes", "Continuar", "Escolher", "Público", "Publico"):
        loc = page.locator(f"button:has-text('{label}'), a:has-text('{label}')")
        if loc.count():
            print(f"\n### STEP 3: click '{label}' ({loc.count()} found)")
            try:
                loc.first.click(timeout=8000)
                page.wait_for_timeout(6000)
                print("### URL:", page.url)
                print("### PAGE TEXT:", page_text(page, 3000))
            except Exception as err:  # noqa: BLE001
                print("    click failed:", err)
            break

    print(f"\n### {len(seen)} API responses captured:")
    for u in seen:
        print("   ", u)
    browser.close()
