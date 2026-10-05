#!/usr/bin/env python3
"""
Website uptime monitor for GitHub Actions (Python standard library only).

What it does
  - Checks every site in sites.json: HTTP status, error pages (WordPress/PHP/
    suspended), blank pages, broken CSS/JS files, and an optional keyword
  - Retries a failing site before counting it as down (avoids false alarms)
  - Treats firewall / bot-protection blocks (401/403/429, Cloudflare challenge)
    as "BLOCKED", not "DOWN", because the server did answer
  - If most sites fail at the same moment, sends ONE "monitor problem" alert
    instead of a flood of DOWN alerts (usually the runner's network is blocked)
  - Sends one combined alert for sites that go DOWN and one for RECOVERED
  - Warns once when an SSL certificate is close to expiry (checked daily)
  - Alerts go to email AND Slack (whichever is configured)
  - Optional: posts a summary of EVERY run to Slack (SLACK_EVERY_RUN=true)
  - Saves state in state.json; a failed alert is retried on the next run

Environment variables (GitHub repository secrets / variables)
  Email : SMTP_HOST, SMTP_PORT, SMTP_USER, SMTP_PASS, MAIL_FROM, ALERT_EMAILS
  Slack : SLACK_WEBHOOK_URL   Slack Incoming Webhook URL
          SLACK_EVERY_RUN     "true" = post a summary to Slack on every run
  Test  : TEST_EMAIL          "true" = send a test email + Slack message and exit

sites.json options per site:
  "name"            display name (required, must be unique)
  "url"             address to check (required)
  "keyword"         text that must appear on the page (optional, recommended)
  "blocked_is_down" true = treat a firewall block (403 etc.) as DOWN (optional)
  "check_assets"    false = don't check the page's CSS/JS files (optional)
  "allow_blank"     true = don't flag pages with very little text (optional)
"""
import json
import os
import smtplib
import socket
import ssl
import sys
import time
import urllib.error
import urllib.request
import zlib
from concurrent.futures import ThreadPoolExecutor
from datetime import datetime, timezone
from email.message import EmailMessage
from html.parser import HTMLParser
from urllib.parse import urljoin, urlparse

# ----------------------------------------------------------------- settings
CONFIG_FILE = "sites.json"
STATE_FILE = "state.json"

TIMEOUT = 15              # seconds per request
RETRIES = 3               # attempts per run before a check counts as failed
RETRY_DELAY = 10          # seconds between attempts
MAX_WORKERS = 16          # sites checked in parallel
FAIL_THRESHOLD = 1        # failed runs in a row before a DOWN alert (1 = alert immediately;
                          # each run already retries a failing site RETRIES times)
SSL_WARN_DAYS = 14        # warn when certificate expires within this many days
MAX_BODY = 2_000_000      # bytes of the page to read
MIN_VISIBLE_TEXT = 30     # fewer visible characters than this = "blank page"
CHECK_ASSETS = True       # also check the page's own CSS/JS files (per-site "check_assets" overrides)
MAX_ASSETS = 25           # max CSS/JS files checked per site
ASSET_TIMEOUT = 10        # seconds per CSS/JS file

MASS_FAILURE_RATIO = 0.6  # if this share of sites is down at once...
MASS_FAILURE_MIN_SITES = 5  # ...(and at least this many sites exist), suspect the monitor

BLOCKED_CODES = {401, 403, 429}
BLOCKED_IS_DOWN_DEFAULT = False  # per-site "blocked_is_down" overrides this

# Slack Incoming Webhook URL. Paste yours here, or leave empty to use the
# SLACK_WEBHOOK_URL environment variable / GitHub secret instead.
SLACK_WEBHOOK_URL: ${{ secrets.SLACK_WEBHOOK_URL }}
SLACK_EVERY_RUN = True    # True = post a summary to Slack on every run

SLACK_TIMEOUT = 15        # seconds for the Slack webhook request
SLACK_MAX_CHARS = 3500    # keep Slack messages readable (longer text is cut)

HEADERS = {
    "User-Agent": ("Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
                   "(KHTML, like Gecko) Chrome/140.0.0.0 Safari/537.36"),
    "Accept": "text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8",
    "Accept-Language": "en-US,en;q=0.9",
    "Accept-Encoding": "gzip, deflate",
    "Cache-Control": "no-cache",
}

# Text that means the site is broken even if the server answers.
ERROR_MARKERS = [
    "Error establishing a database connection",
    "There has been a critical error on this website",
    "Briefly unavailable for scheduled maintenance",
    "This Account has been suspended",
    "Account Suspended",
    "suspendedpage.cgi",
    "This domain has expired",
    "This domain name has expired",
    "Website is no longer available",
    "<b>Fatal error</b>:",
    "<b>Parse error</b>:",
    "PHP Fatal error",
    "Fatal error: Uncaught",
]

UP, DOWN, BLOCKED = "UP", "DOWN", "BLOCKED"
TIME_FMT = "%Y-%m-%d %H:%M UTC"
ICONS = {UP: "🟢", DOWN: "🔴", BLOCKED: "🟡"}


# ------------------------------------------------------------------ helpers
def now_str():
    return datetime.now(timezone.utc).strftime(TIME_FMT)


def today_str():
    return datetime.now(timezone.utc).strftime("%Y-%m-%d")


def duration_since(since):
    try:
        start = datetime.strptime(since, TIME_FMT).replace(tzinfo=timezone.utc)
    except (TypeError, ValueError):
        return "unknown"
    minutes = int((datetime.now(timezone.utc) - start).total_seconds() // 60)
    days, rem = divmod(minutes, 1440)
    hours, mins = divmod(rem, 60)
    parts = [f"{days}d"] if days else []
    if hours:
        parts.append(f"{hours}h")
    parts.append(f"{mins}m")
    return " ".join(parts)


def decode_body(raw, content_encoding):
    enc = (content_encoding or "").lower()
    try:
        if "gzip" in enc:
            raw = zlib.decompressobj(16 + zlib.MAX_WBITS).decompress(raw)
        elif "deflate" in enc:
            try:
                raw = zlib.decompressobj().decompress(raw)
            except zlib.error:
                raw = zlib.decompressobj(-zlib.MAX_WBITS).decompress(raw)
    except zlib.error:
        pass
    return raw.decode("utf-8", errors="ignore")


def find_error_marker(body):
    low = body.lower()
    for marker in ERROR_MARKERS:
        if marker.lower() in low:
            return marker
    return None


class PageParser(HTMLParser):
    """Collects the visible text and the CSS/JS files a page needs."""
    HIDDEN = {"script", "style", "noscript", "template", "title"}

    def __init__(self):
        super().__init__(convert_charrefs=True)
        self.text, self.assets, self._hidden = [], [], 0

    def handle_starttag(self, tag, attrs):
        a = {k: (v or "") for k, v in attrs}
        if tag == "script" and a.get("src"):
            self.assets.append(("JS", a["src"]))
        elif tag == "link" and "stylesheet" in a.get("rel", "").lower().split() and a.get("href"):
            self.assets.append(("CSS", a["href"]))
        if tag in self.HIDDEN:
            self._hidden += 1

    def handle_endtag(self, tag):
        if tag in self.HIDDEN and self._hidden:
            self._hidden -= 1

    def handle_data(self, data):
        if not self._hidden:
            self.text.append(data)


def parse_page(body):
    parser = PageParser()
    try:
        parser.feed(body)
        parser.close()
    except Exception:
        pass
    visible = " ".join(" ".join(parser.text).split())
    return visible, parser.assets


def same_site(asset_url, page_url):
    a = (urlparse(asset_url).hostname or "").lower()
    p = (urlparse(page_url).hostname or "").lower()
    base = p[4:] if p.startswith("www.") else p
    return a == base or a.endswith("." + base)


def check_asset(kind, url):
    """Return None if the file loads fine, otherwise a short problem description."""
    req = urllib.request.Request(url, headers={
        "User-Agent": HEADERS["User-Agent"],
        "Accept": "text/css,*/*;q=0.1" if kind == "CSS" else "*/*",
        "Referer": url,
    })
    try:
        with urllib.request.urlopen(req, timeout=ASSET_TIMEOUT) as resp:
            start = resp.read(512).lstrip().lower()
    except urllib.error.HTTPError as e:
        if e.code in BLOCKED_CODES:
            return None          # firewall, not a broken file
        return f"HTTP {e.code}"
    except Exception as e:
        reason = getattr(e, "reason", e)
        return f"failed to load ({reason})"
    if start.startswith((b"<!doctype", b"<html", b"<head", b"<body")):
        return "server sent an HTML page instead of the file (probably an error page)"
    return None


def check_assets(page_url, assets):
    """Check the page's own CSS/JS files. Returns a list of problems."""
    urls, seen = [], set()
    for kind, src in assets:
        full = urljoin(page_url, src.strip())
        if urlparse(full).scheme not in ("http", "https"):
            continue
        if not same_site(full, page_url) or full in seen:
            continue                 # skip Google Fonts, analytics, CDNs...
        seen.add(full)
        urls.append((kind, full))
    urls = urls[:MAX_ASSETS]
    if not urls:
        return []
    with ThreadPoolExecutor(max_workers=6) as pool:
        results = list(pool.map(lambda ku: check_asset(*ku), urls))
    problems = []
    for (kind, full), problem in zip(urls, results):
        if problem:
            name = urlparse(full).path.rsplit("/", 1)[-1] or full
            problems.append(f"{kind} file {name} -> {problem}")
    return problems


# ------------------------------------------------------------------- checks
def check_once(site):
    """Return (status, reason, page) for a single request. page is set when the HTML loaded."""
    req = urllib.request.Request(site["url"], headers=HEADERS)
    start = time.time()
    try:
        with urllib.request.urlopen(req, timeout=TIMEOUT) as resp:
            code = resp.status
            final_url = resp.geturl()
            body = decode_body(resp.read(MAX_BODY), resp.headers.get("Content-Encoding"))
    except urllib.error.HTTPError as e:
        try:
            err_body = decode_body(e.read(MAX_BODY), e.headers.get("Content-Encoding"))
        except Exception:
            err_body = ""
        marker = find_error_marker(err_body)
        if marker:
            return DOWN, f"HTTP {e.code}, error page: '{marker}'", None
        challenge = (e.headers.get("cf-mitigated") or "").lower() == "challenge"
        if e.code in BLOCKED_CODES or challenge:
            return BLOCKED, f"HTTP {e.code} {e.reason} (firewall/bot protection blocked the monitor)", None
        return DOWN, f"HTTP {e.code} {e.reason}", None
    except urllib.error.URLError as e:
        r = e.reason
        if isinstance(r, ssl.SSLCertVerificationError):
            return DOWN, f"SSL certificate problem: {r.verify_message}", None
        if isinstance(r, socket.gaierror):
            return DOWN, "DNS lookup failed (domain does not resolve)", None
        if isinstance(r, (socket.timeout, TimeoutError)):
            return DOWN, f"Timed out after {TIMEOUT}s", None
        if isinstance(r, ConnectionRefusedError):
            return DOWN, "Connection refused", None
        return DOWN, f"Connection failed: {r}", None
    except (socket.timeout, TimeoutError):
        return DOWN, f"Timed out after {TIMEOUT}s", None
    except Exception as e:
        return DOWN, f"{type(e).__name__}: {e}", None

    elapsed = time.time() - start
    marker = find_error_marker(body)
    if marker:
        return DOWN, f"HTTP {code}, error page: '{marker}'", None

    keyword = (site.get("keyword") or "").strip()
    if keyword and keyword.lower() not in body.lower():
        return DOWN, f"HTTP {code}, but expected text '{keyword}' not found on page", None

    visible, assets = parse_page(body)
    if len(visible) < MIN_VISIBLE_TEXT and not site.get("allow_blank"):
        return DOWN, (f"Blank page: HTTP {code} but almost no visible content "
                      f"({len(visible)} characters of text, {len(body)} bytes)"), None

    return UP, f"HTTP {code} in {elapsed:.1f}s", {"url": final_url, "assets": assets}


def check_site(site):
    status, reason = DOWN, ""
    for attempt in range(1, RETRIES + 1):
        status, reason, page = check_once(site)
        if status == UP and page and site.get("check_assets", CHECK_ASSETS):
            problems = check_assets(page["url"], page["assets"])
            if problems:
                status = DOWN
                reason = (f"Page HTML loads ({reason}) but {len(problems)} required file(s) "
                          f"are broken, so visitors may see a blank/broken page: "
                          + "; ".join(problems[:5]))
        if status in (UP, BLOCKED):   # retrying a firewall block is pointless
            break
        if attempt < RETRIES:
            time.sleep(RETRY_DELAY)
    return site, status, reason


def ssl_days_left(url):
    host = urlparse(url).hostname
    if not url.lower().startswith("https://") or not host:
        return None
    try:
        ctx = ssl.create_default_context()
        with socket.create_connection((host, 443), timeout=TIMEOUT) as sock:
            with ctx.wrap_socket(sock, server_hostname=host) as ssock:
                cert = ssock.getpeercert()
        expires = ssl.cert_time_to_seconds(cert["notAfter"])
        return int((expires - time.time()) // 86400)
    except Exception:
        return None  # broken/expired certificates are already caught by the main check


# -------------------------------------------------------------------- email
def send_email(subject, body):
    """Send an email. Returns True on success, False on any problem (never crashes)."""
    host = os.environ.get("SMTP_HOST")
    port = int(os.environ.get("SMTP_PORT") or 587)
    user = os.environ.get("SMTP_USER")
    password = os.environ.get("SMTP_PASS")
    sender = os.environ.get("MAIL_FROM") or user
    recipients = [a.strip() for a in os.environ.get("ALERT_EMAILS", "").split(",") if a.strip()]

    if not (host and user and password and recipients):
        print("!! Email settings missing (check repository secrets). Email NOT sent:")
        print(f"   {subject}")
        return False

    msg = EmailMessage()
    msg["Subject"] = subject
    msg["From"] = sender
    msg["To"] = ", ".join(recipients)
    msg.set_content(body)

    try:
        if port == 465:
            with smtplib.SMTP_SSL(host, port, context=ssl.create_default_context(), timeout=30) as s:
                s.login(user, password)
                s.send_message(msg)
        else:
            with smtplib.SMTP(host, port, timeout=30) as s:
                s.starttls(context=ssl.create_default_context())
                s.login(user, password)
                s.send_message(msg)
    except Exception as e:
        print(f"!! Email failed ({type(e).__name__}: {e}). Will retry next run: {subject}")
        return False

    print(f"Email sent to {len(recipients)} recipient(s): {subject}")
    return True


# -------------------------------------------------------------------- slack
def slack_escape(text):
    """Slack treats & < > as control characters; escape them so error text shows as-is."""
    return text.replace("&", "&amp;").replace("<", "&lt;").replace(">", "&gt;")


def send_slack(text):
    """Post a message to Slack via an Incoming Webhook.
    Returns True on success, False if not configured or on any problem (never crashes)."""
    url = (os.environ.get("SLACK_WEBHOOK_URL") or SLACK_WEBHOOK_URL or "").strip()
    if not url or "XXX/YYY/ZZZ" in url:
        return False

    if len(text) > SLACK_MAX_CHARS:
        text = text[:SLACK_MAX_CHARS] + "\n… (truncated, see the GitHub Actions run for details)"

    data = json.dumps({"text": text}).encode("utf-8")
    req = urllib.request.Request(url, data=data, headers={"Content-Type": "application/json"})
    try:
        with urllib.request.urlopen(req, timeout=SLACK_TIMEOUT) as resp:
            ok = resp.status == 200
    except urllib.error.HTTPError as e:
        print(f"!! Slack failed (HTTP {e.code}: {e.read(200).decode('utf-8', 'ignore')})")
        return False
    except Exception as e:
        print(f"!! Slack failed ({type(e).__name__}: {e})")
        return False

    print("Slack message sent" if ok else "!! Slack did not accept the message")
    return ok


def notify(subject, body):
    """Send an alert by email and Slack.
    Returns True if at least one channel delivered it (so the alert is not repeated)."""
    email_ok = send_email(subject, body)
    slack_ok = send_slack(f"*{slack_escape(subject)}*\n{slack_escape(body)}")
    return email_ok or slack_ok


def send_run_summary(rows, note=""):
    """If SLACK_EVERY_RUN=true, post one summary message for this run."""
    env = os.environ.get("SLACK_EVERY_RUN", "").strip().lower()
    every_run = (env == "true") if env else SLACK_EVERY_RUN
    if not every_run:
        return
    up_n = sum(1 for _, s, _ in rows if s == UP)
    down_n = sum(1 for _, s, _ in rows if s == DOWN)
    blocked_n = sum(1 for _, s, _ in rows if s == BLOCKED)
    head = "✅" if down_n == 0 else "🚨"
    lines = [f"{head} *Site monitor run* {now_str()}: "
             f"{up_n} up, {down_n} down, {blocked_n} blocked"]
    if note:
        lines.append(f"⚠️ {slack_escape(note)}")
    # Problems first, then the healthy sites
    order = {DOWN: 0, BLOCKED: 1, UP: 2}
    for name, status, reason in sorted(rows, key=lambda r: order[r[1]]):
        lines.append(f"{ICONS[status]} {slack_escape(name)}: {slack_escape(reason)}")
    send_slack("\n".join(lines))   # a failed summary is not retried


# ------------------------------------------------------------------ storage
def load_sites():
    try:
        with open(CONFIG_FILE, encoding="utf-8") as f:
            data = json.load(f)
    except FileNotFoundError:
        sys.exit(f"ERROR: {CONFIG_FILE} not found")
    except json.JSONDecodeError as e:
        sys.exit(f"ERROR: {CONFIG_FILE} is not valid JSON (line {e.lineno}, column {e.colno}): {e.msg}")

    sites, seen = [], set()
    for i, site in enumerate(data.get("sites", []), 1):
        url = (site.get("url") or "").strip()
        if not url:
            print(f"!! Skipping entry #{i} in {CONFIG_FILE}: no url")
            continue
        site["url"] = url
        site["name"] = (site.get("name") or url).strip()
        if site["name"] in seen:
            print(f"!! Duplicate site name '{site['name']}' in {CONFIG_FILE}; skipping the second one")
            continue
        seen.add(site["name"])
        sites.append(site)

    if not sites:
        sys.exit(f"ERROR: no sites found in {CONFIG_FILE}")
    return sites


def load_state():
    try:
        with open(STATE_FILE, encoding="utf-8") as f:
            state = json.load(f)
        return state if isinstance(state, dict) else {}
    except FileNotFoundError:
        return {}
    except json.JSONDecodeError:
        print(f"!! {STATE_FILE} was corrupted; starting with a fresh state")
        return {}


def save_state(state):
    tmp = STATE_FILE + ".tmp"
    with open(tmp, "w", encoding="utf-8") as f:
        json.dump(state, f, indent=2, sort_keys=True, ensure_ascii=False)
        f.write("\n")
    os.replace(tmp, STATE_FILE)


def write_github_summary(rows, note=""):
    path = os.environ.get("GITHUB_STEP_SUMMARY")
    if not path:
        return
    lines = ["## Site monitor results", ""]
    if note:
        lines += [f"> {note}", ""]
    lines += ["| | Site | Details |", "|---|---|---|"]
    for name, status, reason in rows:
        lines.append(f"| {ICONS[status]} | {name} | {reason.replace('|', '/')} |")
    with open(path, "a", encoding="utf-8") as f:
        f.write("\n".join(lines) + "\n")


# --------------------------------------------------------------------- main
def main():
    if os.environ.get("TEST_EMAIL", "").lower() == "true":
        msg = f"Your site monitor notification settings work.\nSent at {now_str()}."
        email_ok = send_email("[Site Monitor] Test email", msg)
        slack_ok = send_slack(f"*[Site Monitor] Test message*\n{msg}")
        print(f"Test result: email={'OK' if email_ok else 'not sent'}, "
              f"slack={'OK' if slack_ok else 'not sent'}")
        sys.exit(0 if (email_ok or slack_ok) else 1)

    sites = load_sites()
    state = load_state()
    alert_failed = False

    # Forget sites that were removed from sites.json
    names = {s["name"] for s in sites}
    for key in [k for k in state if not k.startswith("_") and k not in names]:
        print(f"Removing '{key}' from state (no longer in {CONFIG_FILE})")
        del state[key]

    with ThreadPoolExecutor(max_workers=MAX_WORKERS) as pool:
        results = list(pool.map(check_site, sites))

    rows = []
    for site, status, reason in results:
        print(f"{status:<7} | {site['name']} | {reason}")
        rows.append((site["name"], status, reason))

    # ---- Mass-failure guard: the monitor's own network is the likely problem
    down_count = sum(1 for _, status, _ in results if status == DOWN)
    mass_failure = (len(sites) >= MASS_FAILURE_MIN_SITES
                    and down_count / len(sites) >= MASS_FAILURE_RATIO)

    if mass_failure:
        note = (f"{down_count} of {len(sites)} sites failed at the same time. "
                "Site states were NOT changed this run.")
        print(f"!! {note}")
        if not state.get("_mass_failure_warned"):
            sample = "\n".join(f"- {n}: {r}" for n, s, r in rows if s == DOWN)
            if notify(
                f"[MONITOR WARNING] {down_count} of {len(sites)} sites failed at once",
                f"Detected at {now_str()}\n\n"
                "Most of your sites failed at the same moment. This usually means one of:\n"
                "  1. The monitor's network (GitHub Actions) is blocked or having problems, or\n"
                "  2. A shared hosting provider is having an outage.\n\n"
                "Please open a few of the sites in your browser to confirm.\n"
                "Individual DOWN alerts are paused until this clears.\n\n" + sample):
                state["_mass_failure_warned"] = True
            else:
                alert_failed = True
        write_github_summary(rows, note)
        send_run_summary(rows, note)
        state["_heartbeat"] = today_str()
        save_state(state)
        sys.exit(1 if alert_failed else 0)

    state.pop("_mass_failure_warned", None)

    # ---- Normal run: work out who went down / recovered
    went_down, recovered = [], []   # (name, entry, text)
    notes = []                      # explains every alert decision in the log
    for site, status, reason in results:
        name = site["name"]
        entry = state.get(name)
        if not isinstance(entry, dict):
            entry = {"up": True, "since": now_str(), "fails": 0, "ssl_warned": False}

        blocked_is_down = site.get("blocked_is_down", BLOCKED_IS_DOWN_DEFAULT)
        is_up = status == UP or (status == BLOCKED and not blocked_is_down)

        entry["status"] = status
        entry["reason"] = reason
        if is_up:
            entry["fails"] = 0
            if not entry.get("up", True):
                recovered.append((name, entry,
                    f"- {name} ({site['url']})\n"
                    f"  Was down since {entry.get('since')} ({duration_since(entry.get('since'))})\n"
                    f"  Now: {reason}"))
        else:
            entry["fails"] = entry.get("fails", 0) + 1
            if not entry.get("up", True):
                notes.append(f"{name}: still down (alert already sent at {entry.get('since')}); "
                             "you will get a RECOVERED alert when it is back")
            elif entry["fails"] >= FAIL_THRESHOLD:
                went_down.append((name, entry,
                    f"- {name} ({site['url']})\n  Reason: {reason}"))
            else:
                notes.append(f"{name}: failed {entry['fails']}/{FAIL_THRESHOLD} runs; "
                             "DOWN alert will be sent if it is still down next run")
        state[name] = entry

    print("\n--- Alerts ---")
    for n in notes:
        print(n)
    if not (went_down or recovered):
        print("No DOWN/RECOVERED alert needed this run.")

    if went_down:
        print("Sending DOWN alert for: " + ", ".join(n for n, _, _ in went_down))
        ok = notify(
            f"[DOWN] {len(went_down)} site(s) not responding",
            f"Detected at {now_str()}\n\n" + "\n\n".join(t for _, _, t in went_down) +
            "\n\nYou will get another alert when they recover.")
        if ok:
            for _, entry, _ in went_down:
                entry.update(up=False, since=now_str())
        else:
            alert_failed = True

    if recovered:
        print("Sending RECOVERED alert for: " + ", ".join(n for n, _, _ in recovered))
        ok = notify(
            f"[RECOVERED] {len(recovered)} site(s) back online",
            f"Detected at {now_str()}\n\n" + "\n\n".join(t for _, _, t in recovered))
        if ok:
            for _, entry, _ in recovered:
                entry.update(up=True, since=now_str())
        else:
            alert_failed = True

    # ---- SSL expiry: once a day per site, in parallel
    today = today_str()
    to_check = [s for s, status, _ in results
                if status == UP and s["url"].lower().startswith("https://")
                and state[s["name"]].get("ssl_checked") != today]
    if to_check:
        with ThreadPoolExecutor(max_workers=MAX_WORKERS) as pool:
            days_list = list(pool.map(lambda s: ssl_days_left(s["url"]), to_check))
        ssl_warnings = []
        for site, days in zip(to_check, days_list):
            entry = state[site["name"]]
            if days is None:
                continue
            entry["ssl_checked"] = today
            entry["ssl_days_left"] = days
            if days <= SSL_WARN_DAYS:
                if not entry.get("ssl_warned"):
                    ssl_warnings.append((entry, f"- {site['name']} ({site['url']}): "
                                                f"SSL certificate expires in {days} day(s)"))
            else:
                entry["ssl_warned"] = False
        if ssl_warnings:
            if notify("[SSL WARNING] Certificate(s) expiring soon",
                      "\n".join(t for _, t in ssl_warnings)):
                for entry, _ in ssl_warnings:
                    entry["ssl_warned"] = True
            else:
                alert_failed = True

    up_n = sum(1 for _, s, _ in rows if s == UP)
    blocked_n = sum(1 for _, s, _ in rows if s == BLOCKED)
    print(f"\nSummary: {up_n} up, {down_count} down, {blocked_n} blocked by firewall")

    write_github_summary(rows)
    send_run_summary(rows)
    state["_heartbeat"] = today      # daily commit keeps scheduled workflows active
    save_state(state)
    sys.exit(1 if alert_failed else 0)


if __name__ == "__main__":
    main()
