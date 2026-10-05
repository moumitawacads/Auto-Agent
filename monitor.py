#!/usr/bin/env python3
"""
Website uptime monitor for GitHub Actions.
- Checks every site in sites.json (status code + optional keyword + WordPress error pages)
- Retries before declaring a site down (avoids false alarms)
- Sends ONE combined email when sites go DOWN, and one when they RECOVER
- Warns when an SSL certificate is close to expiry
- Remembers state between runs in state.json (committed back by the workflow)
Uses only the Python standard library.
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
from concurrent.futures import ThreadPoolExecutor
from datetime import datetime, timezone
from email.message import EmailMessage
from urllib.parse import urlparse

CONFIG_FILE = "sites.json"
STATE_FILE = "state.json"
TIMEOUT = 20          # seconds per request
RETRIES = 3           # attempts before a site counts as down
RETRY_DELAY = 20      # seconds between attempts
SSL_WARN_DAYS = 14    # warn when certificate expires within this many days
USER_AGENT = "Mozilla/5.0 (compatible; SiteMonitor/1.0; +https://github.com)"

WP_ERROR_MARKERS = [
    "Error establishing a database connection",
    "There has been a critical error on this website",
    "Briefly unavailable for scheduled maintenance",
]


def now_str():
    return datetime.now(timezone.utc).strftime("%Y-%m-%d %H:%M UTC")


def check_once(site):
    url = site["url"]
    req = urllib.request.Request(url, headers={"User-Agent": USER_AGENT})
    start = time.time()
    try:
        with urllib.request.urlopen(req, timeout=TIMEOUT) as resp:
            code = resp.status
            body = resp.read(500_000).decode("utf-8", errors="ignore")
    except urllib.error.HTTPError as e:
        return False, f"HTTP {e.code} {e.reason}"
    except urllib.error.URLError as e:
        return False, f"Connection failed: {e.reason}"
    except (socket.timeout, TimeoutError):
        return False, f"Timed out after {TIMEOUT}s"
    except Exception as e:
        return False, f"{type(e).__name__}: {e}"

    elapsed = time.time() - start
    for marker in WP_ERROR_MARKERS:
        if marker.lower() in body.lower():
            return False, f"WordPress error page: '{marker}'"

    keyword = site.get("keyword")
    if keyword and keyword.lower() not in body.lower():
        return False, f"HTTP {code}, but expected text '{keyword}' not found on page"

    return True, f"HTTP {code} in {elapsed:.1f}s"


def check_site(site):
    reason = ""
    for attempt in range(1, RETRIES + 1):
        ok, reason = check_once(site)
        if ok:
            return site, True, reason
        if attempt < RETRIES:
            time.sleep(RETRY_DELAY)
    return site, False, reason


def ssl_days_left(url):
    host = urlparse(url).hostname
    if not url.startswith("https://") or not host:
        return None
    try:
        ctx = ssl.create_default_context()
        with socket.create_connection((host, 443), timeout=TIMEOUT) as sock:
            with ctx.wrap_socket(sock, server_hostname=host) as ssock:
                cert = ssock.getpeercert()
        expires = datetime.strptime(cert["notAfter"], "%b %d %H:%M:%S %Y %Z")
        expires = expires.replace(tzinfo=timezone.utc)
        return (expires - datetime.now(timezone.utc)).days
    except Exception:
        return None  # site-down check already covers broken/expired certs


def send_email(subject, body):
    host = os.environ.get("SMTP_HOST")
    port = int(os.environ.get("SMTP_PORT") or 587)
    user = os.environ.get("SMTP_USER")
    password = os.environ.get("SMTP_PASS")
    sender = os.environ.get("MAIL_FROM") or user
    recipients = [a.strip() for a in os.environ.get("ALERT_EMAILS", "").split(",") if a.strip()]

    if not (host and user and password and recipients):
        print("!! Email settings missing (check repository secrets). Not sending.")
        print(subject, "\n", body)
        sys.exit(1)

    msg = EmailMessage()
    msg["Subject"] = subject
    msg["From"] = sender
    msg["To"] = ", ".join(recipients)
    msg.set_content(body)

    if port == 465:
        with smtplib.SMTP_SSL(host, port, context=ssl.create_default_context(), timeout=30) as s:
            s.login(user, password)
            s.send_message(msg)
    else:
        with smtplib.SMTP(host, port, timeout=30) as s:
            s.starttls(context=ssl.create_default_context())
            s.login(user, password)
            s.send_message(msg)
    print(f"Email sent to {len(recipients)} recipient(s): {subject}")
    return True


def load_json(path, default):
    try:
        with open(path, encoding="utf-8") as f:
            return json.load(f)
    except (FileNotFoundError, json.JSONDecodeError):
        return default


def main():
    if os.environ.get("TEST_EMAIL", "").lower() == "true":
        send_email("[Site Monitor] Test email",
                   f"Your site monitor email settings work.\nSent at {now_str()}.")
        return

    sites = load_json(CONFIG_FILE, {}).get("sites", [])
    if not sites:
        print("No sites found in sites.json")
        sys.exit(1)

    state = load_json(STATE_FILE, {})
    went_down, recovered, ssl_warnings = [], [], []

    with ThreadPoolExecutor(max_workers=10) as pool:
        results = list(pool.map(check_site, sites))

    for site, ok, reason in results:
        name = site.get("name") or site["url"]
        prev = state.get(name, {"up": True, "since": now_str(), "ssl_warned": False})
        print(f"{'UP  ' if ok else 'DOWN'} | {name} | {reason}")

        if ok and not prev["up"]:
            recovered.append(f"- {name} ({site['url']})\n  Was down since {prev['since']}")
            prev.update(up=True, since=now_str(), reason=reason)
        elif not ok and prev["up"]:
            went_down.append(f"- {name} ({site['url']})\n  Reason: {reason}")
            prev.update(up=False, since=now_str(), reason=reason)
        else:
            prev["reason"] = reason

        if ok:
            days = ssl_days_left(site["url"])
            if days is not None and days <= SSL_WARN_DAYS:
                if not prev.get("ssl_warned"):
                    ssl_warnings.append(f"- {name}: SSL certificate expires in {days} day(s)")
                    prev["ssl_warned"] = True
            elif days is not None:
                prev["ssl_warned"] = False

        state[name] = prev

    if went_down:
        send_email(f"[DOWN] {len(went_down)} site(s) not responding",
                   f"Detected at {now_str()}\n\n" + "\n\n".join(went_down) +
                   "\n\nYou will get another email when they recover.")
    if recovered:
        send_email(f"[RECOVERED] {len(recovered)} site(s) back online",
                   f"Detected at {now_str()}\n\n" + "\n\n".join(recovered))
    if ssl_warnings:
        send_email("[SSL WARNING] Certificate(s) expiring soon",
                   "\n".join(ssl_warnings))

    # Daily heartbeat so the repo shows regular activity
    state["_heartbeat"] = datetime.now(timezone.utc).strftime("%Y-%m-%d")

    with open(STATE_FILE, "w", encoding="utf-8") as f:
        json.dump(state, f, indent=2, sort_keys=True)


if __name__ == "__main__":
    main()
