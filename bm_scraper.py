#!/usr/bin/env python3
"""
BrighterMonday (Kenya) job scraper v3 - Termux optimized.

  * Quick scrape with saved default values (one tap from the menu)
  * Custom scrape with prompts, plus "edit & save defaults"
  * Smart URL building (category/location/type) with automatic fallbacks
  * SQLite database: jobs already stored are skipped next time
  * Scan modes: "new jobs only" (default) or "full scan"
  * Colored terminal output (auto-disabled when piped; --no-color to force off)

Setup (Termux):
    pkg update && pkg install python -y
    pip install requests beautifulsoup4
    termux-setup-storage        # optional: lets it export to Downloads

Run:
    python bm_scraper.py                       # interactive menu
    python bm_scraper.py --quick               # scrape with saved defaults
    python bm_scraper.py -k waiter -l nairobi  # direct, no prompts
    python bm_scraper.py -c customer-service -l nairobi -t full-time -p 3
    python bm_scraper.py -k python -p 5 --full -d -i python django
    python bm_scraper.py --stats | --export-db | --help
"""

import argparse
import copy
import csv
import json
import os
import random
import re
import shutil
import sqlite3
import subprocess
import sys
import time
from datetime import datetime
from urllib.parse import parse_qs, urlencode, urljoin, urlparse, urlunparse

import requests
from bs4 import BeautifulSoup
from requests.adapters import HTTPAdapter
from urllib3.util.retry import Retry

# ----------------------------------------------------------------------
# DEFAULT OPTIONS  (used by "Quick scrape"; override via menu option 3,
# the command line, or by editing here)
# ----------------------------------------------------------------------
CONFIG = {
    "keyword": "",          # search term, e.g. "waiter"
    "category": "",         # category slug, e.g. "customer-service"
    "location": "",         # location slug, e.g. "nairobi"
    "work_type": "",        # work type slug, e.g. "full-time", "part-time"
    "url": "",              # full custom search URL (overrides the four above)
    "start_page": 1,
    "max_pages": 5,
    "limit": 0,             # stop after N kept jobs (0 = no limit)
    "delay_min": 2.0,       # polite delay between requests (seconds)
    "delay_max": 4.5,
    "details": False,       # open each NEW job page and read its description
    "include": [],          # keep only jobs containing ANY of these (card + description)
    "exclude": [],          # drop jobs whose title/company/category contain ANY of these
    "formats": ["csv", "json"],   # csv, json, txt
    "outdir": "",           # blank = ~/storage/downloads if present, else cwd
    "full": False,          # True = full scan by default
    "stop_known": 0,        # new-only mode: stop after N pages in a row with nothing new (0 = never)
    # --- not saved as "defaults" ---
    "db": "~/.bm_scraper/jobs.db",
    "timeout": 25,
    "quiet": False,
    "verbose": False,
}

# Options remembered in settings.json by "Edit & save defaults"
SETTING_KEYS = [
    "keyword", "category", "location", "work_type", "url", "start_page",
    "max_pages", "limit", "delay_min", "delay_max", "details", "include",
    "exclude", "formats", "outdir", "full", "stop_known",
]

APP_DIR = os.path.expanduser("~/.bm_scraper")
SETTINGS_PATH = os.path.join(APP_DIR, "settings.json")

BASE = "https://www.brightermonday.co.ke"

# Slugs seen in real BrighterMonday URLs (copy others from the site's address bar)
KNOWN_CATEGORIES = [
    "customer-service", "healthcare", "food-services-catering",
    "hospitality-hotel", "banking-finance-insurance", "recruitment",
]
KNOWN_WORK_TYPES = ["full-time", "part-time"]

USER_AGENTS = [
    "Mozilla/5.0 (Linux; Android 13; Pixel 7) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/124.0.0.0 Mobile Safari/537.36",
    "Mozilla/5.0 (Linux; Android 12; SM-A525F) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/123.0.0.0 Mobile Safari/537.36",
    "Mozilla/5.0 (Linux; Android 14; Infinix X6711) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/125.0.0.0 Mobile Safari/537.36",
]

JOB_TYPE_RE = re.compile(
    r"^(full[\s-]?time|part[\s-]?time|contract|internship|temporary|freelance|volunteer|remote|hybrid)",
    re.I,
)
SALARY_RE = re.compile(r"(ksh|kes|usd|\$)\s?[\d,]+", re.I)
POSTED_RE = re.compile(r"\b(ago|today|yesterday|just now)\b", re.I)

FIELDS = [
    "title", "company", "location", "job_type", "salary", "category",
    "posted", "is_new", "first_seen", "url", "description",
]


# ----------------------------------------------------------------------
# Colors
# ----------------------------------------------------------------------
STYLE = {
    "bold": "1", "dim": "2", "red": "31", "green": "32", "yellow": "33",
    "blue": "34", "magenta": "35", "cyan": "36", "white": "37", "gray": "90",
    "bred": "91", "bgreen": "92", "byellow": "93", "bblue": "94",
    "bmagenta": "95", "bcyan": "96",
}
COLOR_ON = False
ANSI_RE = re.compile(r"\033\[[0-9;]*m")


def init_color(force_off=False):
    global COLOR_ON
    COLOR_ON = (
        not force_off
        and sys.stdout.isatty()
        and "NO_COLOR" not in os.environ
        and os.environ.get("TERM") != "dumb"
    )


def paint(text, *styles):
    text = str(text)
    if not COLOR_ON or not styles:
        return text
    return "\033[" + ";".join(STYLE[s] for s in styles) + "m" + text + "\033[0m"


def ok(t):
    return paint(t, "bgreen")


def warn(t):
    return paint(t, "byellow")


def bad(t):
    return paint(t, "bred")


def dim(t):
    return paint(t, "gray")


def head(t):
    return paint(t, "bcyan", "bold")


def strip_ansi(s):
    return ANSI_RE.sub("", s)


def read(prompt):
    """input() that keeps readline happy when the prompt contains colors."""
    return input(re.sub(r"(\033\[[0-9;]*m)", "\001\\1\002", prompt))


def box(title, lines, color="bcyan"):
    inner = max([len(strip_ansi(x)) for x in lines] + [len(title) + 4]) + 1
    top = paint("┌" + ("─ " + title + " ").ljust(inner, "─") + "┐", color)
    out = [top]
    for x in lines:
        pad = " " * (inner - 1 - len(strip_ansi(x)))
        out.append(paint("│", color) + " " + x + pad + paint("│", color))
    out.append(paint("└" + "─" * inner + "┘", color))
    return "\n".join(out)


def progress_bar(done, total, width=18):
    total = max(total, 1)
    n = int(width * done / total)
    return paint("█" * n, "bgreen") + paint("░" * (width - n), "gray")


def banner():
    print(paint("╭──────────────────────────────────╮", "bcyan"))
    print(paint("│", "bcyan") + paint("   BrighterMonday Job Scraper v3  ", "bold", "white") + paint("│", "bcyan"))
    print(paint("╰──────────────────────────────────╯", "bcyan"))


# ----------------------------------------------------------------------
# Small helpers
# ----------------------------------------------------------------------
def log(msg, args):
    if not args.quiet:
        print(msg, flush=True)


def now_str():
    return datetime.now().strftime("%Y-%m-%d %H:%M:%S")


def make_session():
    s = requests.Session()
    retry = Retry(
        total=3,
        backoff_factor=1.5,
        status_forcelist=(500, 502, 503, 504),
        allowed_methods=("GET",),
    )
    s.mount("https://", HTTPAdapter(max_retries=retry))
    s.headers.update({
        "User-Agent": random.choice(USER_AGENTS),
        "Accept": "text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8",
        "Accept-Language": "en-US,en;q=0.9",
        "Referer": BASE + "/",
    })
    return s


def get_page(session, url, args):
    """GET a URL -> (status_code, text). status is None on network errors."""
    try:
        r = session.get(url, timeout=args.timeout)
    except requests.RequestException as e:
        return None, str(e)
    return r.status_code, r.text


def explain_status(status, text):
    if status is None:
        return bad(f"  ✖ network error: {text[:120]}")
    if status in (404, 410):
        return dim(f"  ↳ page gone ({status}) - end of results")
    if status in (403, 429):
        return bad(f"  ✖ blocked/rate-limited ({status}). Try bigger delays or wait a while.")
    return bad(f"  ✖ HTTP {status}")


def fetch(session, url, args):
    """Detail-page fetch: returns HTML or None."""
    status, text = get_page(session, url, args)
    if status == 200:
        return text
    log(explain_status(status, text), args)
    return None


# ----------------------------------------------------------------------
# URL building (with fallbacks)
# ----------------------------------------------------------------------
def slugify(s):
    return re.sub(r"[^a-z0-9]+", "-", s.lower()).strip("-")


def build_url(args, page, mode="exact"):
    """
    BrighterMonday path order is /jobs/<category>/<location>/<work-type>
    (every part optional), with ?q=<keyword>&page=<n>.

    mode "exact"   : use every field as given
    mode "cat_kw"  : category slug was rejected -> treat it as a keyword
    mode "kw_only" : last resort, plain keyword search (no location/type path)
    """
    if args.url:
        parts = urlparse(args.url)
        q = parse_qs(parts.query)
        q["page"] = [str(page)]
        return urlunparse(parts._replace(query=urlencode(q, doseq=True)))

    kw = args.keyword
    if mode == "exact":
        segs = [args.category, args.location, args.work_type]
    elif mode == "cat_kw":
        segs = [args.location, args.work_type]
        kw = kw or args.category.replace("-", " ")
    else:
        segs = []
        kw = kw or args.category.replace("-", " ")

    path = "/jobs" + "".join("/" + slugify(s) for s in segs if s)
    q = {}
    if kw:
        q["q"] = kw
    q["page"] = page
    return f"{BASE}{path}?{urlencode(q)}"


def search_modes(args):
    if args.url:
        return [("custom URL", "exact")]
    modes = [("exact filters", "exact")]
    if args.category:
        modes.append(("category treated as keyword", "cat_kw"))
    if args.keyword or args.category:
        if args.location or args.work_type:
            modes.append(("keyword only (location/type dropped)", "kw_only"))
    return modes


def resolve_search(session, args):
    """Find a URL pattern that the site accepts; returns dict or None."""
    first = args.start_page
    for name, mode in search_modes(args):
        url = build_url(args, first, mode)
        status, text = get_page(session, url, args)
        if status == 200:
            if mode != "exact":
                print(warn(f"  ⚠ fallback used: {name}"))
            return {"mode": mode, "url": url, "html": text}
        if status in (404, 410):
            print(warn(f"  ⚠ {status} for {url}"))
            if (name, mode) != search_modes(args)[-1]:
                print(dim("    trying a fallback..."))
            continue
        print(explain_status(status, text))
        return None
    print(bad("  ✖ No working search URL. Check the category/location slug, or paste a URL from the site."))
    return None


def query_label(args):
    if args.url:
        return args.url
    parts = (args.keyword, args.category, args.location, args.work_type)
    return "|".join(x for x in parts if x) or "all"


def describe_args(args):
    if args.url:
        what = "custom URL"
    else:
        bits = []
        if args.keyword:
            bits.append(f"keyword={args.keyword}")
        if args.category:
            bits.append(f"category={args.category}")
        if args.location:
            bits.append(f"location={args.location}")
        if args.work_type:
            bits.append(f"type={args.work_type}")
        what = ", ".join(bits) or "all jobs"
    last = args.start_page + args.max_pages - 1
    mode = "full scan" if args.full else "new only"
    extra = ", descriptions" if args.details else ""
    return f"{what} | pages {args.start_page}-{last} | {mode}{extra}"


def clean_link(base, href):
    return urljoin(base, href.split("?")[0].split("#")[0])


# ----------------------------------------------------------------------
# Parsing
# ----------------------------------------------------------------------
def parse_listings(html, base=BASE):
    """
    Layout-tolerant parser: finds every link to /listings/..., walks up to the
    smallest container holding exactly ONE listing, then classifies its text.
    """
    soup = BeautifulSoup(html, "html.parser")
    by_href = {}
    for a in soup.select('a[href*="/listings/"]'):
        by_href.setdefault(clean_link(base, a["href"]), []).append(a)

    jobs = []
    for href, anchors in by_href.items():
        container = anchors[0]
        for _ in range(6):
            parent = container.parent
            if parent is None or parent.name in ("body", "html"):
                break
            hrefs = {
                clean_link(base, x["href"])
                for x in parent.select('a[href*="/listings/"]')
            }
            if len(hrefs) > 1:
                break
            container = parent

        seen, pieces = set(), []
        for p in container.stripped_strings:
            if p not in seen:
                seen.add(p)
                pieces.append(p)

        title = next(
            (a.get_text(" ", strip=True) for a in anchors if a.get_text(strip=True)),
            pieces[0] if pieces else "",
        )

        job = dict.fromkeys(FIELDS, "")
        job["title"], job["url"] = title, href
        leftovers = []
        for p in pieces:
            if p == title:
                continue
            if p.lower() == "new":
                job["is_new"] = "yes"
            elif not job["salary"] and (SALARY_RE.search(p) or p.lower() == "confidential"):
                job["salary"] = p
            elif not job["job_type"] and JOB_TYPE_RE.match(p):
                job["job_type"] = p
            elif not job["posted"] and POSTED_RE.search(p) and len(p) < 40:
                job["posted"] = p
            elif len(p) < 90:
                leftovers.append(p)
        if leftovers:
            job["company"] = leftovers[0]
        if len(leftovers) > 1:
            job["location"] = leftovers[1]
        if len(leftovers) > 2:
            job["category"] = " | ".join(leftovers[2:])
        if job["title"]:
            jobs.append(job)
    return jobs


def parse_description(html, limit=2000):
    soup = BeautifulSoup(html, "html.parser")
    for t in soup(["script", "style", "nav", "footer", "header", "noscript"]):
        t.decompose()
    node = soup.find("main") or soup.body or soup
    text = re.sub(r"\s+", " ", node.get_text(" ", strip=True))
    return text[:limit]


def is_excluded(job, args):
    """Exclude words are checked against title/company/category only."""
    if not args.exclude:
        return False
    blob = f"{job['title']} {job['company']} {job['category']}".lower()
    return any(w.lower() in blob for w in args.exclude)


def is_included(job, args):
    """Include words are checked against the card text AND description."""
    if not args.include:
        return True
    blob = " ".join(str(job[k]) for k in FIELDS).lower()
    return any(w.lower() in blob for w in args.include)


def fmt_job(job, marker, mcolor):
    sal = job["salary"]
    if sal and sal.lower() != "confidential":
        sal_s = paint(sal, "bgreen")
    else:
        sal_s = dim(sal or "-")
    badge = " " + paint(" NEW ", "bold", "green") if job["is_new"] else ""
    sep = dim("·")
    l1 = f"  {paint(marker, mcolor, 'bold')} {paint(job['title'], 'bold', 'white')}{badge}"
    l2 = (f"      {paint(job['company'] or '-', 'bcyan')} {sep} {job['location'] or '-'} "
          f"{sep} {sal_s} {sep} {dim(job['posted'] or '-')}")
    return l1 + "\n" + l2


# ----------------------------------------------------------------------
# Settings (saved defaults)
# ----------------------------------------------------------------------
def load_settings():
    try:
        with open(SETTINGS_PATH, encoding="utf-8") as f:
            data = json.load(f)
    except (OSError, ValueError):
        return {}
    good = {}
    for k, v in data.items():
        if k in SETTING_KEYS and type(v) is type(CONFIG[k]):
            good[k] = v
        elif k in SETTING_KEYS and isinstance(CONFIG[k], float) and isinstance(v, int):
            good[k] = float(v)
    return good


def save_settings(args):
    os.makedirs(APP_DIR, exist_ok=True)
    data = {k: getattr(args, k) for k in SETTING_KEYS}
    with open(SETTINGS_PATH, "w", encoding="utf-8") as f:
        json.dump(data, f, indent=2)
    CONFIG.update(copy.deepcopy(data))


def apply_defaults(args):
    """Reset the scrape options on args to the saved/default values."""
    for k in SETTING_KEYS:
        setattr(args, k, copy.deepcopy(CONFIG[k]))
    return args


# ----------------------------------------------------------------------
# Database
# ----------------------------------------------------------------------
def db_open(path):
    path = os.path.expanduser(path)
    os.makedirs(os.path.dirname(path) or ".", exist_ok=True)
    conn = sqlite3.connect(path)
    conn.row_factory = sqlite3.Row
    conn.execute("""
        CREATE TABLE IF NOT EXISTS jobs (
            url TEXT PRIMARY KEY,
            title TEXT, company TEXT, location TEXT, job_type TEXT,
            salary TEXT, category TEXT, posted TEXT, is_new TEXT,
            description TEXT DEFAULT '',
            kept INTEGER DEFAULT 1,
            query TEXT,
            first_seen TEXT, last_seen TEXT,
            times_seen INTEGER DEFAULT 1
        )
    """)
    conn.commit()
    return conn


def db_count(conn):
    return conn.execute("SELECT COUNT(*) FROM jobs").fetchone()[0]


def db_known_urls(conn):
    return {r[0] for r in conn.execute("SELECT url FROM jobs")}


def db_upsert(conn, job, kept, query):
    ts = now_str()
    conn.execute("""
        INSERT INTO jobs (url, title, company, location, job_type, salary,
                          category, posted, is_new, description, kept, query,
                          first_seen, last_seen, times_seen)
        VALUES (?,?,?,?,?,?,?,?,?,?,?,?,?,?,1)
        ON CONFLICT(url) DO UPDATE SET
            title=excluded.title, company=excluded.company,
            location=excluded.location, job_type=excluded.job_type,
            salary=excluded.salary, category=excluded.category,
            posted=excluded.posted, is_new=excluded.is_new,
            description=CASE WHEN excluded.description<>''
                             THEN excluded.description ELSE jobs.description END,
            kept=excluded.kept, last_seen=excluded.last_seen,
            times_seen=jobs.times_seen+1
    """, (job["url"], job["title"], job["company"], job["location"],
          job["job_type"], job["salary"], job["category"], job["posted"],
          job["is_new"], job["description"], 1 if kept else 0, query, ts, ts))
    job["first_seen"] = job["first_seen"] or ts


def db_touch(conn, url):
    conn.execute(
        "UPDATE jobs SET last_seen=?, times_seen=times_seen+1 WHERE url=?",
        (now_str(), url),
    )


def db_all_kept(conn):
    rows = conn.execute("SELECT * FROM jobs WHERE kept=1 ORDER BY first_seen DESC").fetchall()
    return [{k: (r[k] if r[k] is not None else "") for k in FIELDS} for r in rows]


def db_search(conn, term, limit=15):
    like = f"%{term}%"
    rows = conn.execute(
        "SELECT * FROM jobs WHERE kept=1 AND (title LIKE ? OR company LIKE ? "
        "OR category LIKE ? OR description LIKE ?) ORDER BY first_seen DESC LIMIT ?",
        (like, like, like, like, limit),
    ).fetchall()
    return [{k: (r[k] if r[k] is not None else "") for k in FIELDS} for r in rows]


def db_stats(conn):
    total = db_count(conn)
    kept = conn.execute("SELECT COUNT(*) FROM jobs WHERE kept=1").fetchone()[0]
    first = conn.execute("SELECT MIN(first_seen) FROM jobs").fetchone()[0]
    last = conn.execute("SELECT MAX(last_seen) FROM jobs").fetchone()[0]
    cats = conn.execute(
        "SELECT category, COUNT(*) c FROM jobs WHERE kept=1 AND category<>'' "
        "GROUP BY category ORDER BY c DESC LIMIT 5"
    ).fetchall()
    lines = [
        f"Jobs seen     {paint(total, 'bold')}",
        f"Kept          {ok(kept)}",
        f"Filtered out  {warn(total - kept)}",
        f"First scrape  {dim(first or '-')}",
        f"Last seen     {dim(last or '-')}",
    ]
    if cats:
        lines.append("")
        lines.append(paint("Top categories", "bold"))
        top = max(r["c"] for r in cats)
        for r in cats:
            lines.append(f"{progress_bar(r['c'], top, 10)} {r['c']:>3}  {r['category']}")
    print("\n" + box("Database", lines))


# ----------------------------------------------------------------------
# Output files
# ----------------------------------------------------------------------
def out_dir(args):
    if args.outdir:
        d = os.path.expanduser(args.outdir)
    else:
        dl = os.path.expanduser("~/storage/downloads")
        d = dl if os.path.isdir(dl) else os.getcwd()
    os.makedirs(d, exist_ok=True)
    return d


def save(jobs, args, tag):
    if not jobs:
        print(dim("Nothing to export."))
        return
    stamp = datetime.now().strftime("%Y%m%d_%H%M%S")
    slug = re.sub(r"[^a-z0-9]+", "-", (args.keyword or args.category or "all").lower()).strip("-")
    base = os.path.join(out_dir(args), f"brightermonday_{tag}_{slug}_{stamp}")
    for fmt in args.formats:
        path = f"{base}.{fmt}"
        if fmt == "csv":
            with open(path, "w", newline="", encoding="utf-8-sig") as f:
                w = csv.DictWriter(f, fieldnames=FIELDS, extrasaction="ignore")
                w.writeheader()
                w.writerows(jobs)
        elif fmt == "json":
            with open(path, "w", encoding="utf-8") as f:
                json.dump([{k: j.get(k, "") for k in FIELDS} for j in jobs],
                          f, ensure_ascii=False, indent=2)
        elif fmt == "txt":
            with open(path, "w", encoding="utf-8") as f:
                for j in jobs:
                    f.write(f"{j['title']}\n  {j['company']} | {j['location']} | {j['category']}\n")
                    f.write(f"  {j['job_type']} | {j['salary']} | {j['posted']}\n  {j['url']}\n\n")
        else:
            continue
        print(f"{ok('💾 Saved')} {path}")


# ----------------------------------------------------------------------
# Scraping
# ----------------------------------------------------------------------
def run_scrape(args, conn):
    session = make_session()
    known = db_known_urls(conn)
    label = query_label(args)
    end_page = args.start_page + args.max_pages - 1
    mode_tag = paint(" FULL SCAN ", "bold", "yellow") if args.full else paint(" NEW ONLY ", "bold", "green")

    print(f"\n{head('▶ Scan started')} {mode_tag} {dim(f'database holds {len(known)} jobs')}")
    print(dim("  " + describe_args(args)))

    plan = resolve_search(session, args)
    if not plan:
        return

    results, seen_run = [], set()
    skipped = rejected = quiet_pages = pages_done = 0
    t0 = time.time()

    try:
        for page in range(args.start_page, end_page + 1):
            if page == args.start_page:
                url, html = plan["url"], plan["html"]
            else:
                url = build_url(args, page, plan["mode"])
                status, html = get_page(session, url, args)
                if status != 200:
                    print(explain_status(status, html))
                    break

            done = page - args.start_page + 1
            print(f"\n{head(f'Page {page}')} {dim(f'({done}/{args.max_pages})')} "
                  f"{progress_bar(done, args.max_pages)}")
            print(dim("  " + url))

            found = parse_listings(html)
            fresh = [j for j in found if j["url"] not in seen_run]
            if not found:
                if re.search(r"\b0 Jobs Found\b", html, re.I):
                    print(warn("  ⚠ 0 jobs found for these filters."))
                else:
                    print(warn("  ⚠ no listings found - end of results or the site layout changed."))
                break
            if not fresh:
                print(dim("  only duplicates - stopping"))
                break
            pages_done += 1

            unknown_on_page = kept_on_page = 0
            for job in fresh:
                seen_run.add(job["url"])
                was_known = job["url"] in known
                if not was_known:
                    unknown_on_page += 1

                # Already in the database and not a full scan -> skip entirely
                if was_known and not args.full:
                    db_touch(conn, job["url"])
                    skipped += 1
                    if args.verbose:
                        print(dim(f"  = known: {job['title']}"))
                    continue

                if is_excluded(job, args):
                    db_upsert(conn, job, False, label)
                    known.add(job["url"])
                    rejected += 1
                    if args.verbose:
                        print(paint(f"  ✖ excluded: {job['title']}", "red", "dim"))
                    continue

                if args.details:
                    time.sleep(random.uniform(args.delay_min, args.delay_max))
                    d_html = fetch(session, job["url"], args)
                    if d_html:
                        job["description"] = parse_description(d_html)

                if not is_included(job, args):
                    db_upsert(conn, job, False, label)
                    known.add(job["url"])
                    rejected += 1
                    if args.verbose:
                        print(paint(f"  ✖ no include match: {job['title']}", "red", "dim"))
                    continue

                db_upsert(conn, job, True, label)
                known.add(job["url"])
                results.append(job)
                kept_on_page += 1
                if was_known:
                    print(fmt_job(job, "↻", "byellow"))
                else:
                    print(fmt_job(job, "✚", "bgreen"))
                if args.limit and len(results) >= args.limit:
                    break

            conn.commit()
            print(dim(f"  page result: ") + f"{ok(kept_on_page)} kept " + dim("|") +
                  f" {skipped} known " + dim("|") + f" {rejected} filtered")

            if args.limit and len(results) >= args.limit:
                print(warn("  limit reached"))
                break

            if not args.full and args.stop_known:
                quiet_pages = quiet_pages + 1 if unknown_on_page == 0 else 0
                if quiet_pages >= args.stop_known:
                    print(warn(f"  {quiet_pages} page(s) in a row with nothing new - stopping early"))
                    break

            if page < end_page:
                time.sleep(random.uniform(args.delay_min, args.delay_max))
    except KeyboardInterrupt:
        print(warn("\n⏹ Interrupted - saving what we have..."))

    conn.commit()
    secs = int(time.time() - t0)
    label_kept = "Jobs kept" if args.full else "NEW jobs"
    lines = [
        f"{label_kept:<14}{ok(len(results)) if results else dim(0)}",
        f"{'Already known':<14}{skipped}",
        f"{'Filtered out':<14}{warn(rejected) if rejected else dim(0)}",
        f"{'Pages scanned':<14}{pages_done}",
        f"{'Time':<14}{dim(f'{secs}s')}",
    ]
    print("\n" + box("Scan complete", lines, "bgreen" if results else "byellow"))
    save(results, args, "full" if args.full else "new")


# ----------------------------------------------------------------------
# Interactive prompts
# ----------------------------------------------------------------------
def ask(label, default="", cast=str, hint=""):
    shown = f" {paint('[' + str(default) + ']', 'cyan')}" if default not in ("", None) else ""
    h = f" {dim(hint)}" if hint else ""
    while True:
        raw = read(f"{paint('›', 'byellow', 'bold')} {label}{h}{shown}: ").strip()
        if not raw:
            return default
        if raw == "-":
            return "" if cast is str else cast(0)
        try:
            return cast(raw)
        except ValueError:
            print(bad("  invalid value, try again"))


def ask_yn(label, default):
    d = "Y/n" if default else "y/N"
    while True:
        raw = read(f"{paint('›', 'byellow', 'bold')} {label} {paint('[' + d + ']', 'cyan')}: ").strip().lower()
        if not raw:
            return default
        if raw in ("y", "yes"):
            return True
        if raw in ("n", "no"):
            return False


def ask_words(label, default):
    shown = f" {paint('[' + ', '.join(default) + ']', 'cyan')}" if default else ""
    raw = read(f"{paint('›', 'byellow', 'bold')} {label} {dim('(comma-separated, - = none)')}{shown}: ").strip()
    if not raw:
        return list(default)
    if raw == "-":
        return []
    return [w.strip() for w in raw.split(",") if w.strip()]


def ask_formats(default):
    while True:
        raw = read(f"{paint('›', 'byellow', 'bold')} Export formats {dim('(csv, json, txt)')} "
                   f"{paint('[' + ', '.join(default) + ']', 'cyan')}: ").strip().lower()
        if not raw:
            return list(default)
        fm = [w.strip() for w in raw.split(",") if w.strip()]
        if fm and all(f in ("csv", "json", "txt") for f in fm):
            return fm
        print(bad("  choose from csv, json, txt"))


def prompt_scrape_options(args, conn, defaults_mode=False):
    title = "Edit default values" if defaults_mode else "Custom scrape"
    print("\n" + head(f"── {title} ──") + dim("  Enter = keep [value], - = clear"))
    args.url = ask("Paste a BrighterMonday search URL", args.url, hint="(optional)")
    if args.url:
        args.keyword = args.category = args.location = args.work_type = ""
    else:
        args.keyword = ask("Keyword", args.keyword, hint="e.g. waiter")
        args.category = ask("Category slug", args.category, hint="e.g. " + ", ".join(KNOWN_CATEGORIES[:3]))
        if args.category and args.category not in KNOWN_CATEGORIES:
            print(dim("  not a slug I know - if the site rejects it, I'll search it as a keyword"))
        args.location = ask("Location slug", args.location, hint="e.g. nairobi")
        args.work_type = ask("Work type slug", args.work_type, hint="full-time / part-time")
    args.start_page = ask("Start page", args.start_page, int)
    args.max_pages = ask("Number of pages", args.max_pages, int)
    args.limit = ask("Stop after N kept jobs", args.limit, int, hint="(0 = no limit)")
    args.details = ask_yn("Read each job's description? (slower, enables description matching)", args.details)
    args.include = ask_words("Include words (match ANY)", args.include)
    args.exclude = ask_words("Exclude words (title/company/category)", args.exclude)
    args.formats = ask_formats(args.formats)

    print(f"\n{paint('Scan mode', 'bold')} {dim(f'(database holds {db_count(conn)} jobs)')}")
    print(f"  {paint('1', 'bgreen')}) New jobs only - skip anything already in the database")
    print(f"  {paint('2', 'byellow')}) Full scan     - re-check everything and refresh the database")
    choice = ask("Choose", 2 if args.full else 1, int)
    args.full = (choice == 2)
    if args.full:
        print(dim("  tip: use a full scan after changing keywords/filters"))
    else:
        args.stop_known = ask("Stop early after N pages with nothing new", args.stop_known, int, hint="(0 = never)")
    return args


def open_in_browser(url):
    opener = shutil.which("termux-open-url") or shutil.which("xdg-open")
    if opener:
        subprocess.run([opener, url], check=False)
    else:
        print(dim("  no opener found - copy this link: ") + url)


def browse_jobs(conn):
    term = read(f"{paint('›', 'byellow', 'bold')} Filter {dim('(title/company/category/description, Enter = latest)')}: ").strip()
    rows = db_search(conn, term, 15)
    if not rows:
        print(warn("No matching jobs in the database."))
        return
    print()
    for i, j in enumerate(rows, 1):
        print(f"{paint(f'{i:>2}.', 'byellow')}" + fmt_job(j, " ", "white")[3:])
    pick = read(f"\n{paint('›', 'byellow', 'bold')} Open which number in the browser? {dim('(Enter = back)')}: ").strip()
    if pick.isdigit() and 1 <= int(pick) <= len(rows):
        open_in_browser(rows[int(pick) - 1]["url"])


def interactive(args, conn):
    banner()
    while True:
        defaults = apply_defaults(copy.copy(args))
        print("\n" + box("Saved defaults", [dim(describe_args(defaults)),
                                            dim(f"database: {db_count(conn)} jobs")]))
        print(f" {paint('1', 'bgreen', 'bold')}) Quick scrape        {dim('(use saved defaults)')}")
        print(f" {paint('2', 'bcyan', 'bold')}) Custom scrape       {dim('(answer prompts)')}")
        print(f" {paint('3', 'byellow', 'bold')}) Edit & save defaults")
        print(f" {paint('4', 'bmagenta', 'bold')}) Browse saved jobs   {dim('(search / open link)')}")
        print(f" {paint('5', 'bblue', 'bold')}) Export whole database")
        print(f" {paint('6', 'bblue', 'bold')}) Database stats")
        print(f" {paint('7', 'bred', 'bold')}) Clear database")
        print(f" {paint('0', 'gray', 'bold')}) Quit")
        choice = read(f"{paint('Choose', 'bold')}: ").strip()
        if choice == "1":
            run_scrape(defaults, conn)
        elif choice == "2":
            run_scrape(prompt_scrape_options(defaults, conn), conn)
            if ask_yn("Save these options as your new defaults?", False):
                save_settings(args_from(defaults, args))
                print(ok("✔ Defaults saved."))
        elif choice == "3":
            edited = prompt_scrape_options(defaults, conn, defaults_mode=True)
            save_settings(edited)
            print(ok("✔ Defaults saved to ") + dim(SETTINGS_PATH))
        elif choice == "4":
            browse_jobs(conn)
        elif choice == "5":
            args.formats = ask_formats(args.formats)
            save(db_all_kept(conn), args, "database")
        elif choice == "6":
            db_stats(conn)
        elif choice == "7":
            if read(f"{bad('Type yes to delete ALL stored jobs')}: ").strip().lower() == "yes":
                conn.execute("DELETE FROM jobs")
                conn.commit()
                print(ok("Database cleared."))
        elif choice in ("0", "q", ""):
            print(dim("Bye."))
            break


def args_from(src, base):
    """Copy the scrape options from src onto base (used for saving)."""
    for k in SETTING_KEYS:
        setattr(base, k, copy.deepcopy(getattr(src, k)))
    return base


# ----------------------------------------------------------------------
# Command line
# ----------------------------------------------------------------------
def get_args():
    c = CONFIG
    p = argparse.ArgumentParser(description="BrighterMonday Kenya job scraper (Termux friendly)")
    p.add_argument("-k", "--keyword", default=c["keyword"], help="search keyword")
    p.add_argument("-c", "--category", default=c["category"], help="category slug, e.g. customer-service")
    p.add_argument("-l", "--location", default=c["location"], help="location slug, e.g. nairobi")
    p.add_argument("-t", "--work-type", default=c["work_type"], help="work type slug, e.g. full-time")
    p.add_argument("--url", default=c["url"], help="full custom search URL (overrides -k/-c/-l/-t)")
    p.add_argument("-s", "--start", dest="start_page", type=int, default=c["start_page"], help="first page")
    p.add_argument("-p", "--pages", dest="max_pages", type=int, default=c["max_pages"], help="number of pages")
    p.add_argument("-n", "--limit", type=int, default=c["limit"], help="stop after N kept jobs (0 = no limit)")
    p.add_argument("--delay-min", type=float, default=c["delay_min"])
    p.add_argument("--delay-max", type=float, default=c["delay_max"])
    p.add_argument("-d", "--details", action="store_true", default=c["details"], help="read each job's description")
    p.add_argument("-i", "--include", nargs="*", default=c["include"], help="keep jobs containing any of these words")
    p.add_argument("-x", "--exclude", nargs="*", default=c["exclude"], help="drop jobs whose title/company/category contain these")
    p.add_argument("-f", "--formats", nargs="+", default=c["formats"], choices=["csv", "json", "txt"])
    p.add_argument("-o", "--outdir", default=c["outdir"], help="export folder")
    p.add_argument("--db", default=c["db"], help="database path")
    p.add_argument("--full", action="store_true", default=c["full"], help="full scan: re-check jobs already in the database")
    p.add_argument("--stop-known", type=int, default=c["stop_known"], help="new-only mode: stop after N pages with nothing new")
    p.add_argument("--quick", action="store_true", help="scrape right away using saved default values")
    p.add_argument("--menu", action="store_true", help="open the interactive menu")
    p.add_argument("--save-defaults", action="store_true", help="save the options given on this command line as defaults")
    p.add_argument("--export-db", action="store_true", help="export the whole database and exit")
    p.add_argument("--stats", action="store_true", help="show database stats and exit")
    p.add_argument("--no-prompt", action="store_true", help="never show the interactive menu")
    p.add_argument("--no-color", action="store_true", help="disable colored output")
    p.add_argument("-v", "--verbose", action="store_true", default=c["verbose"], help="also show skipped/filtered jobs")
    p.add_argument("--timeout", type=int, default=c["timeout"])
    p.add_argument("-q", "--quiet", action="store_true", default=c["quiet"])
    return p.parse_args()


def main():
    CONFIG.update(load_settings())
    args = get_args()
    init_color(args.no_color)
    conn = db_open(args.db)
    try:
        if args.save_defaults:
            save_settings(args)
            print(ok("✔ Defaults saved to ") + dim(SETTINGS_PATH))
        if args.stats:
            db_stats(conn)
        elif args.export_db:
            save(db_all_kept(conn), args, "database")
        elif args.quick:
            run_scrape(args, conn)
        elif args.menu or (len(sys.argv) == 1 and not args.no_prompt):
            interactive(args, conn)
        elif not args.save_defaults:
            run_scrape(args, conn)
    except (KeyboardInterrupt, EOFError):
        print(dim("\nBye."))
    finally:
        conn.close()


if __name__ == "__main__":
    sys.exit(main())

