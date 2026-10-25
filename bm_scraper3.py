#!/usr/bin/env python3
"""
BrighterMonday (Kenya) job scraper v4 - Termux optimized.

  * Scrape EVERYTHING: crawl every page + read every job's full details
    (resumable - already-detailed jobs are skipped on the next run)
  * Fill in missing details for jobs already in your database
  * Job details: description, qualification, experience, language, hours,
    applicant location, deadline, easy-apply (where the site provides them)
  * Quick scrape with saved defaults / custom scrape with prompts
  * Smart URL building (category/location/type) with automatic fallbacks
  * SQLite database: jobs already stored are skipped next time
  * Paged job browser with a detail view (no more 15-job limit)
  * Colored terminal output (auto-off when piped; --no-color)

Setup (Termux):
    pkg update && pkg install python -y
    pip install requests beautifulsoup4
    termux-setup-storage        # optional: lets it export to Downloads

Run:
    python bm_scraper.py                       # interactive menu
    python bm_scraper.py --quick               # scrape with saved defaults
    python bm_scraper.py --all --whole-site    # EVERY job + full details
    python bm_scraper.py --fill-details        # add details to saved jobs
    python bm_scraper.py -k waiter -l nairobi  # direct, no prompts
    python bm_scraper.py --stats | --export-db | --help
"""

import argparse
import copy
import csv
import json
import math
import os
import random
import re
import shutil
import sqlite3
import subprocess
import sys
import textwrap
import time
from datetime import datetime
from urllib.parse import parse_qs, urlencode, urljoin, urlparse, urlunparse

import requests
from bs4 import BeautifulSoup
from requests.adapters import HTTPAdapter
from urllib3.util.retry import Retry

# ----------------------------------------------------------------------
# DEFAULT OPTIONS  (used by "Quick scrape"; override via menu option 5,
# the command line, or by editing here)
# ----------------------------------------------------------------------
CONFIG = {
    "keyword": "",          # search term, e.g. "waiter"
    "category": "",         # category slug, e.g. "customer-service"
    "location": "",         # location slug, e.g. "nairobi"
    "work_type": "",        # work type slug, e.g. "full-time", "part-time"
    "url": "",              # full custom search URL (overrides the four above)
    "start_page": 1,
    "max_pages": 7,
    "limit": 0,             # stop after N kept jobs (0 = no limit)
    "delay_min": 2.0,       # polite delay between requests (seconds)
    "delay_max": 4.5,
    "details": False,       # open each NEW job page and read its full details
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
    "desc_limit": 6000,     # max characters of description stored per job
    "page_size": 15,        # jobs per page in the browser
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
TOTAL_RE = re.compile(r"([\d,]+)\s+Jobs?\s+Found", re.I)

CARD_COLS = ["title", "company", "location", "job_type", "salary", "category", "posted", "is_new"]
DETAIL_COLS = [
    "min_qualification", "experience_level", "experience_length", "language",
    "working_hours", "applicant_location", "deadline", "date_posted", "easy_apply",
]
KEEP_COLS = DETAIL_COLS + ["description"]   # preserved in the DB if a rescan has none
FIELDS = CARD_COLS + ["first_seen"] + DETAIL_COLS + ["url", "description"]

DETAIL_LABELS = [
    ("min_qualification", r"min(?:imum)?\.?\s+qualifications?"),
    ("experience_level", r"experience\s+level"),
    ("experience_length", r"experience\s+length"),
    ("language", r"language\s+requirements?"),
    ("working_hours", r"working\s+hours"),
    ("applicant_location", r"applicant\s+location"),
]
DETAIL_LABEL_RES = [
    (k, re.compile(r"^[\s•\-·*]*" + p + r"\s*:?\s*(.*)$", re.I)) for k, p in DETAIL_LABELS
]
END_MARKERS = [
    "Important safety tips", "Similar jobs", "Stay Updated",
    "We care about the protection", "This action will pause all job alerts",
]
DEADLINE_RE = re.compile(
    r"(?:deadline|closing date|closes on|apply before|application deadline)\W{0,6}"
    r"(\d{1,2}(?:st|nd|rd|th)?\s+[A-Za-z]+,?\s+\d{4}|[A-Za-z]+\s+\d{1,2},?\s+\d{4}|\d{4}-\d{2}-\d{2})",
    re.I,
)


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
    inner = max([len(strip_ansi(x)) for x in lines] + [len(title) + 4]) + 2
    out = [paint("┌" + ("─ " + title + " ").ljust(inner, "─") + "┐", color)]
    for x in lines:
        pad = " " * (inner - 1 - len(strip_ansi(x)))
        out.append(paint("│", color) + " " + x + pad + paint("│", color))
    out.append(paint("└" + "─" * inner + "┘", color))
    return "\n".join(out)


def progress_bar(done, total, width=18):
    total = max(total, 1)
    n = min(width, int(width * done / total))
    return paint("█" * n, "bgreen") + paint("░" * (width - n), "gray")


def status_line(msg=""):
    """Single self-overwriting line (only on a real terminal)."""
    if sys.stdout.isatty():
        sys.stdout.write("\r\033[K" + (dim(msg) if msg else ""))
        sys.stdout.flush()


def banner():
    print(paint("╭──────────────────────────────────╮", "bcyan"))
    print(paint("│", "bcyan") + paint("   BrighterMonday Job Scraper v4  ", "bold", "white") + paint("│", "bcyan"))
    print(paint("╰──────────────────────────────────╯", "bcyan"))


# ----------------------------------------------------------------------
# Small helpers
# ----------------------------------------------------------------------
def log(msg, args):
    if not args.quiet:
        print(msg, flush=True)


def now_str():
    return datetime.now().strftime("%Y-%m-%d %H:%M:%S")


def fmt_duration(seconds):
    seconds = int(seconds)
    h, rem = divmod(seconds, 3600)
    m, s = divmod(rem, 60)
    if h:
        return f"{h}h {m:02d}m"
    if m:
        return f"{m}m {s:02d}s"
    return f"{s}s"


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


def get_with_backoff(session, url, args, tries=3):
    """Like get_page, but waits and retries when the site says slow down."""
    for attempt in range(tries):
        status, text = get_page(session, url, args)
        if status in (403, 429) and attempt < tries - 1:
            wait = 45 * (attempt + 1)
            status_line()
            print(warn(f"  ⏳ site says slow down ({status}) - waiting {wait}s..."))
            time.sleep(wait)
            continue
        return status, text
    return status, text


def polite_sleep(args):
    time.sleep(random.uniform(args.delay_min, args.delay_max))
    if getattr(args, "long_run", False):
        args._reqs = getattr(args, "_reqs", 0) + 1
        if args._reqs % 40 == 0:
            rest = random.uniform(20, 35)
            status_line()
            print(dim(f"  ☕ short break ({int(rest)}s) to stay polite"))
            time.sleep(rest)


def explain_status(status, text):
    if status is None:
        return bad(f"  ✖ network error: {text[:120]}")
    if status in (404, 410):
        return dim(f"  ↳ page gone ({status}) - end of results")
    if status in (403, 429):
        return bad(f"  ✖ blocked/rate-limited ({status}). Wait a while or raise the delays.")
    return bad(f"  ✖ HTTP {status}")


def fetch(session, url, args):
    """Detail-page fetch: returns HTML or None."""
    status, text = get_with_backoff(session, url, args)
    if status == 200:
        return text
    status_line()
    log(explain_status(status, text), args)
    return None


def wake_lock(on):
    """Keep Termux awake during long runs (needs the Termux:API-free built-in command)."""
    exe = shutil.which("termux-wake-lock" if on else "termux-wake-unlock")
    if exe:
        subprocess.run([exe], check=False)
        if on:
            print(dim("  wake-lock on (screen can turn off)"))


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
    if (args.keyword or args.category) and (args.location or args.work_type):
        modes.append(("keyword only (location/type dropped)", "kw_only"))
    return modes


def resolve_search(session, args):
    """Find a URL pattern that the site accepts; returns dict or None."""
    first = args.start_page
    modes = search_modes(args)
    for name, mode in modes:
        url = build_url(args, first, mode)
        status, text = get_with_backoff(session, url, args)
        if status == 200:
            if mode != "exact":
                print(warn(f"  ⚠ fallback used: {name}"))
            return {"mode": mode, "url": url, "html": text}
        if status in (404, 410):
            print(warn(f"  ⚠ {status} for {url}"))
            if (name, mode) != modes[-1]:
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
    if getattr(args, "crawl_all", False):
        pages = f"from page {args.start_page}, no page limit"
    else:
        pages = f"pages {args.start_page}-{args.start_page + args.max_pages - 1}"
    mode = "full scan" if args.full else "new only"
    extra = ", details" if args.details else ""
    return f"{what} | {pages} | {mode}{extra}"


def clean_link(base, href):
    return urljoin(base, href.split("?")[0].split("#")[0])


def parse_total(html):
    m = TOTAL_RE.search(html or "")
    return int(m.group(1).replace(",", "")) if m else 0


def discover_filters(html):
    """Single-segment /jobs/<slug> links on a results page (categories, locations...)."""
    soup = BeautifulSoup(html, "html.parser")
    found = []
    for a in soup.find_all("a", href=True):
        path = urlparse(urljoin(BASE, a["href"])).path.rstrip("/")
        m = re.fullmatch(r"/jobs/([a-z0-9][a-z0-9-]*)", path)
        if m and m.group(1) not in found:
            found.append(m.group(1))
    return found


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


def _ld_jobposting(soup):
    for s in soup.find_all("script", type="application/ld+json"):
        try:
            data = json.loads(s.string or s.get_text() or "")
        except ValueError:
            continue
        items = data if isinstance(data, list) else (
            data.get("@graph", [data]) if isinstance(data, dict) else [])
        for it in items:
            if isinstance(it, dict) and "JobPosting" in str(it.get("@type", "")):
                return it
    return {}


def parse_details(html, limit=6000):
    """Pull the description and structured details out of a job page."""
    soup = BeautifulSoup(html, "html.parser")
    ld = _ld_jobposting(soup)
    for t in soup(["script", "style", "nav", "footer", "header", "noscript"]):
        t.decompose()
    root = soup.find("main") or soup.body or soup
    pieces = list(root.stripped_strings)
    joined = " ".join(pieces)

    out = dict.fromkeys(KEEP_COLS, "")

    # labelled facts, e.g. "Experience Level : Entry level" (inline or next piece)
    for i, piece in enumerate(pieces):
        for key, rx in DETAIL_LABEL_RES:
            m = rx.match(piece)
            if not m or out[key]:
                continue
            val = m.group(1).strip(" :•-·")
            if not val and i + 1 < len(pieces):
                nxt = pieces[i + 1]
                if not any(r.match(nxt) for _, r in DETAIL_LABEL_RES):
                    val = nxt.strip(" :•-·")
            if 0 < len(val) < 120:
                out[key] = val

    # description: from "Job summary" up to the page boilerplate
    start = joined.find("Job summary")
    start = 0 if start < 0 else start
    end = len(joined)
    for mk in END_MARKERS:
        j = joined.find(mk, start + 1)
        if j != -1:
            end = min(end, j)
    out["description"] = re.sub(r"\s+", " ", joined[start:end]).strip()[:limit]

    # structured data (JSON-LD) fills the gaps when present
    if ld:
        out["date_posted"] = str(ld.get("datePosted", ""))[:10]
        out["deadline"] = str(ld.get("validThrough", ""))[:10]
        if not out["description"] and ld.get("description"):
            ld_text = BeautifulSoup(str(ld["description"]), "html.parser").get_text(" ", strip=True)
            out["description"] = re.sub(r"\s+", " ", ld_text)[:limit]
    if not out["deadline"]:
        m = DEADLINE_RE.search(joined)
        if m:
            out["deadline"] = m.group(1)
    if re.search(r"easy\s+apply", joined, re.I):
        out["easy_apply"] = "yes"
    return out


def apply_details(job, html, args):
    d = parse_details(html, args.desc_limit)
    for k, v in d.items():
        if v:
            job[k] = v
    job["detailed"] = 1


def is_excluded(job, args):
    """Exclude words are checked against title/company/category only."""
    if not args.exclude:
        return False
    blob = f"{job['title']} {job['company']} {job['category']}".lower()
    return any(w.lower() in blob for w in args.exclude)


def is_included(job, args):
    """Include words are checked against the card text AND the details."""
    if not args.include:
        return True
    blob = " ".join(str(job.get(k, "")) for k in FIELDS).lower()
    return any(w.lower() in blob for w in args.include)


def fmt_job(job, marker="", mcolor="white", indent=2):
    sal = job["salary"]
    sal_s = paint(sal, "bgreen") if sal and sal.lower() != "confidential" else dim(sal or "-")
    badge = " " + paint(" NEW ", "bold", "green") if job["is_new"] else ""
    sep = dim("·")
    mk = (paint(marker, mcolor, "bold") + " ") if marker else ""
    l1 = f"{' ' * indent}{mk}{paint(job['title'], 'bold', 'white')}{badge}"
    l2 = (f"{' ' * (indent + 4)}{paint(job['company'] or '-', 'bcyan')} {sep} {job['location'] or '-'} "
          f"{sep} {sal_s} {sep} {dim(job['posted'] or '-')}")
    bits = [job.get("min_qualification", ""), job.get("experience_level", ""),
            job.get("experience_length", ""),
            ("closes " + job["deadline"]) if job.get("deadline") else ""]
    bits = [b for b in bits if b]
    out = l1 + "\n" + l2
    if bits:
        out += "\n" + dim(" " * (indent + 4) + " · ".join(bits))
    return out


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
        if k not in SETTING_KEYS:
            continue
        if type(v) is type(CONFIG[k]):
            good[k] = v
        elif isinstance(CONFIG[k], float) and isinstance(v, int):
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
    cols_sql = ", ".join(
        [f"{c} TEXT" for c in CARD_COLS] + [f"{c} TEXT DEFAULT ''" for c in KEEP_COLS]
    )
    conn.execute(f"""
        CREATE TABLE IF NOT EXISTS jobs (
            url TEXT PRIMARY KEY, {cols_sql},
            kept INTEGER DEFAULT 1, query TEXT,
            first_seen TEXT, last_seen TEXT,
            times_seen INTEGER DEFAULT 1,
            detailed INTEGER DEFAULT 0
        )
    """)
    have = {r[1] for r in conn.execute("PRAGMA table_info(jobs)")}
    for c in KEEP_COLS:                      # upgrade databases from older versions
        if c not in have:
            conn.execute(f"ALTER TABLE jobs ADD COLUMN {c} TEXT DEFAULT ''")
    if "detailed" not in have:
        conn.execute("ALTER TABLE jobs ADD COLUMN detailed INTEGER DEFAULT 0")
    conn.commit()
    return conn


def db_count(conn):
    return conn.execute("SELECT COUNT(*) FROM jobs").fetchone()[0]


def db_known_urls(conn):
    return {r[0] for r in conn.execute("SELECT url FROM jobs")}


def db_detailed_urls(conn):
    return {r[0] for r in conn.execute("SELECT url FROM jobs WHERE detailed=1")}


def db_upsert(conn, job, kept, query):
    ts = now_str()
    names = (["url"] + CARD_COLS + KEEP_COLS +
             ["kept", "query", "first_seen", "last_seen", "times_seen", "detailed"])
    vals = ([job["url"]] + [job.get(c, "") for c in CARD_COLS + KEEP_COLS] +
            [1 if kept else 0, query, ts, ts, 1, 1 if job.get("detailed") else 0])
    upd = [f"{c}=excluded.{c}" for c in CARD_COLS]
    upd += [f"{c}=CASE WHEN excluded.{c}<>'' THEN excluded.{c} ELSE jobs.{c} END" for c in KEEP_COLS]
    upd += ["kept=excluded.kept", "last_seen=excluded.last_seen",
            "times_seen=jobs.times_seen+1", "detailed=MAX(jobs.detailed, excluded.detailed)"]
    sql = (f"INSERT INTO jobs ({','.join(names)}) VALUES ({','.join('?' * len(names))}) "
           f"ON CONFLICT(url) DO UPDATE SET {', '.join(upd)}")
    conn.execute(sql, vals)
    job["first_seen"] = job.get("first_seen") or ts


def db_save_details(conn, job):
    sets = ", ".join(f"{c}=?" for c in KEEP_COLS)
    conn.execute(
        f"UPDATE jobs SET {sets}, detailed=1, last_seen=? WHERE url=?",
        [job.get(c, "") for c in KEEP_COLS] + [now_str(), job["url"]],
    )


def db_touch(conn, url):
    conn.execute(
        "UPDATE jobs SET last_seen=?, times_seen=times_seen+1 WHERE url=?",
        (now_str(), url),
    )


def _rows(rows):
    return [{k: (r[k] if r[k] is not None else "") for k in FIELDS} for r in rows]


def db_all_kept(conn):
    return _rows(conn.execute("SELECT * FROM jobs WHERE kept=1 ORDER BY first_seen DESC, url").fetchall())


def db_missing_details(conn):
    return _rows(conn.execute(
        "SELECT * FROM jobs WHERE kept=1 AND detailed=0 ORDER BY first_seen DESC, url").fetchall())


def _where(term):
    if not term:
        return "kept=1", []
    like = f"%{term}%"
    return ("kept=1 AND (title LIKE ? OR company LIKE ? OR category LIKE ? "
            "OR description LIKE ? OR location LIKE ?)", [like] * 5)


def db_search_count(conn, term):
    where, params = _where(term)
    return conn.execute(f"SELECT COUNT(*) FROM jobs WHERE {where}", params).fetchone()[0]


def db_search(conn, term, limit, offset):
    where, params = _where(term)
    return _rows(conn.execute(
        f"SELECT * FROM jobs WHERE {where} ORDER BY first_seen DESC, url LIMIT ? OFFSET ?",
        params + [limit, offset]).fetchall())


def db_stats(conn):
    total = db_count(conn)
    kept = conn.execute("SELECT COUNT(*) FROM jobs WHERE kept=1").fetchone()[0]
    detailed = conn.execute("SELECT COUNT(*) FROM jobs WHERE kept=1 AND detailed=1").fetchone()[0]
    first = conn.execute("SELECT MIN(first_seen) FROM jobs").fetchone()[0]
    last = conn.execute("SELECT MAX(last_seen) FROM jobs").fetchone()[0]
    cats = conn.execute(
        "SELECT category, COUNT(*) c FROM jobs WHERE kept=1 AND category<>'' "
        "GROUP BY category ORDER BY c DESC LIMIT 5"
    ).fetchall()
    lines = [
        f"Jobs seen      {paint(total, 'bold')}",
        f"Kept           {ok(kept)}",
        f"With details   {ok(detailed)} {dim(f'({kept - detailed} missing)')}",
        f"Filtered out   {warn(total - kept)}",
        f"First scrape   {dim(first or '-')}",
        f"Last seen      {dim(last or '-')}",
    ]
    if cats:
        lines += ["", paint("Top categories", "bold")]
        top = max(r["c"] for r in cats)
        for r in cats:
            lines.append(f"{progress_bar(r['c'], top, 10)} {r['c']:>4}  {r['category']}")
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
                    f.write(f"  {j['job_type']} | {j['salary']} | {j['posted']}\n")
                    extra = [j.get(k, "") for k in ("min_qualification", "experience_level", "experience_length", "deadline")]
                    if any(extra):
                        f.write("  " + " | ".join(x for x in extra if x) + "\n")
                    f.write(f"  {j['url']}\n")
                    if j.get("description"):
                        f.write("  " + j["description"][:600] + "\n")
                    f.write("\n")
        else:
            continue
        print(f"{ok('💾 Saved')} {path} {dim(f'({len(jobs)} jobs)')}")


# ----------------------------------------------------------------------
# Scraping
# ----------------------------------------------------------------------
def run_scrape(args, conn, export=True):
    """Crawl result pages. Returns the list of jobs kept in this run."""
    session = make_session()
    known = db_known_urls(conn)
    detailed = db_detailed_urls(conn) if args.details else set()
    label = query_label(args)
    crawl_all = getattr(args, "crawl_all", False)
    fill_known = getattr(args, "fill_known", False)
    end_page = args.start_page + args.max_pages - 1
    mode_tag = paint(" FULL SCAN ", "bold", "yellow") if args.full else paint(" NEW ONLY ", "bold", "green")

    print(f"\n{head('▶ Scan started')} {mode_tag} {dim(f'database holds {len(known)} jobs')}")
    print(dim("  " + describe_args(args)))

    plan = resolve_search(session, args)
    if not plan:
        return []

    total_jobs = parse_total(plan["html"])
    total_pages = None
    results, seen_run = [], set()
    skipped = rejected = quiet_pages = pages_done = filled = details_ok = 0
    t0 = time.time()

    try:
        for page in range(args.start_page, end_page + 1):
            if page == args.start_page:
                url, html = plan["url"], plan["html"]
            else:
                url = build_url(args, page, plan["mode"])
                status, html = get_with_backoff(session, url, args)
                if status != 200:
                    print(explain_status(status, html))
                    break

            found = parse_listings(html)
            if page == args.start_page and total_jobs and found:
                total_pages = math.ceil(total_jobs / len(found))

            done = page - args.start_page + 1
            if crawl_all:
                if total_pages:
                    prog = f"{dim(f'({done}/~{total_pages})')} {progress_bar(done, total_pages)}"
                else:
                    prog = ""
            else:
                prog = f"{dim(f'({done}/{args.max_pages})')} {progress_bar(done, args.max_pages)}"
            print(f"\n{head(f'Page {page}')} {prog}")
            print(dim("  " + url))

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
            for idx, job in enumerate(fresh, 1):
                seen_run.add(job["url"])
                was_known = job["url"] in known
                if not was_known:
                    unknown_on_page += 1
                needs_details = args.details and job["url"] not in detailed

                # Already in the database and not a full scan -> skip,
                # unless we are filling in missing details for it
                if was_known and not args.full and not (fill_known and needs_details):
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

                if needs_details or (args.details and args.full):
                    polite_sleep(args)
                    status_line(f"  ⋯ details {idx}/{len(fresh)}: {job['title'][:45]}")
                    d_html = fetch(session, job["url"], args)
                    status_line()
                    if d_html:
                        apply_details(job, d_html, args)
                        detailed.add(job["url"])
                        details_ok += 1

                if not is_included(job, args):
                    db_upsert(conn, job, False, label)
                    known.add(job["url"])
                    rejected += 1
                    if args.verbose:
                        print(paint(f"  ✖ no include match: {job['title']}", "red", "dim"))
                    continue

                db_upsert(conn, job, True, label)
                if args.details:
                    conn.commit()           # keep progress safe on long runs
                results.append(job)
                kept_on_page += 1
                if not was_known:
                    print(fmt_job(job, "✚", "bgreen"))
                elif args.full:
                    print(fmt_job(job, "↻", "byellow"))
                else:
                    filled += 1
                    print(fmt_job(job, "⤓", "bcyan"))
                known.add(job["url"])
                if args.limit and len(results) >= args.limit:
                    break

            conn.commit()
            print(dim("  page result: ") + f"{ok(kept_on_page)} kept " + dim("|") +
                  f" {skipped} known " + dim("|") + f" {rejected} filtered")

            if args.limit and len(results) >= args.limit:
                print(warn("  limit reached"))
                break

            if not args.full and args.stop_known and not crawl_all:
                quiet_pages = quiet_pages + 1 if unknown_on_page == 0 else 0
                if quiet_pages >= args.stop_known:
                    print(warn(f"  {quiet_pages} page(s) in a row with nothing new - stopping early"))
                    break

            if page < end_page:
                polite_sleep(args)
    except KeyboardInterrupt:
        status_line()
        print(warn("\n⏹ Interrupted - progress is saved in the database."))

    conn.commit()
    label_kept = "Jobs kept" if args.full else "NEW jobs"
    lines = [
        f"{label_kept:<14}{ok(len(results) - filled) if results else dim(0)}",
        f"{'Details added':<14}{ok(filled) if filled else dim(0)}",
        f"{'Already known':<14}{skipped}",
        f"{'Filtered out':<14}{warn(rejected) if rejected else dim(0)}",
        f"{'Details read':<14}{details_ok}",
        f"{'Pages scanned':<14}{pages_done}",
        f"{'Time':<14}{dim(fmt_duration(time.time() - t0))}",
    ]
    print("\n" + box("Scan complete", lines, "bgreen" if results else "byellow"))
    if export:
        save(results, args, "full" if args.full else "new")
    return results


def run_scrape_all(args, conn, confirm=True, sweep=False):
    """Crawl EVERY result page and read EVERY job's full details (resumable)."""
    a = copy.copy(args)
    a.details = True
    a.crawl_all = True
    a.fill_known = True
    a.long_run = True
    a.max_pages = 10 ** 6
    a.limit = 0
    a.include, a.exclude = [], []
    a.full = False
    a.stop_known = 0

    session = make_session()
    print(f"\n{head('▶ Scrape everything')}  {dim(describe_args(a))}")
    plan = resolve_search(session, a)
    if not plan:
        return

    total = parse_total(plan["html"])
    first_n = max(len(parse_listings(plan["html"])), 1)
    have = len(db_detailed_urls(conn))
    avg = (a.delay_min + a.delay_max) / 2 + 0.8
    lines = []
    if total:
        todo = max(total - have, 0)
        lines += [
            f"Jobs on site      {paint(f'{total:,}', 'bold')}",
            f"Result pages      ~{math.ceil(total / first_n):,}",
            f"Already detailed  {have:,} {dim('(skipped)')}",
            f"Estimated time    {warn(fmt_duration(todo * avg + math.ceil(total / first_n) * avg))}",
        ]
    else:
        lines.append(dim("Total not shown by the site - will crawl until results end."))
    slugs = []
    if sweep and not a.url:
        slugs = [s for s in discover_filters(plan["html"]) if s != a.category]
        lines.append(f"Filter sweep      {len(slugs)} extra category/location pages {dim('(best effort)')}")
    lines += [
        dim("Resumable: Ctrl+C any time, run again to continue."),
        dim("Tip: keep Termux in the foreground or use termux-wake-lock."),
    ]
    print("\n" + box("Scrape everything", lines, "byellow"))
    if confirm and not ask_yn("Start now?", True):
        return

    wake_lock(True)
    try:
        run_scrape(a, conn, export=False)
        for i, slug in enumerate(slugs, 1):
            sub = copy.copy(a)
            sub.url, sub.keyword, sub.location, sub.work_type = "", "", "", ""
            sub.category = slug
            print(f"\n{head(f'━━ Sweep {i}/{len(slugs)}: {slug} ━━')}")
            run_scrape(sub, conn, export=False)
    except KeyboardInterrupt:
        print(warn("\n⏹ Stopped. Run again to continue where it left off."))
    finally:
        wake_lock(False)
    save(db_all_kept(conn), a, "everything")


def run_fill_details(args, conn):
    """Read the full details for saved jobs that don't have them yet."""
    todo = db_missing_details(conn)
    if not todo:
        print(ok("✔ Every saved job already has its details."))
        return
    if args.limit:
        todo = todo[:args.limit]
    a = copy.copy(args)
    a.long_run = True
    avg = (a.delay_min + a.delay_max) / 2 + 0.8
    print(f"\n{head('▶ Filling in details')} {len(todo)} jobs {dim('~' + fmt_duration(len(todo) * avg))}")
    session = make_session()
    done = failed = 0
    t0 = time.time()
    wake_lock(True)
    try:
        for i, job in enumerate(todo, 1):
            polite_sleep(a)
            status_line(f"  ⋯ {i}/{len(todo)}: {job['title'][:50]}")
            html = fetch(session, job["url"], a)
            status_line()
            if not html:
                failed += 1
                continue
            apply_details(job, html, a)
            db_save_details(conn, job)
            conn.commit()
            done += 1
            print(fmt_job(job, "⤓", "bcyan"))
    except KeyboardInterrupt:
        status_line()
        print(warn("\n⏹ Interrupted - progress is saved."))
    finally:
        wake_lock(False)
    lines = [
        f"{'Details added':<14}{ok(done) if done else dim(0)}",
        f"{'Failed':<14}{bad(failed) if failed else dim(0)}",
        f"{'Time':<14}{dim(fmt_duration(time.time() - t0))}",
    ]
    print("\n" + box("Details complete", lines, "bgreen" if done else "byellow"))
    if done:
        save(db_all_kept(conn), a, "details")


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
    args.details = ask_yn("Read each job's full details? (slower; adds description, qualification, experience...)", args.details)
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


def show_job(job, full=False):
    cols = shutil.get_terminal_size((60, 20)).columns
    width = max(30, min(cols - 4, 90))
    print("\n" + paint(job["title"], "bold", "white") +
          (" " + paint(" NEW ", "bold", "green") if job["is_new"] else ""))
    print(paint(job["company"] or "-", "bcyan") + dim(" · ") + (job["location"] or "-"))
    exp = " ".join(x for x in (job["experience_level"], job["experience_length"]) if x)
    rows = [
        ("Salary", job["salary"]), ("Type", job["job_type"]), ("Category", job["category"]),
        ("Posted", job["posted"]), ("Closes", job["deadline"]),
        ("Qualification", job["min_qualification"]), ("Experience", exp),
        ("Language", job["language"]), ("Hours", job["working_hours"]),
        ("Applicant loc.", job["applicant_location"]), ("Easy apply", job["easy_apply"]),
        ("First seen", job["first_seen"]), ("Link", job["url"]),
    ]
    for label, val in rows:
        if val:
            print("  " + paint(label.ljust(15), "gray") + str(val))
    desc = job["description"]
    if desc:
        shown = desc if full else desc[:1200]
        print("\n" + paint("Description", "bold"))
        print(textwrap.fill(shown, width=width, initial_indent="  ", subsequent_indent="  "))
        if not full and len(desc) > 1200:
            print(dim(f"  ... {len(desc) - 1200} more characters (press m)"))
    else:
        print(dim("\n  (no details saved yet - use 'Fill in missing details' from the menu)"))


def view_job(job):
    full = False
    while True:
        show_job(job, full)
        cmd = read(f"\n{paint('›', 'byellow', 'bold')} {dim('o = open in browser · m = full text · Enter = back')}: ").strip().lower()
        if cmd == "o":
            open_in_browser(job["url"])
        elif cmd == "m":
            full = True
        else:
            return


def browse_jobs(conn, size=15):
    term = read(f"{paint('›', 'byellow', 'bold')} Filter {dim('(title/company/category/description, Enter = all)')}: ").strip()
    offset = 0
    while True:
        total = db_search_count(conn, term)
        if total == 0:
            print(warn("No matching jobs in the database."))
            return
        offset = min(offset, ((total - 1) // size) * size)
        rows = db_search(conn, term, size, offset)
        pages = math.ceil(total / size)
        title = f"{head('Saved jobs')} {dim(f'{offset + 1}-{offset + len(rows)} of {total}')} {dim(f'(page {offset // size + 1}/{pages})')}"
        if term:
            title += " " + dim(f"filter: {term}")
        print("\n" + title)
        for i, j in enumerate(rows, offset + 1):
            print(paint(f"{i:>3}.", "byellow") + " " + fmt_job(j, indent=0))
        more = offset + size < total
        nav = "number = view · " + ("n = next · " if more else "") + ("p = prev · " if offset else "") + "f = filter · s = page size · q = back"
        cmd = read(f"\n{paint('›', 'byellow', 'bold')} {dim(nav)}: ").strip().lower()
        if cmd == "q":
            return
        if cmd in ("n", "") and more:
            offset += size
        elif cmd == "" and not more:
            return
        elif cmd == "p":
            offset = max(0, offset - size)
        elif cmd == "f":
            term = read(f"{paint('›', 'byellow', 'bold')} New filter {dim('(Enter = all)')}: ").strip()
            offset = 0
        elif cmd == "s":
            size = max(5, ask("Jobs per page", size, int))
            offset = 0
        elif cmd.isdigit() and 1 <= int(cmd) <= total:
            job = db_search(conn, term, 1, int(cmd) - 1)
            if job:
                view_job(job[0])


def interactive(args, conn):
    banner()
    while True:
        defaults = apply_defaults(copy.copy(args))
        kept = conn.execute("SELECT COUNT(*) FROM jobs WHERE kept=1").fetchone()[0]
        missing = conn.execute("SELECT COUNT(*) FROM jobs WHERE kept=1 AND detailed=0").fetchone()[0]
        print("\n" + box("Saved defaults", [dim(describe_args(defaults)),
                                            dim(f"database: {kept} jobs, {missing} without details")]))
        print(f" {paint('1', 'bgreen', 'bold')}) Quick scrape        {dim('(use saved defaults)')}")
        print(f" {paint('2', 'bcyan', 'bold')}) Custom scrape       {dim('(answer prompts)')}")
        print(f" {paint('3', 'byellow', 'bold')}) Scrape EVERYTHING   {dim('(all jobs + full details)')}")
        print(f" {paint('4', 'byellow', 'bold')}) Fill in missing details {dim('(saved jobs)')}")
        print(f" {paint('5', 'bmagenta', 'bold')}) Edit & save defaults")
        print(f" {paint('6', 'bmagenta', 'bold')}) Browse saved jobs   {dim('(paged, view details)')}")
        print(f" {paint('7', 'bblue', 'bold')}) Export whole database")
        print(f" {paint('8', 'bblue', 'bold')}) Database stats")
        print(f" {paint('9', 'bred', 'bold')}) Clear database")
        print(f" {paint('0', 'gray', 'bold')}) Quit")
        choice = read(f"{paint('Choose', 'bold')}: ").strip()
        if choice == "1":
            run_scrape(defaults, conn)
        elif choice == "2":
            run_scrape(prompt_scrape_options(defaults, conn), conn)
            if ask_yn("Save these options as your new defaults?", False):
                save_settings(defaults)
                print(ok("✔ Defaults saved."))
        elif choice == "3":
            keep_filters = ask_yn("Limit to your saved filters (keyword/category/location)? No = whole site", False)
            if not keep_filters:
                defaults.url = defaults.keyword = defaults.category = ""
                defaults.location = defaults.work_type = ""
            sweep = ask_yn("Also sweep every category/location filter found on the site? (slower, catches more)", False)
            run_scrape_all(defaults, conn, confirm=True, sweep=sweep)
        elif choice == "4":
            defaults.limit = ask("Only the newest N jobs", 0, int, hint="(0 = all of them)")
            run_fill_details(defaults, conn)
        elif choice == "5":
            edited = prompt_scrape_options(defaults, conn, defaults_mode=True)
            save_settings(edited)
            print(ok("✔ Defaults saved to ") + dim(SETTINGS_PATH))
        elif choice == "6":
            browse_jobs(conn, args.page_size)
        elif choice == "7":
            args.formats = ask_formats(args.formats)
            save(db_all_kept(conn), args, "database")
        elif choice == "8":
            db_stats(conn)
        elif choice == "9":
            if read(f"{bad('Type yes to delete ALL stored jobs')}: ").strip().lower() == "yes":
                conn.execute("DELETE FROM jobs")
                conn.commit()
                print(ok("Database cleared."))
        elif choice in ("0", "q", ""):
            print(dim("Bye."))
            break


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
    p.add_argument("-d", "--details", action="store_true", default=c["details"], help="read each job's full details")
    p.add_argument("-i", "--include", nargs="*", default=c["include"], help="keep jobs containing any of these words")
    p.add_argument("-x", "--exclude", nargs="*", default=c["exclude"], help="drop jobs whose title/company/category contain these")
    p.add_argument("-f", "--formats", nargs="+", default=c["formats"], choices=["csv", "json", "txt"])
    p.add_argument("-o", "--outdir", default=c["outdir"], help="export folder")
    p.add_argument("--db", default=c["db"], help="database path")
    p.add_argument("--full", action="store_true", default=c["full"], help="full scan: re-check jobs already in the database")
    p.add_argument("--stop-known", type=int, default=c["stop_known"], help="new-only mode: stop after N pages with nothing new")
    p.add_argument("--all", action="store_true", help="scrape EVERY page and every job's full details (resumable)")
    p.add_argument("--whole-site", action="store_true", help="with --all: ignore saved filters and crawl the whole site")
    p.add_argument("--sweep", action="store_true", help="with --all: also crawl every category/location filter found")
    p.add_argument("--fill-details", action="store_true", help="read details for saved jobs that don't have them")
    p.add_argument("-y", "--yes", action="store_true", help="don't ask for confirmation (for --all)")
    p.add_argument("--quick", action="store_true", help="scrape right away using saved default values")
    p.add_argument("--menu", action="store_true", help="open the interactive menu")
    p.add_argument("--save-defaults", action="store_true", help="save the options given on this command line as defaults")
    p.add_argument("--export-db", action="store_true", help="export the whole database and exit")
    p.add_argument("--stats", action="store_true", help="show database stats and exit")
    p.add_argument("--no-prompt", action="store_true", help="never show the interactive menu")
    p.add_argument("--no-color", action="store_true", help="disable colored output")
    p.add_argument("-v", "--verbose", action="store_true", default=c["verbose"], help="also show skipped/filtered jobs")
    p.add_argument("--desc-limit", type=int, default=c["desc_limit"], help="max description characters stored per job")
    p.add_argument("--page-size", type=int, default=c["page_size"], help="jobs per page in the browser")
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
        elif args.all:
            if args.whole_site:
                args.url = args.keyword = args.category = args.location = args.work_type = ""
            run_scrape_all(args, conn, confirm=not args.yes, sweep=args.sweep)
        elif args.fill_details:
            run_fill_details(args, conn)
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
