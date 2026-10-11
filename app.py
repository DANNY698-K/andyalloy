from flask import Flask, render_template, request, redirect, url_for, session, flash, Response, send_from_directory
from jinja2 import DictLoader
from werkzeug.security import generate_password_hash, check_password_hash
from werkzeug.utils import secure_filename
import sqlite3
import io
import base64
import os
import re
import time
import hashlib
import secrets as pysecrets
from urllib.parse import urlencode
import requests

try:
    import psycopg2
    import psycopg2.extras
except ImportError:
    psycopg2 = None

app = Flask(__name__)
app.secret_key = os.environ.get("SECRET_KEY", "1495dff8208d99c1764d317cfecc295eee3e2cb9405f944deda5f3b8c53f2960")

# ---------------------------------------------------------------------------
# SECURITY HARDENING
# ---------------------------------------------------------------------------
# Debug mode now defaults OFF and must be explicitly enabled — leaving
# Flask's debugger reachable in production allows remote code execution.
FLASK_DEBUG = os.environ.get("FLASK_DEBUG", "0") == "1"

# Cap request size so a huge upload can't be used to exhaust memory/disk.
app.config["MAX_CONTENT_LENGTH"] = 30 * 1024 * 1024  # 30 MB

# Session cookie hardening. SESSION_COOKIE_SECURE is left off by default so
# local HTTP testing keeps working — set FORCE_HTTPS=1 once this is served
# over HTTPS (Render, your own domain, etc.) so the session cookie is only
# ever sent over an encrypted connection.
app.config["SESSION_COOKIE_HTTPONLY"] = True
app.config["SESSION_COOKIE_SAMESITE"] = "Lax"
app.config["SESSION_COOKIE_SECURE"] = os.environ.get("FORCE_HTTPS", "0") == "1"


@app.after_request
def set_security_headers(response):
    response.headers["X-Content-Type-Options"] = "nosniff"
    response.headers["X-Frame-Options"] = "DENY"
    response.headers["Referrer-Policy"] = "strict-origin-when-cross-origin"
    return response


# --- CSRF protection ---------------------------------------------------
# Every POST form carries a hidden csrf_token field (added automatically,
# see inject_csrf_token below). This check runs before any POST route and
# rejects the request if the token is missing or doesn't match the one
# tied to the visitor's session, blocking cross-site request forgery.
@app.before_request
def check_csrf():
    if request.method == "POST":
        session_token = session.get("_csrf_token")
        form_token = request.form.get("csrf_token")
        if not session_token or not form_token or not pysecrets.compare_digest(session_token, form_token):
            flash("Your session expired — please try that again.", "error")
            return redirect(request.referrer or url_for("home"))


_SITE_CONTROL_EXEMPT_ENDPOINTS = {
    "login", "logout", "login_google", "google_callback", "static", "style_css",
    "admin_site", "admin_controls", "admin_dashboard", "admin_artisans", "add_artisan",
    "toggle_artisan", "admin_jobs", "admin_chats", "job_thread", "post_job_message",
    "admin_update_job", "settings", "forgot_password", "reset_password",
}


@app.before_request
def enforce_site_controls():
    endpoint = request.endpoint
    if not endpoint or endpoint in _SITE_CONTROL_EXEMPT_ENDPOINTS:
        return
    site = get_site_content()
    user = current_user()

    if site.get("maintenance_mode") and not is_owner(user):
        return render_template("maintenance.html", user=None, active_page="maintenance", auto_open_auth=False), 503

    if endpoint == "signup_customer" and not site.get("signups_enabled", 1):
        flash("New sign-ups are temporarily paused. Please check back soon.", "error")
        return redirect(url_for("home"))

    if endpoint in ("catalog", "add_to_cart", "cart", "checkout_cart") and not site.get("catalog_enabled", 1):
        flash("The catalog is temporarily unavailable.", "error")
        return redirect(url_for("home"))

    if endpoint in ("reels", "like_video", "save_video", "comment_video", "my_collection") and not site.get("reels_enabled", 1):
        flash("Reels are temporarily unavailable.", "error")
        return redirect(url_for("home"))

    if endpoint == "tipped_videos" and not site.get("tipped_videos_enabled", 1):
        flash("Tipped Videos are temporarily unavailable.", "error")
        return redirect(url_for("home"))

    if endpoint in ("measure_tool", "save_measurement", "measurement_history") and not site.get("measure_enabled", 1):
        flash("The Measurement Assistant is temporarily unavailable.", "error")
        return redirect(url_for("home"))


def get_csrf_token():
    if "_csrf_token" not in session:
        session["_csrf_token"] = pysecrets.token_hex(24)
    return session["_csrf_token"]


@app.context_processor
def inject_csrf_token():
    return {"csrf_token": get_csrf_token}


# --- Login rate limiting (brute-force protection) -----------------------
# In-memory per-process tracker: fine for a single dev/small deployment;
# for multiple server workers in production, swap this dict for a shared
# store like Redis so limits apply across all of them.
_login_attempts = {}
LOGIN_MAX_ATTEMPTS = 6
LOGIN_LOCKOUT_SECONDS = 300


def _login_rate_limited(key):
    now = time.time()
    attempts = [t for t in _login_attempts.get(key, []) if now - t < LOGIN_LOCKOUT_SECONDS]
    _login_attempts[key] = attempts
    return len(attempts) >= LOGIN_MAX_ATTEMPTS


def _record_login_attempt(key):
    _login_attempts.setdefault(key, []).append(time.time())

# ---------------------------------------------------------------------------
# SUPABASE — one connection string for the database itself.
# ---------------------------------------------------------------------------
SUPABASE_DB_URL = os.environ.get("SUPABASE_DB_URL", "REPLACE_ME")


def supabase_db_configured():
    return SUPABASE_DB_URL != "REPLACE_ME" and psycopg2 is not None


def upload_media(file_storage):
    """Tries Cloudinary for any image. Returns a URL, or None if not
    configured/working (the caller then falls back to local disk)."""
    return upload_to_cloudinary(file_storage)


# ---------------------------------------------------------------------------
# GOOGLE SIGN-IN — lets customers create an account or log in with Gmail.
# ---------------------------------------------------------------------------
GOOGLE_CLIENT_ID = os.environ.get("GOOGLE_CLIENT_ID", "REPLACE_ME")
GOOGLE_CLIENT_SECRET = os.environ.get("GOOGLE_CLIENT_SECRET", "REPLACE_ME")


def google_configured():
    return "REPLACE_ME" not in (GOOGLE_CLIENT_ID, GOOGLE_CLIENT_SECRET)


# ---------------------------------------------------------------------------
# CLOUDINARY — image/video storage.
# ---------------------------------------------------------------------------
CLOUDINARY_CLOUD_NAME = os.environ.get("CLOUDINARY_CLOUD_NAME", "REPLACE_ME")
CLOUDINARY_API_KEY = os.environ.get("CLOUDINARY_API_KEY", "REPLACE_ME")
CLOUDINARY_API_SECRET = os.environ.get("CLOUDINARY_API_SECRET", "REPLACE_ME")


def cloudinary_configured():
    return "REPLACE_ME" not in (CLOUDINARY_CLOUD_NAME, CLOUDINARY_API_KEY, CLOUDINARY_API_SECRET)


def upload_to_cloudinary(file_storage):
    if not cloudinary_configured():
        return None
    try:
        timestamp = str(int(time.time()))
        signature = hashlib.sha1(
            f"timestamp={timestamp}{CLOUDINARY_API_SECRET}".encode("utf-8")
        ).hexdigest()
        resp = requests.post(
            f"https://api.cloudinary.com/v1_1/{CLOUDINARY_CLOUD_NAME}/image/upload",
            data={"api_key": CLOUDINARY_API_KEY, "timestamp": timestamp, "signature": signature},
            files={"file": (file_storage.filename, file_storage.stream, file_storage.mimetype)},
            timeout=20,
        )
        data = resp.json()
        return data.get("secure_url")
    except Exception:
        return None


ALLOWED_VIDEO_EXT = {"mp4", "mov", "webm", "m4v"}
ALLOWED_FILE_EXT = {"pdf", "doc", "docx", "xls", "xlsx", "txt"}


def upload_video_to_cloudinary(file_storage):
    if not cloudinary_configured():
        return None
    try:
        timestamp = str(int(time.time()))
        signature = hashlib.sha1(
            f"timestamp={timestamp}{CLOUDINARY_API_SECRET}".encode("utf-8")
        ).hexdigest()
        resp = requests.post(
            f"https://api.cloudinary.com/v1_1/{CLOUDINARY_CLOUD_NAME}/video/upload",
            data={"api_key": CLOUDINARY_API_KEY, "timestamp": timestamp, "signature": signature},
            files={"file": (file_storage.filename, file_storage.stream, file_storage.mimetype)},
            timeout=60,
        )
        data = resp.json()
        return data.get("secure_url")
    except Exception:
        return None


def upload_video_media(file_storage):
    return upload_video_to_cloudinary(file_storage)


BASE_DIR = os.path.dirname(os.path.abspath(__file__))
DB_PATH = os.path.join(BASE_DIR, "andy.db")
UPLOAD_DIR = os.path.join(BASE_DIR, "static", "uploads", "hero")
os.makedirs(UPLOAD_DIR, exist_ok=True)
WORKS_UPLOAD_DIR = os.path.join(BASE_DIR, "static", "uploads", "works")
os.makedirs(WORKS_UPLOAD_DIR, exist_ok=True)
VIDEOS_UPLOAD_DIR = os.path.join(BASE_DIR, "static", "uploads", "videos")
os.makedirs(VIDEOS_UPLOAD_DIR, exist_ok=True)
PRODUCTS_UPLOAD_DIR = os.path.join(BASE_DIR, "static", "uploads", "products")
os.makedirs(PRODUCTS_UPLOAD_DIR, exist_ok=True)
ATTACHMENTS_UPLOAD_DIR = os.path.join(BASE_DIR, "static", "uploads", "attachments")
os.makedirs(ATTACHMENTS_UPLOAD_DIR, exist_ok=True)
AVATARS_UPLOAD_DIR = os.path.join(BASE_DIR, "static", "uploads", "avatars")
os.makedirs(AVATARS_UPLOAD_DIR, exist_ok=True)
MEASUREMENTS_UPLOAD_DIR = os.path.join(BASE_DIR, "static", "uploads", "measurements")
os.makedirs(MEASUREMENTS_UPLOAD_DIR, exist_ok=True)
ALLOWED_PHOTO_EXT = {"jpg", "jpeg", "png", "webp"}

# ---------------------------------------------------------------------------
# CAMERA MEASUREMENT ASSISTANT — reference objects a user can use instead of
# a tape measure. Kept as simple data here (not hardcoded in JS) so the
# list can be edited or extended without touching the measurement logic.
# "Method C" (manual tape entry) is always offered too, as the spec requires.
# ---------------------------------------------------------------------------
MEASUREMENT_REFERENCES = [
    {"id": "door", "label": "Standard door width", "cm": 80},
    {"id": "a4_long", "label": "A4 paper (long side)", "cm": 29.7},
    {"id": "a4_short", "label": "A4 paper (short side)", "cm": 21.0},
    {"id": "card", "label": "Bank/ID card", "cm": 8.56},
    {"id": "custom", "label": "I have a tape measure (enter exact length)", "cm": None},
]

PAYSTACK_SECRET_KEY = "sk_test_REPLACE_WITH_YOUR_OWN_TEST_KEY"
PAYSTACK_PUBLIC_KEY = "pk_test_REPLACE_WITH_YOUR_OWN_TEST_KEY"
CONNECT_COINS_PER_NAIRA = 1
PRO_MEMBERSHIP_COST = 200  # CONNECT coins for a Pro upgrade

PHONE_PATTERN = re.compile(r"\d[\d\s\-]{5,}\d")

JOB_CATEGORIES = ["Windows", "Doors", "Partitions", "Aluminum Fabrication", "Repair", "Other"]
PRODUCT_CATEGORIES = ["Windows", "Doors", "Partitions", "Custom Solutions"]
JOB_STATUSES = ["submitted", "assigned", "in_progress", "completed", "cancelled"]

# ---------------------------------------------------------------------------
# DATABASE
# ---------------------------------------------------------------------------

class _PGCursorWrapper:
    def __init__(self, cursor):
        self._cursor = cursor
        self.lastrowid = None

    def fetchone(self):
        return self._cursor.fetchone()

    def fetchall(self):
        return self._cursor.fetchall()


class _PGConnWrapper:
    def __init__(self, pg_conn):
        self._conn = pg_conn

    def execute(self, query, params=()):
        q = query.replace("?", "%s")
        is_insert = q.strip().lower().startswith("insert into")
        if is_insert and "returning" not in q.lower():
            q = q.rstrip().rstrip(";") + " RETURNING id"
        cur = self._conn.cursor(cursor_factory=psycopg2.extras.RealDictCursor)
        cur.execute(q, params)
        wrapped = _PGCursorWrapper(cur)
        if is_insert:
            try:
                row = cur.fetchone()
                wrapped.lastrowid = row["id"] if row else None
            except Exception:
                wrapped.lastrowid = None
        return wrapped

    def executescript(self, script):
        cur = self._conn.cursor()
        cur.execute(script)

    def commit(self):
        self._conn.commit()

    def close(self):
        self._conn.close()


def get_db():
    if supabase_db_configured():
        pg_conn = psycopg2.connect(SUPABASE_DB_URL)
        return _PGConnWrapper(pg_conn)
    conn = sqlite3.connect(DB_PATH)
    conn.row_factory = sqlite3.Row
    conn.execute("PRAGMA foreign_keys = ON")
    return conn


def _add_column_if_missing(conn, table, column, coldef):
    if supabase_db_configured():
        rows = conn.execute(
            "SELECT column_name FROM information_schema.columns WHERE table_name = ?", (table,)
        ).fetchall()
        cols = [r["column_name"] for r in rows]
    else:
        cols = [r["name"] for r in conn.execute(f"PRAGMA table_info({table})").fetchall()]
    if column not in cols:
        conn.execute(f"ALTER TABLE {table} ADD COLUMN {column} {coldef}")


def init_db():
    conn = get_db()
    id_column = "SERIAL PRIMARY KEY" if supabase_db_configured() else "INTEGER PRIMARY KEY AUTOINCREMENT"
    conn.executescript(f"""
        CREATE TABLE IF NOT EXISTS users (
            id {id_column},
            name TEXT NOT NULL,
            email TEXT UNIQUE NOT NULL,
            password_hash TEXT NOT NULL,
            role TEXT NOT NULL,
            wallet INTEGER NOT NULL DEFAULT 0,
            referral_code TEXT,
            theme TEXT NOT NULL DEFAULT 'green',
            dark_mode INTEGER DEFAULT 0,
            is_pro INTEGER NOT NULL DEFAULT 0,
            created_at TEXT DEFAULT CURRENT_TIMESTAMP
        );

        CREATE TABLE IF NOT EXISTS artisans (
            id {id_column},
            user_id INTEGER NOT NULL,
            category TEXT NOT NULL DEFAULT 'Aluminum Fabrication',
            phone TEXT DEFAULT '',
            active INTEGER NOT NULL DEFAULT 1,
            rating REAL NOT NULL DEFAULT 0,
            reviews INTEGER NOT NULL DEFAULT 0,
            jobs_completed INTEGER NOT NULL DEFAULT 0,
            initials TEXT DEFAULT ''
        );

        CREATE TABLE IF NOT EXISTS site_content (
            id {id_column},
            tagline TEXT DEFAULT 'Connecting you with trusted artisans when you need them.',
            about_text TEXT DEFAULT ''
        );

        CREATE TABLE IF NOT EXISTS hero_photos (
            id {id_column},
            filename TEXT NOT NULL,
            created_at TEXT DEFAULT CURRENT_TIMESTAMP
        );

        CREATE TABLE IF NOT EXISTS work_posts (
            id {id_column},
            title TEXT NOT NULL,
            description TEXT DEFAULT '',
            created_at TEXT DEFAULT CURRENT_TIMESTAMP
        );

        CREATE TABLE IF NOT EXISTS work_photos (
            id {id_column},
            work_id INTEGER NOT NULL REFERENCES work_posts(id),
            filename TEXT NOT NULL
        );

        CREATE TABLE IF NOT EXISTS products (
            id {id_column},
            name TEXT NOT NULL,
            category TEXT NOT NULL DEFAULT 'Windows',
            description TEXT DEFAULT '',
            price INTEGER NOT NULL DEFAULT 0,
            sizes_csv TEXT DEFAULT '',
            image_filename TEXT DEFAULT '',
            created_at TEXT DEFAULT CURRENT_TIMESTAMP
        );

        CREATE TABLE IF NOT EXISTS product_orders (
            id {id_column},
            customer_id INTEGER NOT NULL,
            product_id INTEGER NOT NULL,
            size TEXT DEFAULT '',
            quantity INTEGER NOT NULL DEFAULT 1,
            amount INTEGER NOT NULL DEFAULT 0,
            status TEXT NOT NULL DEFAULT 'cart',
            created_at TEXT DEFAULT CURRENT_TIMESTAMP
        );

        CREATE TABLE IF NOT EXISTS videos (
            id {id_column},
            artisan_id INTEGER NOT NULL,
            title TEXT NOT NULL,
            rating REAL NOT NULL DEFAULT 0,
            ratings_count INTEGER NOT NULL DEFAULT 0,
            is_paid INTEGER NOT NULL DEFAULT 0,
            price INTEGER NOT NULL DEFAULT 0,
            video_url TEXT DEFAULT ''
        );

        CREATE TABLE IF NOT EXISTS video_purchases (
            video_id INTEGER NOT NULL,
            user_id INTEGER NOT NULL,
            PRIMARY KEY (video_id, user_id)
        );

        CREATE TABLE IF NOT EXISTS jobs (
            id {id_column},
            customer_id INTEGER NOT NULL,
            title TEXT NOT NULL,
            description TEXT DEFAULT '',
            category TEXT DEFAULT 'Other',
            track TEXT NOT NULL DEFAULT 'standard',
            status TEXT NOT NULL DEFAULT 'submitted',
            artisan_id INTEGER,
            amount INTEGER NOT NULL DEFAULT 0,
            created_at TEXT DEFAULT CURRENT_TIMESTAMP
        );

        CREATE TABLE IF NOT EXISTS job_attachments (
            id {id_column},
            job_id INTEGER NOT NULL REFERENCES jobs(id),
            filename TEXT NOT NULL,
            kind TEXT NOT NULL DEFAULT 'image'
        );

        CREATE TABLE IF NOT EXISTS messages (
            id {id_column},
            job_id INTEGER NOT NULL REFERENCES jobs(id),
            sender_id INTEGER NOT NULL,
            sender_role TEXT NOT NULL,
            text TEXT DEFAULT '',
            attachment_filename TEXT DEFAULT '',
            attachment_kind TEXT DEFAULT '',
            created_at TEXT DEFAULT CURRENT_TIMESTAMP
        );

        CREATE TABLE IF NOT EXISTS transactions (
            id {id_column},
            user_id INTEGER NOT NULL,
            label TEXT NOT NULL,
            amount INTEGER NOT NULL,
            created_at TEXT DEFAULT CURRENT_TIMESTAMP
        );

        CREATE TABLE IF NOT EXISTS feed_posts (
            id {id_column},
            artisan_id INTEGER,
            caption TEXT NOT NULL,
            media_type TEXT NOT NULL DEFAULT 'none',
            created_at TEXT DEFAULT CURRENT_TIMESTAMP
        );

        CREATE TABLE IF NOT EXISTS feed_likes (
            post_id INTEGER NOT NULL,
            user_id INTEGER NOT NULL,
            PRIMARY KEY (post_id, user_id)
        );
    """)
    conn.commit()

    # migrations for fields added after first release
    _add_column_if_missing(conn, "videos", "description", "TEXT DEFAULT ''")
    _add_column_if_missing(conn, "site_content", "what_offers", "TEXT DEFAULT ''")
    _add_column_if_missing(conn, "products", "video_url", "TEXT DEFAULT ''")
    _add_column_if_missing(conn, "messages", "read_by_owner", "INTEGER DEFAULT 0")
    _add_column_if_missing(conn, "messages", "read_by_customer", "INTEGER DEFAULT 1")
    _add_column_if_missing(conn, "users", "has_seen_guide", "INTEGER DEFAULT 0")
    _add_column_if_missing(conn, "users", "reset_token", "TEXT DEFAULT ''")
    _add_column_if_missing(conn, "users", "reset_token_expires", "TEXT DEFAULT ''")
    _add_column_if_missing(conn, "users", "avatar_filename", "TEXT DEFAULT ''")
    _add_column_if_missing(conn, "users", "bio", "TEXT DEFAULT ''")
    _add_column_if_missing(conn, "site_content", "maintenance_mode", "INTEGER DEFAULT 0")
    _add_column_if_missing(conn, "site_content", "signups_enabled", "INTEGER DEFAULT 1")
    _add_column_if_missing(conn, "site_content", "catalog_enabled", "INTEGER DEFAULT 1")
    _add_column_if_missing(conn, "site_content", "reels_enabled", "INTEGER DEFAULT 1")
    _add_column_if_missing(conn, "site_content", "tipped_videos_enabled", "INTEGER DEFAULT 1")
    _add_column_if_missing(conn, "site_content", "measure_enabled", "INTEGER DEFAULT 1")
    conn.commit()
    # new tables for Reels engagement (Like / Comment / Share / Collection)
    id_column2 = "SERIAL PRIMARY KEY" if supabase_db_configured() else "INTEGER PRIMARY KEY AUTOINCREMENT"
    conn.executescript(f"""
        CREATE TABLE IF NOT EXISTS video_likes (
            video_id INTEGER NOT NULL,
            user_id INTEGER NOT NULL,
            PRIMARY KEY (video_id, user_id)
        );
        CREATE TABLE IF NOT EXISTS video_saves (
            video_id INTEGER NOT NULL,
            user_id INTEGER NOT NULL,
            PRIMARY KEY (video_id, user_id)
        );
        CREATE TABLE IF NOT EXISTS video_comments (
            id {id_column2},
            video_id INTEGER NOT NULL,
            user_id INTEGER NOT NULL,
            text TEXT NOT NULL,
            created_at TEXT DEFAULT CURRENT_TIMESTAMP
        );
        CREATE TABLE IF NOT EXISTS reviews (
            id {id_column2},
            job_id INTEGER NOT NULL UNIQUE,
            artisan_id INTEGER NOT NULL,
            customer_id INTEGER NOT NULL,
            rating INTEGER NOT NULL,
            text TEXT DEFAULT '',
            created_at TEXT DEFAULT CURRENT_TIMESTAMP
        );
        CREATE TABLE IF NOT EXISTS measurements (
            id {id_column2},
            user_id INTEGER NOT NULL,
            job_id INTEGER,
            photo_filename TEXT DEFAULT '',
            project_name TEXT DEFAULT '',
            reference_label TEXT DEFAULT '',
            reference_cm REAL DEFAULT 0,
            width_cm REAL DEFAULT 0,
            height_cm REAL DEFAULT 0,
            confidence TEXT DEFAULT 'normal',
            notes TEXT DEFAULT '',
            created_at TEXT DEFAULT CURRENT_TIMESTAMP
        );
    """)
    conn.commit()

    owner_email = "danny@andy.local"
    owner_password = "changeme123"
    existing_owner_row = conn.execute("SELECT * FROM users WHERE email = ?", (owner_email,)).fetchone()
    if existing_owner_row is None:
        conn.execute(
            "INSERT INTO users (name, email, password_hash, role, wallet, referral_code) "
            "VALUES ('Danny', ?, ?, 'owner', 0, 'ANDY-ADMIN')",
            (owner_email, generate_password_hash(owner_password)),
        )
        conn.commit()
        print(f"[ANDY] Seeded admin/owner login -> email: {owner_email}  password: {owner_password}")
        print("[ANDY] Change this password immediately from Settings once you log in.")
    elif existing_owner_row["role"] != "owner":
        # Leftover account from an older version of this app with the same email — upgrade it in place.
        conn.execute("UPDATE users SET role = 'owner' WHERE email = ?", (owner_email,))
        conn.commit()
        print(f"[ANDY] Upgraded existing account for {owner_email} to the 'owner' role.")

    existing_content = conn.execute("SELECT COUNT(*) AS c FROM site_content").fetchone()["c"]
    if existing_content == 0:
        conn.execute("INSERT INTO site_content (tagline, about_text) VALUES (?, ?)",
                     ("Connecting you with trusted artisans when you need them.", ""))
        conn.commit()

    conn.close()

# ---------------------------------------------------------------------------
# HELPERS
# ---------------------------------------------------------------------------

def mask_phone_numbers(text):
    return PHONE_PATTERN.sub("[number hidden]", text)


def current_user():
    uid = session.get("user_id")
    if not uid:
        return None
    conn = get_db()
    user = conn.execute("SELECT * FROM users WHERE id = ?", (uid,)).fetchone()
    conn.close()
    return dict(user) if user else None


def is_owner(user):
    return bool(user and user.get("role") == "owner")


def is_artisan(user):
    return bool(user and user.get("role") == "artisan")


def is_customer(user):
    return bool(user and user.get("role") == "customer")


def get_artisan_profile(user_id):
    conn = get_db()
    row = conn.execute("SELECT * FROM artisans WHERE user_id = ?", (user_id,)).fetchone()
    conn.close()
    return dict(row) if row else None


def get_site_content():
    conn = get_db()
    row = conn.execute("SELECT * FROM site_content ORDER BY id LIMIT 1").fetchone()
    conn.close()
    return dict(row) if row else {"tagline": "", "about_text": "", "maintenance_mode": 0, "signups_enabled": 1,
                                   "catalog_enabled": 1, "reels_enabled": 1, "tipped_videos_enabled": 1, "measure_enabled": 1}


def get_hero_photos():
    conn = get_db()
    rows = conn.execute("SELECT * FROM hero_photos ORDER BY id DESC").fetchall()
    conn.close()
    return [dict(r) for r in rows]


def require_login():
    user = current_user()
    if not user:
        flash("Please log in or sign up first.", "error")
        return None
    return user


def require_owner():
    user = current_user()
    if not is_owner(user):
        flash("Admin access only.", "error")
        return None
    return user


def job_visible_to(user, job):
    """Whether this user is allowed to view/act on this job's thread."""
    if is_owner(user):
        return True
    if is_customer(user):
        return job["customer_id"] == user["id"]
    if is_artisan(user):
        tech = get_artisan_profile(user["id"])
        return tech and job["artisan_id"] == tech["id"]
    return False


def _product_dict(row):
    p = dict(row)
    p["sizes"] = [s.strip() for s in p["sizes_csv"].split(",") if s.strip()]
    return p


CATEGORY_GRAPHICS = {
    "Windows": '''<svg viewBox="0 0 200 130" xmlns="http://www.w3.org/2000/svg">
        <rect width="200" height="130" fill="#0a0f0c"/>
        <rect x="45" y="18" width="110" height="94" rx="3" fill="none" stroke="#22C55E" stroke-width="4"/>
        <line x1="100" y1="18" x2="100" y2="112" stroke="#22C55E" stroke-width="3"/>
        <line x1="45" y1="65" x2="155" y2="65" stroke="#22C55E" stroke-width="3"/>
        <rect x="50" y="23" width="45" height="37" fill="#1a3324" opacity="0.7"/>
        <rect x="105" y="23" width="45" height="37" fill="#1a3324" opacity="0.5"/>
        <rect x="50" y="70" width="45" height="37" fill="#1a3324" opacity="0.5"/>
        <rect x="105" y="70" width="45" height="37" fill="#1a3324" opacity="0.7"/>
    </svg>''',
    "Doors": '''<svg viewBox="0 0 200 130" xmlns="http://www.w3.org/2000/svg">
        <rect width="200" height="130" fill="#0a0f0c"/>
        <rect x="70" y="14" width="60" height="108" rx="2" fill="#1a3324" opacity="0.6" stroke="#22C55E" stroke-width="4"/>
        <line x1="100" y1="14" x2="100" y2="122" stroke="#22C55E" stroke-width="2" opacity="0.5"/>
        <circle cx="118" cy="70" r="3.5" fill="#22C55E"/>
    </svg>''',
    "Partitions": '''<svg viewBox="0 0 200 130" xmlns="http://www.w3.org/2000/svg">
        <rect width="200" height="130" fill="#0a0f0c"/>
        <rect x="35" y="16" width="32" height="100" fill="#1a3324" opacity="0.5" stroke="#22C55E" stroke-width="3"/>
        <rect x="75" y="16" width="32" height="100" fill="#1a3324" opacity="0.7" stroke="#22C55E" stroke-width="3"/>
        <rect x="115" y="16" width="32" height="100" fill="#1a3324" opacity="0.5" stroke="#22C55E" stroke-width="3"/>
        <rect x="155" y="16" width="20" height="100" fill="#1a3324" opacity="0.3" stroke="#22C55E" stroke-width="2"/>
    </svg>''',
    "Custom Solutions": '''<svg viewBox="0 0 200 130" xmlns="http://www.w3.org/2000/svg">
        <rect width="200" height="130" fill="#0a0f0c"/>
        <circle cx="100" cy="65" r="34" fill="none" stroke="#22C55E" stroke-width="4"/>
        <circle cx="100" cy="65" r="10" fill="#1a3324" stroke="#22C55E" stroke-width="3"/>
        <line x1="100" y1="20" x2="100" y2="32" stroke="#22C55E" stroke-width="4"/>
        <line x1="100" y1="98" x2="100" y2="110" stroke="#22C55E" stroke-width="4"/>
        <line x1="55" y1="65" x2="67" y2="65" stroke="#22C55E" stroke-width="4"/>
        <line x1="133" y1="65" x2="145" y2="65" stroke="#22C55E" stroke-width="4"/>
    </svg>''',
}
DEFAULT_CATEGORY_GRAPHIC = CATEGORY_GRAPHICS["Custom Solutions"]


TEMPLATES = {

"base.html": '''<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="UTF-8">
<meta name="viewport" content="width=device-width, initial-scale=1.0">
<title>{% block title %}ANDY{% endblock %}</title>
<link rel="preconnect" href="https://fonts.googleapis.com">
<link href="https://fonts.googleapis.com/css2?family=Sora:wght@600;700&family=Inter:wght@400;500;600&family=IBM+Plex+Mono:wght@500&display=swap" rel="stylesheet">
<link rel="stylesheet" href="{{ url_for('static', filename='style.css') }}">
</head>
<body class="theme-{{ user.theme if user else 'green' }} {{ 'dark-mode' if user and user.dark_mode }}">

<div class="mobile-topbar">
  <span class="logo-mark"></span>
  <span class="mobile-topbar-title">ANDY.</span>
  <a href="{{ url_for('contact_support') if (user and user.role == 'customer') else url_for('help_page') }}" class="help-icon-btn" title="Help / Customer Care">💬</a>
  <button onclick="toggleMenu()" class="hamburger-btn">☰</button>
</div>
<div class="menu-overlay" onclick="toggleMenu()"></div>

<div class="app-shell">
  <div class="sidebar" id="sidebar">
    <div class="logo"><span class="logo-mark"></span>ANDY<span>.</span></div>

    {% if user %}
      <div class="sidebar-profile">
        {% if user.avatar_filename %}
          <div class="profile-avatar sidebar-avatar" style="background-image:url('{{ user.avatar_filename|photo_url('avatars') }}');"></div>
        {% else %}
          <div class="profile-avatar profile-avatar-placeholder sidebar-avatar">{{ user.name[0]|upper }}</div>
        {% endif %}
        <span class="sidebar-profile-name">{{ user.name }}</span>
      </div>
    {% endif %}

    {% if user and user.role == 'customer' %}
      <div class="wallet-pill">🪙 {{ user.wallet }} CONNECT {% if user.is_pro %}<span class="pro-badge">PRO</span>{% endif %}</div>
    {% endif %}

    <nav>
      <a href="{{ url_for('home') }}" class="{{ 'active' if active_page == 'home' }}"><span class="icon">🏠</span><span>Home</span></a>

      {% if not user or user.role == 'customer' %}
        <div class="nav-section-label">Browse</div>
        <a href="{{ url_for('catalog') }}" class="{{ 'active' if active_page == 'catalog' }}"><span class="icon">🛒</span><span>Catalog</span></a>
        <a href="{{ url_for('works') }}" class="{{ 'active' if active_page == 'works' }}"><span class="icon">📸</span><span>Our Work</span></a>
        <a href="{{ url_for('reels') }}" class="{{ 'active' if active_page == 'reels' }}"><span class="icon">🎬</span><span>Reels</span></a>
        <a href="{{ url_for('tipped_videos') }}" class="{{ 'active' if active_page == 'tipped_videos' }}"><span class="icon">⭐</span><span>Tipped Videos</span></a>
      {% endif %}

      {% if user %}
        <div class="nav-section-label">My Account</div>
        {% if user.role == 'customer' %}
          <a href="{{ url_for('notifications_page') }}" class="{{ 'active' if active_page == 'notifications' }}"><span class="icon">🔔</span><span>Notifications</span>{% if customer_unread_count %}<span class="unread-badge">{{ customer_unread_count }}</span>{% endif %}</a>
          <a href="{{ url_for('request_service') }}" class="{{ 'active' if active_page == 'request_service' }}"><span class="icon">🛠️</span><span>Request a Service</span></a>
          <a href="{{ url_for('my_jobs') }}" class="{{ 'active' if active_page == 'my_jobs' }}"><span class="icon">📋</span><span>My Jobs</span></a>
          <a href="{{ url_for('measure_tool') }}" class="{{ 'active' if active_page == 'measure' }}"><span class="icon">📐</span><span>Measure a Window</span></a>
          <a href="{{ url_for('measurement_history') }}" class="{{ 'active' if active_page == 'measure_history' }}"><span class="icon">📏</span><span>Saved Measurements</span></a>
          <a href="{{ url_for('my_collection') }}" class="{{ 'active' if active_page == 'my_collection' }}"><span class="icon">💚</span><span>My Collection</span></a>
          <a href="{{ url_for('wallet') }}" class="{{ 'active' if active_page == 'wallet' }}"><span class="icon">👛</span><span>Wallet</span></a>
          <a href="{{ url_for('cart') }}" class="{{ 'active' if active_page == 'cart' }}"><span class="icon">🧺</span><span>My Cart</span></a>
          <a href="{{ url_for('pro_page') }}" class="{{ 'active' if active_page == 'pro' }}"><span class="icon">⭐</span><span>Go Pro</span></a>
        {% elif user.role == 'artisan' %}
          <a href="{{ url_for('artisan_jobs') }}" class="{{ 'active' if active_page == 'artisan_jobs' }}"><span class="icon">📋</span><span>My Assigned Jobs</span></a>
          <a href="{{ url_for('measure_tool') }}" class="{{ 'active' if active_page == 'measure' }}"><span class="icon">📐</span><span>Measure a Window</span></a>
          <a href="{{ url_for('measurement_history') }}" class="{{ 'active' if active_page == 'measure_history' }}"><span class="icon">📏</span><span>Saved Measurements</span></a>
          <a href="{{ url_for('dashboard') }}" class="{{ 'active' if active_page == 'dashboard' }}"><span class="icon">📊</span><span>Dashboard</span></a>
        {% elif user.role == 'owner' %}
          <a href="{{ url_for('admin_dashboard') }}" class="{{ 'active' if active_page == 'admin_dashboard' }}"><span class="icon">📊</span><span>Admin Overview</span></a>
          <a href="{{ url_for('admin_chats') }}" class="{{ 'active' if active_page == 'admin_chats' }}"><span class="icon">💬</span><span>Chats</span>{% if admin_unread_count %}<span class="unread-badge">{{ admin_unread_count }}</span>{% endif %}</a>
          <a href="{{ url_for('admin_artisans') }}" class="{{ 'active' if active_page == 'admin_artisans' }}"><span class="icon">🧑‍🔧</span><span>Artisans</span></a>
          <a href="{{ url_for('admin_jobs') }}" class="{{ 'active' if active_page == 'admin_jobs' }}"><span class="icon">📋</span><span>All Jobs</span></a>
          <a href="{{ url_for('dashboard_catalog') }}" class="{{ 'active' if active_page == 'dashboard_catalog' }}"><span class="icon">🛒</span><span>Manage Catalog</span></a>
          <a href="{{ url_for('admin_site') }}" class="{{ 'active' if active_page == 'admin_site' }}"><span class="icon">🖼️</span><span>Site Content</span></a>
          <a href="{{ url_for('admin_controls') }}" class="{{ 'active' if active_page == 'admin_controls' }}"><span class="icon">🎛️</span><span>Site Controls</span></a>
          <a href="{{ url_for('admin_learning') }}" class="{{ 'active' if active_page == 'admin_learning' }}"><span class="icon">📚</span><span>Upload Tips Videos</span></a>
        {% endif %}
      {% endif %}
    </nav>

    <div class="bottom-links">
      <a href="{{ url_for('about') }}" class="{{ 'active' if active_page == 'about' }}"><span class="icon">ℹ️</span><span>About Andy</span></a>
      {% if user and user.role == 'customer' %}
        <a href="{{ url_for('contact_support') }}"><span class="icon">💬</span><span>Contact Andy</span></a>
      {% endif %}
      {% if user %}
        <a href="{{ url_for('settings') }}" class="{{ 'active' if active_page == 'settings' }}"><span class="icon">⚙️</span><span>Settings</span></a>
        <a href="{{ url_for('logout') }}"><span class="icon">🚪</span><span>Logout</span></a>
      {% else %}
        <button onclick="openAuth()"><span class="icon">🔑</span><span>Login / Sign up</span></button>
      {% endif %}
    </div>
  </div>

  <div class="content-area">
    <main>
      {% with messages = get_flashed_messages(with_categories=true) %}
        {% if messages %}
          {% for category, message in messages %}
            <div class="flash flash-{{ category }}">{{ message }}</div>
          {% endfor %}
        {% endif %}
      {% endwith %}

      {% block content %}{% endblock %}
    </main>
  </div>
</div>

<nav class="bottom-tabs">
  {% if user and user.role == 'artisan' %}
    <a href="{{ url_for('home') }}" class="{{ 'active' if active_page == 'home' }}"><span>🏠</span>Home</a>
    <a href="{{ url_for('artisan_jobs') }}" class="{{ 'active' if active_page == 'artisan_jobs' }}"><span>📋</span>Jobs</a>
    <a href="{{ url_for('catalog') }}" class="{{ 'active' if active_page == 'catalog' }}"><span>🛒</span>Catalog</a>
    <button onclick="toggleMenu()"><span>⚙️</span>More</button>
  {% elif user and user.role == 'owner' %}
    <a href="{{ url_for('home') }}" class="{{ 'active' if active_page == 'home' }}"><span>🏠</span>Home</a>
    <a href="{{ url_for('admin_chats') }}" class="{{ 'active' if active_page == 'admin_chats' }}"><span>💬</span>Chats{% if admin_unread_count %}<span class="unread-badge" style="position:absolute;margin-left:2px;">{{ admin_unread_count }}</span>{% endif %}</a>
    <a href="{{ url_for('admin_jobs') }}" class="{{ 'active' if active_page == 'admin_jobs' }}"><span>📋</span>Jobs</a>
    <a href="{{ url_for('admin_artisans') }}" class="{{ 'active' if active_page == 'admin_artisans' }}"><span>🧑‍🔧</span>Techs</a>
    <button onclick="toggleMenu()"><span>⚙️</span>More</button>
  {% else %}
    <a href="{{ url_for('home') }}" class="{{ 'active' if active_page == 'home' }}"><span>🏠</span>Home</a>
    <a href="{{ url_for('reels') }}" class="{{ 'active' if active_page == 'reels' }}"><span>🎬</span>Reels</a>
    <a href="{{ url_for('catalog') }}" class="{{ 'active' if active_page == 'catalog' }}"><span>🛒</span>Catalogue</a>
    <a href="{{ url_for('tipped_videos') }}" class="{{ 'active' if active_page == 'tipped_videos' }}"><span>⭐</span>Tipped</a>
    {% if user %}
      <button onclick="toggleMenu()"><span>⚙️</span>More</button>
    {% else %}
      <button onclick="toggleMenu()"><span>🔑</span>Login</button>
    {% endif %}
  {% endif %}
</nav>

{% include "_auth_modal.html" %}

<script>
  function openAuth() {
    document.getElementById('authModal').classList.add('open');
  }
  function closeAuth() {
    document.getElementById('authModal').classList.remove('open');
  }
  function showStep(id) {
    ['signupForm','loginForm'].forEach(s => {
      document.getElementById(s).style.display = (s === id) ? 'block' : 'none';
    });
  }
  function toggleMenu() {
    document.body.classList.toggle('menu-open');
  }
  document.addEventListener('DOMContentLoaded', function() {
    document.querySelectorAll('.sidebar a, .sidebar button').forEach(function(el) {
      el.addEventListener('click', function() { document.body.classList.remove('menu-open'); });
    });
  });
  {% if auto_open_auth %}
    openAuth();
  {% endif %}
</script>

</body>
</html>
''',

"_auth_modal.html": '''<div class="modal-overlay" id="authModal">
  <div class="modal-box">
    <span class="close-btn" onclick="closeAuth()">&times;</span>
    <div class="modal-brand">
      <span class="logo-mark"></span>
      <span class="modal-brand-name">ANDY.</span>
    </div>

    <a href="{{ url_for('login_google') }}" class="btn btn-google" style="margin-bottom:14px;">
      <svg width="16" height="16" viewBox="0 0 48 48"><path fill="#EA4335" d="M24 9.5c3.4 0 6.4 1.2 8.8 3.5l6.6-6.6C35.3 2.5 30 0 24 0 14.6 0 6.5 5.4 2.5 13.2l7.7 6C12.1 13 17.6 9.5 24 9.5z"/><path fill="#4285F4" d="M46.5 24.5c0-1.6-.1-3.2-.4-4.7H24v9h12.6c-.5 3-2.2 5.5-4.7 7.2l7.2 5.6c4.2-3.9 6.4-9.6 6.4-17.1z"/><path fill="#FBBC05" d="M10.2 19.2A14.6 14.6 0 0 0 9.5 24c0 1.7.3 3.3.7 4.8l-7.7 6A24 24 0 0 1 0 24c0-3.9.9-7.5 2.5-10.8l7.7 6z"/><path fill="#34A853" d="M24 48c6.5 0 12-2.1 16-5.8l-7.2-5.6c-2 1.4-4.7 2.2-8.8 2.2-6.4 0-11.9-3.5-13.8-8.7l-7.7 6C6.5 42.6 14.6 48 24 48z"/></svg>
      Continue with Google
    </a>
    <div class="divider-or">or</div>

    <div id="signupForm">
      <h3 class="modal-headline">Let's get you set up 👋</h3>
      <p style="font-size:13px;color:var(--text-muted);margin-top:4px;">A free account is all it takes to request a service, chat with Andy, and start browsing.</p>
      <form class="auth-form" method="POST" action="{{ url_for('signup_customer') }}"><input type="hidden" name="csrf_token" value="{{ csrf_token() }}">
        <input type="text" name="name" placeholder="Full name" required>
        <input type="email" name="email" placeholder="Email address" required>
        <input type="password" name="password" placeholder="Create a password (min 6 chars)" required>
        <button class="btn btn-purple" type="submit">Create my account</button>
      </form>
      <p style="font-size:12px;text-align:center;margin-top:14px;color:var(--text-muted);">
        Already with us? <a href="#" style="color:var(--accent);font-weight:600;" onclick="showStep('loginForm')">Log in instead</a>
      </p>
    </div>

    <div id="loginForm" style="display:none;">
      <h3 class="modal-headline">Welcome back 🙌</h3>
      <p style="font-size:13px;color:var(--text-muted);margin-top:4px;">Good to see you again — log in to pick up where you left off.</p>
      <form class="auth-form" method="POST" action="{{ url_for('login') }}"><input type="hidden" name="csrf_token" value="{{ csrf_token() }}">
        <input type="email" name="email" placeholder="Email address" required>
        <input type="password" name="password" placeholder="Password" required>
        <button class="btn btn-purple" type="submit">Log in</button>
      </form>
      <p style="font-size:12px;text-align:center;margin-top:10px;">
        <a href="{{ url_for('forgot_password') }}" style="color:var(--text-muted);">Forgot your password?</a>
      </p>
      <p style="font-size:12px;text-align:center;margin-top:4px;color:var(--text-muted);">
        New to Andy? <a href="#" style="color:var(--accent);font-weight:600;" onclick="showStep('signupForm')">Create an account</a>
      </p>
    </div>

  </div>
</div>
''',

}


MORE_TEMPLATES_1 = {

"home.html": '''{% extends "base.html" %}
{% block content %}

<div class="hero" style="{% if hero_photos %}background-image:url('{{ hero_photos[0].filename|photo_url(\'hero\') }}');{% endif %}">
  {% if not hero_photos %}
  <div class="hero-default-bg">
    <svg width="100%" height="100%" viewBox="0 0 800 400" xmlns="http://www.w3.org/2000/svg" preserveAspectRatio="xMidYMax slice">
      <defs>
        <linearGradient id="skyG" x1="0" y1="0" x2="0" y2="1">
          <stop offset="0%" stop-color="#0a0f0c"/>
          <stop offset="100%" stop-color="#0f1a13"/>
        </linearGradient>
        <linearGradient id="glassG" x1="0" y1="0" x2="0" y2="1">
          <stop offset="0%" stop-color="#1a3324"/>
          <stop offset="100%" stop-color="#0d1a12"/>
        </linearGradient>
      </defs>
      <rect x="0" y="0" width="800" height="400" fill="url(#skyG)"/>
      <g opacity="0.9">
        <rect x="40" y="180" width="110" height="220" fill="url(#glassG)" stroke="#22C55E" stroke-opacity="0.25"/>
        <rect x="170" y="120" width="90" height="280" fill="url(#glassG)" stroke="#22C55E" stroke-opacity="0.3"/>
        <rect x="280" y="60" width="130" height="340" fill="url(#glassG)" stroke="#22C55E" stroke-opacity="0.4"/>
        <rect x="430" y="150" width="100" height="250" fill="url(#glassG)" stroke="#22C55E" stroke-opacity="0.3"/>
        <rect x="550" y="90" width="115" height="310" fill="url(#glassG)" stroke="#22C55E" stroke-opacity="0.35"/>
        <rect x="690" y="200" width="90" height="200" fill="url(#glassG)" stroke="#22C55E" stroke-opacity="0.25"/>
      </g>
      <g fill="#22C55E">
        <rect x="55" y="200" width="10" height="14" opacity="0.8"/>
        <rect x="80" y="200" width="10" height="14" opacity="0.5"/>
        <rect x="55" y="230" width="10" height="14" opacity="0.4"/>
        <rect x="105" y="230" width="10" height="14" opacity="0.7"/>
        <rect x="185" y="150" width="10" height="14" opacity="0.6"/>
        <rect x="210" y="150" width="10" height="14" opacity="0.9"/>
        <rect x="185" y="190" width="10" height="14" opacity="0.4"/>
        <rect x="230" y="190" width="10" height="14" opacity="0.7"/>
        <rect x="300" y="90" width="12" height="16" opacity="0.9"/>
        <rect x="330" y="90" width="12" height="16" opacity="0.5"/>
        <rect x="360" y="90" width="12" height="16" opacity="0.8"/>
        <rect x="300" y="130" width="12" height="16" opacity="0.5"/>
        <rect x="330" y="130" width="12" height="16" opacity="0.9"/>
        <rect x="360" y="130" width="12" height="16" opacity="0.4"/>
        <rect x="300" y="170" width="12" height="16" opacity="0.7"/>
        <rect x="330" y="170" width="12" height="16" opacity="0.4"/>
        <rect x="450" y="180" width="10" height="14" opacity="0.6"/>
        <rect x="480" y="180" width="10" height="14" opacity="0.9"/>
        <rect x="450" y="220" width="10" height="14" opacity="0.5"/>
        <rect x="570" y="120" width="11" height="15" opacity="0.8"/>
        <rect x="600" y="120" width="11" height="15" opacity="0.5"/>
        <rect x="630" y="120" width="11" height="15" opacity="0.9"/>
        <rect x="570" y="160" width="11" height="15" opacity="0.4"/>
        <rect x="600" y="160" width="11" height="15" opacity="0.7"/>
        <rect x="710" y="230" width="10" height="14" opacity="0.6"/>
        <rect x="740" y="230" width="10" height="14" opacity="0.8"/>
      </g>
    </svg>
  </div>
  {% endif %}
  <div class="hero-overlay">
    <div class="hero-name">ANDY</div>
    <div class="hero-title">{{ site.tagline }}</div>
    <div class="hero-actions">
      <a href="{{ url_for('request_service') if user else '#' }}" onclick="{{ '' if user else 'document.getElementById(\\'authModal\\').classList.add(\\'open\\');return false;' }}" class="btn btn-purple">Get Started</a>
      <a href="#how-it-works" class="btn btn-outline-light">Learn More</a>
    </div>
  </div>
</div>

<div class="section">
  <div class="section-title">What Andy Offers</div>
  <div class="info-card">
    <p>{% if site.what_offers %}{{ site.what_offers }}{% else %}Andy connects you with carefully selected, staffed artisans for your aluminum and fabrication service needs. We don't just list anyone — every artisan on Andy is personally vetted and managed, so you get dependable, trustworthy help every time.{% endif %}</p>
  </div>
</div>

<div class="section" id="how-it-works">
  <div class="section-title">How Andy Works</div>
  <div class="steps-grid">
    <div class="step-card"><div class="step-num">1</div><div class="step-title">Tell Andy what you need</div><div class="step-desc">Describe the job, add photos or files if it helps explain it.</div></div>
    <div class="step-card"><div class="step-num">2</div><div class="step-title">Andy connects you</div><div class="step-desc">We match you with the right staffed artisan for the job.</div></div>
    <div class="step-card"><div class="step-num">3</div><div class="step-title">Get the job handled</div><div class="step-desc">Your artisan takes care of the work, with Andy overseeing it.</div></div>
    <div class="step-card"><div class="step-num">4</div><div class="step-title">Larger projects</div><div class="step-desc">Sufficiently large projects can be routed to EAS, our larger-project team.</div></div>
  </div>
</div>

<div class="section">
  <div class="section-title">Our Work</div>
  {% if hero_photos %}
    <div class="ba-grid">
      {% for p in hero_photos[:4] %}
        <div class="gallery-photo" style="background-image:url('{{ p.filename|photo_url('hero') }}');"></div>
      {% endfor %}
    </div>
  {% else %}
    <div class="empty-state">Photos of completed work coming soon.</div>
  {% endif %}
</div>

{% if not user %}
<div class="section cta-section">
  <div class="section-title">Ready to get started?</div>
  <div style="display:flex;gap:10px;flex-wrap:wrap;">
    <button class="btn btn-purple" onclick="document.getElementById('authModal').classList.add('open')">Sign Up to Andy</button>
    <button class="btn btn-outline" onclick="document.getElementById('authModal').classList.add('open');showStep('loginForm')">Login to Andy</button>
  </div>
</div>
{% endif %}

{% endblock %}
''',

"about.html": '''{% extends "base.html" %}
{% block content %}

<div class="section-title">About Andy</div>
<div class="info-card">
  <p>{% if site.about_text %}{{ site.about_text }}{% else %}Andy helps customers connect with carefully selected artisans for their service needs. Our aim is to make finding reliable technical help easier, more organized, and more convenient — while building a dependable network of capable artisans.{% endif %}</p>
</div>

<div class="section">
  <div class="section-title">How we work</div>
  <div class="info-card">
    <p>Andy is not the artisan. We manage the connection between customers and our staffed artisan network. Artisans join Andy only by invitation — we personally select and manage everyone on the platform to keep quality high and dependable.</p>
  </div>
</div>

{% endblock %}
''',

"request_service.html": '''{% extends "base.html" %}
{% block content %}

<div class="section-title">🛠️ Request a Service</div>
<p style="font-size:13px;color:var(--text-muted);margin-bottom:16px;">Tell Andy what you need. You can add photos or files to help explain the job.</p>

<form method="POST" action="{{ url_for('request_service') }}" enctype="multipart/form-data" class="auth-form post-composer"><input type="hidden" name="csrf_token" value="{{ csrf_token() }}">
  <input type="text" name="title" placeholder="Short title (e.g. 'Aluminum window installation')" required>
  <select name="category" required>
    {% for c in categories %}<option value="{{ c }}">{{ c }}</option>{% endfor %}
  </select>
  <textarea name="description" placeholder="Describe what you need done..." rows="4" required></textarea>
  <label style="font-size:12px;color:var(--text-muted);">Attach photos or files (optional)</label>
  <input type="file" name="attachments" multiple>
  <button class="btn btn-purple" type="submit">Submit Request</button>
</form>

{% endblock %}
''',

"my_jobs.html": '''{% extends "base.html" %}
{% block content %}

<div class="section-title">📋 My Jobs</div>

{% for j in jobs %}
  <a href="{{ url_for('job_thread', job_id=j.id) }}">
    <div class="job-card">
      <div class="job-title">{{ j.title }}</div>
      <div class="job-meta">{{ j.category }} · <span class="status-badge status-{{ j.status }}">{{ j.status.replace('_',' ')|title }}</span> {% if j.track == 'eas' %}<span class="eas-badge">EAS</span>{% endif %}</div>
      <div class="job-desc">{{ j.description[:120] }}{% if j.description|length > 120 %}...{% endif %}</div>
    </div>
  </a>
{% endfor %}

{% if not jobs %}
  <div class="empty-state">No requests yet. <a href="{{ url_for('request_service') }}" style="color:var(--accent);font-weight:600;">Request a service</a> to get started.</div>
{% endif %}

{% endblock %}
''',

"job_thread.html": '''{% extends "base.html" %}
{% block content %}

<div class="section-title">{{ job.title }}</div>
<div class="job-card" style="margin-bottom:16px;">
  <div class="job-meta">
    {{ job.category }} ·
    <span class="status-badge status-{{ job.status }}">{{ job.status.replace('_',' ')|title }}</span>
    {% if job.track == 'eas' %}<span class="eas-badge">EAS</span>{% endif %}
    {% if job.amount %} · ₦{{ "{:,}".format(job.amount) }}{% endif %}
  </div>
  <div class="job-desc">{{ job.description }}</div>
  {% if attachments %}
    <div class="ba-grid" style="margin-top:10px;">
      {% for a in attachments %}
        {% if a.kind == 'image' %}
          <div class="gallery-photo" style="background-image:url('{{ a.filename|photo_url('attachments') }}');"></div>
        {% else %}
          <a href="{{ a.filename|photo_url('attachments') }}" target="_blank" class="file-chip">📎 {{ a.filename.split('_', 1)[-1] }}</a>
        {% endif %}
      {% endfor %}
    </div>
  {% endif %}
  <div style="font-size:12px;color:var(--text-muted);margin-top:8px;">Customer: {{ customer_name }}{% if artisan_name %} · Artisan: {{ artisan_name }}{% endif %}</div>
</div>

{% if is_owner_view %}
  <div class="post-composer">
    <div class="section-title" style="font-size:14px;">Admin controls</div>
    <form method="POST" action="{{ url_for('admin_update_job', job_id=job.id) }}" class="auth-form"><input type="hidden" name="csrf_token" value="{{ csrf_token() }}">
      <label style="font-size:12px;color:var(--text-muted);">Assign artisan</label>
      <select name="artisan_id">
        <option value="">— Unassigned —</option>
        {% for t in artisans %}
          <option value="{{ t.id }}" {{ 'selected' if job.artisan_id == t.id }}>{{ t.name }} ({{ t.category }})</option>
        {% endfor %}
      </select>
      <label style="font-size:12px;color:var(--text-muted);">Track</label>
      <select name="track">
        <option value="standard" {{ 'selected' if job.track == 'standard' }}>Standard Andy Job</option>
        <option value="eas" {{ 'selected' if job.track == 'eas' }}>Large Project → EAS</option>
      </select>
      <label style="font-size:12px;color:var(--text-muted);">Agreed price (CONNECT)</label>
      <input type="number" name="amount" value="{{ job.amount }}">
      <button class="btn btn-purple" type="submit">Save</button>
    </form>
  </div>
{% endif %}

{% if is_customer_view and job.status == 'assigned' and job.amount and job.amount > 0 %}
  <form method="POST" action="{{ url_for('pay_for_job', job_id=job.id) }}" style="margin-bottom:16px;"><input type="hidden" name="csrf_token" value="{{ csrf_token() }}">
    <button class="btn btn-gold" type="submit" style="width:100%;">Pay ₦{{ "{:,}".format(job.amount) }} &amp; Confirm — held in escrow</button>
  </form>
{% endif %}
{% if is_customer_view and job.status == 'in_progress' %}
  <form method="POST" action="{{ url_for('complete_service_job', job_id=job.id) }}" style="margin-bottom:16px;"><input type="hidden" name="csrf_token" value="{{ csrf_token() }}">
    <button class="btn btn-teal" type="submit" style="width:100%;">✓ Mark complete &amp; release payment</button>
  </form>
{% endif %}

{% if is_customer_view and job.status == 'completed' and job.artisan_id %}
  {% if review %}
    <div class="settings-card">
      <div class="settings-card-title">Your review</div>
      <div style="margin:6px 0;">{% for i in range(review.rating) %}⭐{% endfor %}</div>
      {% if review.text %}<div style="font-size:13px;color:var(--text-muted);">{{ review.text }}</div>{% endif %}
    </div>
  {% else %}
    <div class="settings-card">
      <div class="settings-card-title" style="margin-bottom:10px;">Rate your artisan</div>
      <form method="POST" action="{{ url_for('submit_review', job_id=job.id) }}" class="auth-form"><input type="hidden" name="csrf_token" value="{{ csrf_token() }}">
        <select name="rating" required>
          <option value="5">⭐⭐⭐⭐⭐ Excellent</option>
          <option value="4">⭐⭐⭐⭐ Good</option>
          <option value="3">⭐⭐⭐ Okay</option>
          <option value="2">⭐⭐ Not great</option>
          <option value="1">⭐ Poor</option>
        </select>
        <textarea name="text" placeholder="Tell us how it went (optional)" rows="2"></textarea>
        <button class="btn btn-purple" type="submit">Submit review</button>
      </form>
    </div>
  {% endif %}
{% endif %}

<div class="chat-box">
  <div class="chat-messages">
    {% if not messages %}
      <div class="empty-state">No messages yet.</div>
    {% endif %}
    {% for m in messages %}
      <div class="msg-row {{ 'msg-row-me' if m.sender_id == user.id else 'msg-row-them' }}">
        {% if m.sender_id != user.id %}
          {% if m.sender_avatar %}
            <div class="profile-avatar msg-avatar" style="background-image:url('{{ m.sender_avatar|photo_url('avatars') }}');"></div>
          {% else %}
            <div class="profile-avatar profile-avatar-placeholder msg-avatar">{{ m.sender_name[0]|upper }}</div>
          {% endif %}
        {% endif %}
        <div class="msg {{ 'me' if m.sender_id == user.id else 'them' }}">
          <div style="font-size:10px;opacity:0.7;margin-bottom:2px;">{{ m.sender_name }} · {{ m.sender_role|title }}</div>
          {% if m.text %}{{ m.text }}{% endif %}
          {% if m.attachment_filename %}
            {% if m.attachment_kind == 'image' %}
              <div><img src="{{ m.attachment_filename|photo_url('attachments') }}" style="max-width:180px;border-radius:8px;margin-top:6px;"></div>
            {% else %}
              <div><a href="{{ m.attachment_filename|photo_url('attachments') }}" target="_blank" style="color:inherit;text-decoration:underline;">📎 attachment</a></div>
            {% endif %}
          {% endif %}
        </div>
      </div>
    {% endfor %}
  </div>
  <form class="chat-input telegram-composer" method="POST" action="{{ url_for('post_job_message', job_id=job.id) }}" enctype="multipart/form-data"><input type="hidden" name="csrf_token" value="{{ csrf_token() }}">
    <button type="button" class="attach-btn" onclick="document.getElementById('chat-file-{{ job.id }}').click()" title="Attach a file or photo">
      <svg width="18" height="18" viewBox="0 0 24 24" fill="none"><path d="M21.44 11.05l-9.19 9.19a5.5 5.5 0 01-7.78-7.78l9.19-9.19a3.5 3.5 0 014.95 4.95l-9.2 9.19a1.5 1.5 0 01-2.12-2.12l8.49-8.48" stroke="currentColor" stroke-width="1.8" stroke-linecap="round" stroke-linejoin="round"/></svg>
    </button>
    <input type="file" id="chat-file-{{ job.id }}" name="attachment" style="display:none;" onchange="document.getElementById('chat-file-label-{{ job.id }}').textContent = this.files[0] ? this.files[0].name : '';">
    <input type="text" name="text" placeholder="Type a message..." class="chat-text-input" autocomplete="off">
    <button class="send-btn" type="submit" title="Send">
      <svg width="18" height="18" viewBox="0 0 24 24" fill="none"><path d="M2 12l19-9-6 19-4.5-7.5L2 12z" fill="#22C55E"/></svg>
    </button>
  </form>
  <div id="chat-file-label-{{ job.id }}" style="font-size:11px;color:var(--text-muted);padding:4px 12px;"></div>
</div>

{% endblock %}
''',

}

MORE_TEMPLATES_2 = {

"admin_dashboard.html": '''{% extends "base.html" %}
{% block content %}

<div class="section-title">📊 Admin Overview</div>
<div class="stats-grid">
  <div class="stat-tile"><div class="stat-num">{{ stats.customers }}</div><div class="stat-label">Customers</div></div>
  <div class="stat-tile"><div class="stat-num">{{ stats.artisans }}</div><div class="stat-label">Active Artisans</div></div>
  <div class="stat-tile"><div class="stat-num">{{ stats.pending_jobs }}</div><div class="stat-label">Pending Requests</div></div>
  <div class="stat-tile"><div class="stat-num">{{ stats.eas_jobs }}</div><div class="stat-label">EAS Projects</div></div>
</div>

<div class="section">
  <div class="section-title">Newest requests</div>
  {% for j in recent_jobs %}
    <a href="{{ url_for('job_thread', job_id=j.id) }}">
      <div class="job-card">
        <div class="job-title">{{ j.title }}</div>
        <div class="job-meta">by {{ j.customer_name }} · <span class="status-badge status-{{ j.status }}">{{ j.status.replace('_',' ')|title }}</span></div>
      </div>
    </a>
  {% endfor %}
  {% if not recent_jobs %}
    <div class="empty-state">No requests yet.</div>
  {% endif %}
</div>

{% endblock %}
''',

"admin_chats.html": '''{% extends "base.html" %}
{% block content %}

<div class="section-title">💬 Chats</div>

<div class="chat-search-bar">
  <span class="chat-search-icon">🔍</span>
  <input type="text" id="chatSearchInput" placeholder="Search by name or job..." onkeyup="filterChats()">
</div>

<div id="chatList">
{% for c in conversations %}
  <a href="{{ url_for('job_thread', job_id=c.job_id) }}" class="chat-row-link" data-search="{{ (c.customer_name ~ ' ' ~ c.title)|lower }}">
    <div class="chat-row {{ 'chat-row-unread' if c.unread }}">
      {% if c.unread %}<span class="unread-dot">{{ c.unread }}</span>{% endif %}
      {% if c.customer_avatar %}
        <div class="profile-avatar chat-row-avatar" style="background-image:url('{{ c.customer_avatar|photo_url('avatars') }}');"></div>
      {% else %}
        <div class="profile-avatar profile-avatar-placeholder chat-row-avatar">{{ c.customer_name[0]|upper }}</div>
      {% endif %}
      <div class="chat-row-body">
        <div class="chat-row-top">
          <span class="chat-row-name">{{ c.customer_name }}</span>
          <span class="status-badge status-{{ c.status }}">{{ c.status.replace('_',' ')|title }}</span>
        </div>
        <div class="chat-row-job">{{ c.title }}</div>
        {% if c.last_text %}
          <div class="chat-row-preview {{ 'chat-row-preview-unread' if c.unread }}">
            {{ 'You: ' if c.last_sender_role == 'owner' else '' }}{{ c.last_text[:90] }}{% if c.last_text|length > 90 %}...{% endif %}
          </div>
        {% endif %}
      </div>
    </div>
  </a>
{% endfor %}
</div>

{% if not conversations %}
  <div class="empty-state">No conversations yet.</div>
{% endif %}

<script>
function filterChats() {
  var q = document.getElementById('chatSearchInput').value.toLowerCase();
  document.querySelectorAll('.chat-row-link').forEach(function(el) {
    el.style.display = el.getAttribute('data-search').includes(q) ? '' : 'none';
  });
}
</script>

{% endblock %}
''',

"admin_artisans.html": '''{% extends "base.html" %}
{% block content %}

<div class="section-title">🧑‍🔧 Artisans</div>
<p style="font-size:13px;color:var(--text-muted);margin-bottom:16px;">Only you can add artisans — there is no public artisan signup.</p>

<div class="post-composer">
  <form method="POST" action="{{ url_for('add_artisan') }}" class="auth-form"><input type="hidden" name="csrf_token" value="{{ csrf_token() }}">
    <input type="text" name="name" placeholder="Full name" required>
    <input type="email" name="email" placeholder="Email (their login)" required>
    <input type="password" name="password" placeholder="Temporary password (min 6 chars)" required>
    <select name="category" required>
      {% for c in categories %}<option value="{{ c }}">{{ c }}</option>{% endfor %}
    </select>
    <input type="text" name="phone" placeholder="Phone number">
    <button class="btn btn-purple" type="submit">Add artisan</button>
  </form>
</div>

<div class="section">
  {% for t in artisans %}
    <div class="job-card">
      <div class="job-title">{{ t.name }} {% if not t.active %}<span class="status-badge status-cancelled">Inactive</span>{% endif %}</div>
      <div class="job-meta">{{ t.category }} · {{ t.email }} · {{ t.phone }} · ★ {{ t.rating }} ({{ t.reviews }}) · {{ t.jobs_completed }} jobs done</div>
      {% if t.recent_reviews %}
        <div style="margin:8px 0;">
          {% for r in t.recent_reviews %}
            <div style="font-size:12px;color:var(--text-muted);margin-bottom:4px;">
              {% for i in range(r.rating) %}⭐{% endfor %} — {{ r.customer_name }}{% if r.text %}: {{ r.text }}{% endif %}
            </div>
          {% endfor %}
        </div>
      {% endif %}
      <form method="POST" action="{{ url_for('toggle_artisan', artisan_id=t.id) }}"><input type="hidden" name="csrf_token" value="{{ csrf_token() }}">
        <button class="btn btn-outline" type="submit" style="font-size:11px;padding:6px 10px;">{{ 'Deactivate' if t.active else 'Activate' }}</button>
      </form>
    </div>
  {% endfor %}
  {% if not artisans %}
    <div class="empty-state">No artisans added yet.</div>
  {% endif %}
</div>

{% endblock %}
''',

"admin_learning.html": '''{% extends "base.html" %}
{% block content %}

<div class="section-title">📚 Upload Learning Center Content</div>
<p style="font-size:13px;color:var(--text-muted);margin-bottom:16px;">Posted as "Andy Team" — visible to everyone in the Learning Center.</p>

<div class="section">
  <div class="section-title" style="font-size:14px;">Upload a how-to clip (free)</div>
  <form method="POST" action="{{ url_for('upload_clip') }}" enctype="multipart/form-data" class="auth-form" style="max-width:340px;"><input type="hidden" name="csrf_token" value="{{ csrf_token() }}">
    <input type="text" name="title" placeholder="e.g. 'How to fix a stuck lock'" required>
    <textarea name="description" placeholder="Short description (optional)" rows="2"></textarea>
    <input type="file" name="video" accept=".mp4,.mov,.webm,.m4v">
    <button class="btn btn-purple" type="submit">Upload</button>
  </form>
</div>

<div class="section">
  <div class="section-title" style="font-size:14px;">Upload a paid tips video</div>
  <p style="font-size:13px;color:var(--text-muted);">Shows as "Coming Soon" to customers until you're ready to sell it.</p>
  <form method="POST" action="{{ url_for('upload_paid_clip') }}" enctype="multipart/form-data" class="auth-form" style="max-width:340px;margin-top:8px;"><input type="hidden" name="csrf_token" value="{{ csrf_token() }}">
    <input type="text" name="title" placeholder="Video title" required>
    <textarea name="description" placeholder="Short description (optional)" rows="2"></textarea>
    <input type="number" name="price" placeholder="Price in CONNECT" required>
    <input type="file" name="video" accept=".mp4,.mov,.webm,.m4v">
    <button class="btn btn-gold" type="submit">Upload paid clip</button>
  </form>
</div>

<div class="section">
  <div class="section-title" style="font-size:14px;">Your uploads</div>
  <div class="video-grid">
    {% for v in videos %}
      <div class="video-card">
        {% if v.video_url %}
          <video class="video-thumb" style="width:100%;object-fit:cover;" controls muted src="{{ v.video_url|photo_url('videos') }}"></video>
        {% else %}
          <div class="video-thumb">{{ '⏳' if v.is_paid else '▶' }}</div>
        {% endif %}
        <div class="video-info">
          <div class="video-title">{{ v.title }}</div>
          {% if v.is_paid %}<div style="font-size:11px;color:var(--gold);">{{ v.price }} 🪙 (Coming Soon)</div>{% endif %}
          <form method="POST" action="{{ url_for('delete_video', video_id=v.id) }}" style="margin-top:6px;"><input type="hidden" name="csrf_token" value="{{ csrf_token() }}">
            <button class="btn btn-outline" type="submit" style="width:100%;padding:6px;font-size:11px;">Remove</button>
          </form>
        </div>
      </div>
    {% endfor %}
  </div>
  {% if not videos %}
    <div class="empty-state">No uploads yet.</div>
  {% endif %}
</div>

{% endblock %}
''',

"admin_jobs.html": '''{% extends "base.html" %}
{% block content %}

<div class="section-title">📋 All Jobs</div>

<div class="cat-filter-row">
  <a href="{{ url_for('admin_jobs') }}" class="cat-filter {{ 'active' if not active_status }}">All</a>
  {% for s in statuses %}
    <a href="{{ url_for('admin_jobs', status=s) }}" class="cat-filter {{ 'active' if active_status == s }}">{{ s.replace('_',' ')|title }}</a>
  {% endfor %}
</div>

<div class="section">
  {% for j in jobs %}
    <a href="{{ url_for('job_thread', job_id=j.id) }}">
      <div class="job-card">
        <div class="job-title">{{ j.title }} {% if j.track == 'eas' %}<span class="eas-badge">EAS</span>{% endif %}</div>
        <div class="job-meta">by {{ j.customer_name }} {% if j.artisan_name %}· assigned to {{ j.artisan_name }}{% endif %} · <span class="status-badge status-{{ j.status }}">{{ j.status.replace('_',' ')|title }}</span></div>
      </div>
    </a>
  {% endfor %}
  {% if not jobs %}
    <div class="empty-state">No jobs found.</div>
  {% endif %}
</div>

{% endblock %}
''',

"admin_site.html": '''{% extends "base.html" %}
{% block content %}

<div class="section-title">🖼️ Site Content</div>

<div class="section">
  <div class="section-title" style="font-size:14px;">Homepage text</div>
  <form method="POST" action="{{ url_for('admin_site') }}" class="auth-form" style="max-width:520px;"><input type="hidden" name="csrf_token" value="{{ csrf_token() }}">
    <label style="font-size:12px;color:var(--text-muted);">Tagline (shown in the hero)</label>
    <input type="text" name="tagline" value="{{ site.tagline }}" required>
    <label style="font-size:12px;color:var(--text-muted);">"What Andy Offers" text</label>
    <textarea name="what_offers" rows="4">{{ site.what_offers }}</textarea>
    <label style="font-size:12px;color:var(--text-muted);">About Andy text</label>
    <textarea name="about_text" rows="5">{{ site.about_text }}</textarea>
    <button class="btn btn-purple" type="submit">Save</button>
  </form>
</div>

<div class="section">
  <div class="section-title" style="font-size:14px;">Hero &amp; work photos</div>
  <form method="POST" action="{{ url_for('upload_photo') }}" enctype="multipart/form-data" class="auth-form" style="max-width:340px;"><input type="hidden" name="csrf_token" value="{{ csrf_token() }}">
    <input type="file" name="photo" accept=".jpg,.jpeg,.png,.webp" required>
    <button class="btn btn-purple" type="submit">Upload photo</button>
  </form>
  <div class="video-grid" style="margin-top:14px;">
    {% for p in hero_photos %}
      <div class="video-card">
        <div class="gallery-photo" style="height:90px;background-image:url('{{ p.filename|photo_url('hero') }}');"></div>
        <div class="video-info">
          <form method="POST" action="{{ url_for('delete_photo', photo_id=p.id) }}"><input type="hidden" name="csrf_token" value="{{ csrf_token() }}">
            <button class="btn btn-outline" type="submit" style="width:100%;padding:6px;font-size:11px;">Remove</button>
          </form>
        </div>
      </div>
    {% endfor %}
  </div>
</div>

{% endblock %}
''',

"admin_controls.html": '''{% extends "base.html" %}
{% block content %}
<div class="section-title">🎛️ Site Controls</div>
<p style="font-size:13px;color:var(--text-muted);margin-bottom:16px;">Turn features on/off for everyone, instantly.</p>
<form method="POST" action="{{ url_for('admin_controls') }}">
  <input type="hidden" name="csrf_token" value="{{ csrf_token() }}">
  {% set toggles = [('maintenance_mode','🚧 Maintenance Mode','Take the whole site offline except for you'),
                     ('signups_enabled','✍️ New Sign-ups','Let new customers create accounts'),
                     ('catalog_enabled','🛒 Catalog','Browsing, cart, and checkout'),
                     ('reels_enabled','🎬 Reels','Free how-to video feed'),
                     ('tipped_videos_enabled','⭐ Tipped Videos','The Coming Soon paid videos page'),
                     ('measure_enabled','📐 Measurement Assistant','Camera window measurement tool')] %}
  {% for key, title, sub in toggles %}
    <div class="settings-card">
      <div class="settings-card-header toggle-row">
        <div>
          <div class="settings-card-title">{{ title }}</div>
          <div class="settings-card-sub">{{ sub }}</div>
        </div>
        <label class="toggle-switch">
          <input type="checkbox" name="{{ key }}" {{ 'checked' if site.get(key) }}>
          <span class="toggle-slider"></span>
        </label>
      </div>
    </div>
  {% endfor %}
  <button class="btn btn-purple" type="submit" style="width:100%;margin-top:6px;">Save Controls</button>
</form>
{% endblock %}
''',

"artisan_jobs.html": '''{% extends "base.html" %}
{% block content %}

<div class="section-title">📋 My Assigned Jobs</div>

{% for j in jobs %}
  <a href="{{ url_for('job_thread', job_id=j.id) }}">
    <div class="job-card">
      <div class="job-title">{{ j.title }} {% if j.track == 'eas' %}<span class="eas-badge">EAS</span>{% endif %}</div>
      <div class="job-meta">for {{ j.customer_name }} · <span class="status-badge status-{{ j.status }}">{{ j.status.replace('_',' ')|title }}</span></div>
    </div>
  </a>
{% endfor %}

{% if not jobs %}
  <div class="empty-state">No jobs assigned to you yet.</div>
{% endif %}

{% endblock %}
''',

"dashboard.html": '''{% extends "base.html" %}
{% block content %}

<div class="section-title">Your dashboard</div>
<div class="job-card">
  <div class="job-title">{{ artisan.name }}</div>
  <div class="job-meta">{{ artisan.category }} · ★ {{ artisan.rating }} ({{ artisan.reviews }}) · {{ artisan.jobs_completed }} jobs done</div>
</div>

<div class="section">
  <div class="section-title">Upload a how-to clip (free)</div>
  <form method="POST" action="{{ url_for('upload_clip') }}" enctype="multipart/form-data" class="auth-form" style="max-width:340px;"><input type="hidden" name="csrf_token" value="{{ csrf_token() }}">
    <input type="text" name="title" placeholder="e.g. 'How I fix a leaking pipe'" required>
    <textarea name="description" placeholder="Short description (optional)" rows="2"></textarea>
    <input type="file" name="video" accept=".mp4,.mov,.webm,.m4v">
    <button class="btn btn-purple" type="submit">Upload</button>
  </form>
</div>

<div class="section">
  <div class="section-title">Upload a paid tips video</div>
  <p style="font-size:13px;color:var(--text-muted);">Shows as "Coming Soon" to customers until this feature goes live.</p>
  <form method="POST" action="{{ url_for('upload_paid_clip') }}" enctype="multipart/form-data" class="auth-form" style="max-width:340px;margin-top:8px;"><input type="hidden" name="csrf_token" value="{{ csrf_token() }}">
    <input type="text" name="title" placeholder="Video title" required>
    <textarea name="description" placeholder="Short description (optional)" rows="2"></textarea>
    <input type="number" name="price" placeholder="Price in CONNECT" required>
    <input type="file" name="video" accept=".mp4,.mov,.webm,.m4v">
    <button class="btn btn-gold" type="submit">Upload paid clip</button>
  </form>
</div>

<div class="section">
  <div class="section-title">Your clips</div>
  <div class="video-grid">
    {% for v in videos %}
      <div class="video-card">
        {% if v.video_url %}
          <video class="video-thumb" style="width:100%;object-fit:cover;" controls muted src="{{ v.video_url|photo_url('videos') }}"></video>
        {% else %}
          <div class="video-thumb">{{ '⏳' if v.is_paid else '▶' }}</div>
        {% endif %}
        <div class="video-info">
          <div class="video-title">{{ v.title }}</div>
          {% if v.is_paid %}<div style="font-size:11px;color:var(--gold);">{{ v.price }} 🪙 (Coming Soon)</div>{% endif %}
          <form method="POST" action="{{ url_for('delete_video', video_id=v.id) }}" style="margin-top:6px;"><input type="hidden" name="csrf_token" value="{{ csrf_token() }}">
            <button class="btn btn-outline" type="submit" style="width:100%;padding:6px;font-size:11px;">Remove</button>
          </form>
        </div>
      </div>
    {% endfor %}
  </div>
  {% if not videos %}
    <div class="empty-state">No clips uploaded yet.</div>
  {% endif %}
</div>

{% endblock %}
''',

}

MORE_TEMPLATES_3 = {

"catalog.html": '''{% extends "base.html" %}
{% block content %}

<div class="section-title">🛒 Product Catalog</div>
<p style="font-size:13px;color:var(--text-muted);margin-bottom:16px;">Standard windows, doors, and partitions — pick a size and add to cart.</p>

<div class="cat-filter-row">
  <a href="{{ url_for('catalog') }}" class="cat-filter {{ 'active' if not active_cat }}">All</a>
  {% for c in categories %}
    <a href="{{ url_for('catalog', cat=c) }}" class="cat-filter {{ 'active' if active_cat == c }}">{{ c }}</a>
  {% endfor %}
</div>

<div class="video-grid" style="margin-top:16px;">
  {% for p in products %}
    <div class="video-card product-card">
      {% if p.image_filename %}
        <div class="gallery-photo" style="height:120px;background-image:url('{{ p.image_filename|photo_url('products') }}');"></div>
      {% else %}
        <div class="category-graphic" style="height:120px;">{{ category_graphic(p.category)|safe }}</div>
      {% endif %}
      {% if p.video_url %}
        <video style="width:100%;max-height:160px;object-fit:cover;" controls muted src="{{ p.video_url|photo_url('products') }}"></video>
      {% endif %}
      <div class="video-info">
        <div class="video-title">{{ p.name }}</div>
        <div style="font-size:11px;color:var(--text-muted);margin:2px 0 6px;">{{ p.category }}</div>
        {% if p.description %}<div style="font-size:12px;color:var(--navy);margin-bottom:6px;">{{ p.description }}</div>{% endif %}
        <div class="price-range" style="margin-bottom:8px;">₦{{ "{:,}".format(p.price) }} per unit</div>
        {% if user and user.role == 'customer' %}
          <form method="POST" action="{{ url_for('add_to_cart', product_id=p.id) }}" style="display:flex;flex-direction:column;gap:6px;"><input type="hidden" name="csrf_token" value="{{ csrf_token() }}">
            {% if p.sizes %}
              <select name="size" required>
                {% for s in p.sizes %}<option value="{{ s }}">{{ s }}</option>{% endfor %}
              </select>
            {% endif %}
            <input type="number" name="quantity" value="1" min="1" style="padding:8px;border:1px solid var(--border);border-radius:8px;">
            <button class="btn btn-purple" type="submit" style="font-size:12px;">Add to Cart</button>
          </form>
        {% endif %}
      </div>
    </div>
  {% endfor %}
</div>

{% if not products %}
  <div class="empty-state">No products in the catalog yet.</div>
{% endif %}

{% endblock %}
''',

"cart.html": '''{% extends "base.html" %}
{% block content %}

<div class="section-title">🧺 My Cart</div>

{% for item in cart_items %}
  <div class="job-card">
    <div class="job-title">{{ item.name }} {% if item.size %}— {{ item.size }}{% endif %}</div>
    <div class="job-meta">Qty {{ item.quantity }} × ₦{{ "{:,}".format(item.unit_price) }} = ₦{{ "{:,}".format(item.amount) }}</div>
    <form method="POST" action="{{ url_for('remove_from_cart', order_id=item.id) }}"><input type="hidden" name="csrf_token" value="{{ csrf_token() }}">
      <button class="btn btn-outline" type="submit" style="font-size:11px;padding:6px 10px;">Remove</button>
    </form>
  </div>
{% endfor %}

{% if not cart_items %}
  <div class="empty-state">Your cart is empty. Browse the <a href="{{ url_for('catalog') }}" style="color:var(--accent);font-weight:600;">Catalog</a>.</div>
{% else %}
  <div class="wallet-card" style="margin-top:20px;">
    <div style="font-size:13px;opacity:0.8;">Total</div>
    <div class="wallet-balance">🪙 {{ total }} CONNECT</div>
    <form method="POST" action="{{ url_for('checkout_cart') }}"><input type="hidden" name="csrf_token" value="{{ csrf_token() }}">
      <button class="btn btn-gold" type="submit" style="width:100%;">Checkout — pay from wallet</button>
    </form>
  </div>
{% endif %}

{% if my_orders %}
  <div class="section">
    <div class="section-title">Order status</div>
    {% for o in my_orders %}
      <div class="job-card">
        <div class="job-title">{{ o.name }} {% if o.size %}— {{ o.size }}{% endif %}</div>
        <div class="job-meta">Qty {{ o.quantity }} · ₦{{ "{:,}".format(o.amount) }} · <b>{{ o.status }}</b></div>
      </div>
    {% endfor %}
  </div>
{% endif %}

{% endblock %}
''',

"dashboard_catalog.html": '''{% extends "base.html" %}
{% block content %}

<div class="section-title">🛒 Manage Catalog</div>

<div class="post-composer">
  <form method="POST" action="{{ url_for('add_product') }}" enctype="multipart/form-data" class="auth-form"><input type="hidden" name="csrf_token" value="{{ csrf_token() }}">
    <input type="text" name="name" placeholder="Product name" required>
    <select name="category" required>
      {% for c in categories %}<option value="{{ c }}">{{ c }}</option>{% endfor %}
    </select>
    <textarea name="description" placeholder="Short description" rows="2"></textarea>
    <input type="number" name="price" placeholder="Price in ₦ per unit" required>
    <input type="text" name="sizes" placeholder="Sizes, comma separated">
    <label style="font-size:12px;color:var(--text-muted);">Photo</label>
    <input type="file" name="image" accept=".jpg,.jpeg,.png,.webp">
    <label style="font-size:12px;color:var(--text-muted);">Demo video (optional)</label>
    <input type="file" name="video" accept=".mp4,.mov,.webm,.m4v">
    <button class="btn btn-purple" type="submit">Add product</button>
  </form>
</div>

<div class="section">
  <div class="video-grid">
    {% for p in products %}
      <div class="video-card">
        {% if p.image_filename %}
          <div class="gallery-photo" style="height:100px;background-image:url('{{ p.image_filename|photo_url('products') }}');"></div>
        {% else %}
          <div class="category-graphic" style="height:100px;">{{ category_graphic(p.category)|safe }}</div>
        {% endif %}
        <div class="video-info">
          <div class="video-title">{{ p.name }}</div>
          <div style="font-size:11px;color:var(--text-muted);">{{ p.category }} · ₦{{ "{:,}".format(p.price) }}</div>
          <form method="POST" action="{{ url_for('delete_product', product_id=p.id) }}" style="margin-top:6px;"><input type="hidden" name="csrf_token" value="{{ csrf_token() }}">
            <button class="btn btn-outline" type="submit" style="width:100%;padding:6px;font-size:11px;">Remove</button>
          </form>
        </div>
      </div>
    {% endfor %}
  </div>
  {% if not products %}
    <div class="empty-state">No products yet.</div>
  {% endif %}
</div>

<div class="section">
  <div class="section-title">Orders</div>
  {% for o in orders %}
    <div class="job-card">
      <div class="job-title">{{ o.name }} {% if o.size %}— {{ o.size }}{% endif %}</div>
      <div class="job-meta">Qty {{ o.quantity }} · ₦{{ "{:,}".format(o.amount) }} · ordered by {{ o.customer_name }} · <b>{{ o.status }}</b></div>
      {% if o.status == 'paid' %}
        <form method="POST" action="{{ url_for('fulfill_order', order_id=o.id) }}"><input type="hidden" name="csrf_token" value="{{ csrf_token() }}">
          <button class="btn btn-gold" type="submit" style="font-size:11px;padding:6px 10px;">Mark fulfilled &amp; release payment</button>
        </form>
      {% endif %}
    </div>
  {% endfor %}
  {% if not orders %}
    <div class="empty-state">No orders yet.</div>
  {% endif %}
</div>

{% endblock %}
''',

"wallet.html": '''{% extends "base.html" %}
{% block content %}

<div class="wallet-card">
  <div style="font-size:13px;opacity:0.8;">CONNECT balance</div>
  <div class="wallet-balance">🪙 {{ user.wallet }}</div>
  <form method="POST" action="{{ url_for('wallet') }}" style="display:flex;gap:8px;"><input type="hidden" name="csrf_token" value="{{ csrf_token() }}">
    <input type="number" name="amount" placeholder="Amount in ₦ to add" required style="flex:1;padding:10px;border-radius:8px;border:none;">
    <button class="btn btn-gold" type="submit">Top up via Paystack</button>
  </form>
</div>

<div class="section">
  <div class="section-title">Transaction history</div>
  {% if user.transactions %}
    {% for tx in user.transactions|reverse %}
      <div class="tx-row {{ 'positive' if tx.amount > 0 else 'negative' }}">
        <span>{{ tx.label }}</span>
        <span>{{ '+' if tx.amount > 0 else '' }}{{ tx.amount }}</span>
      </div>
    {% endfor %}
  {% else %}
    <div class="empty-state">No transactions yet.</div>
  {% endif %}
</div>

{% endblock %}
''',

"settings.html": '''{% extends "base.html" %}
{% block content %}

<div class="section-title">Settings</div>
<p style="font-size:13px;color:var(--text-muted);margin-bottom:16px;">Manage your profile, appearance, and account security.</p>

<div class="settings-card">
  <div class="settings-card-header">
    <span class="settings-icon">🙂</span>
    <div>
      <div class="settings-card-title">Profile</div>
      <div class="settings-card-sub">How others see you across Andy</div>
    </div>
  </div>
  <form method="POST" action="{{ url_for('settings') }}" enctype="multipart/form-data" class="auth-form"><input type="hidden" name="csrf_token" value="{{ csrf_token() }}">
    <input type="hidden" name="form_type" value="profile">
    <div style="display:flex;align-items:center;gap:14px;margin-bottom:4px;">
      {% if user.avatar_filename %}
        <div class="profile-avatar" style="background-image:url('{{ user.avatar_filename|photo_url('avatars') }}');"></div>
      {% else %}
        <div class="profile-avatar profile-avatar-placeholder">{{ user.name[0]|upper }}</div>
      {% endif %}
      <input type="file" name="avatar" accept=".jpg,.jpeg,.png,.webp" style="flex:1;">
    </div>
    <textarea name="bio" placeholder="Add a short bio (optional)" rows="3">{{ user.bio }}</textarea>
    <button class="btn btn-purple" type="submit">Save profile</button>
  </form>
</div>

<div class="settings-card">
  <div class="settings-card-header">
    <span class="settings-icon">🎨</span>
    <div>
      <div class="settings-card-title">Theme</div>
      <div class="settings-card-sub">Choose how Andy looks on this device</div>
    </div>
  </div>
  <form method="POST" action="{{ url_for('settings') }}"><input type="hidden" name="csrf_token" value="{{ csrf_token() }}">
    <input type="hidden" name="form_type" value="appearance">
    <label class="theme-option {{ 'selected' if not user.dark_mode }}">
      <input type="radio" name="appearance" value="light" {{ 'checked' if not user.dark_mode }} style="display:none;" onchange="this.form.submit()">
      <span class="theme-swatch" style="background:#F5F4FA;border:1px solid #ccc;"></span>Light
    </label>
    <label class="theme-option {{ 'selected' if user.dark_mode }}">
      <input type="radio" name="appearance" value="dark" {{ 'checked' if user.dark_mode }} style="display:none;" onchange="this.form.submit()">
      <span class="theme-swatch" style="background:#14161F;"></span>Dark
    </label>
  </form>
</div>

<div class="settings-card">
  <div class="settings-card-header">
    <span class="settings-icon">🔒</span>
    <div>
      <div class="settings-card-title">Security</div>
      <div class="settings-card-sub">Keep your account safe</div>
    </div>
  </div>
  <form method="POST" action="{{ url_for('settings') }}" class="auth-form" style="max-width:320px;"><input type="hidden" name="csrf_token" value="{{ csrf_token() }}">
    <input type="hidden" name="form_type" value="password">
    <input type="password" name="current_password" placeholder="Current password" required>
    <input type="password" name="new_password" placeholder="New password (min 6 chars)" required>
    <button class="btn btn-purple" type="submit">Update password</button>
  </form>
  <p style="font-size:12px;color:var(--text-muted);margin-top:14px;">
    Forgot your password? <a href="{{ url_for('forgot_password') }}" style="color:var(--accent);font-weight:600;">Reset it here</a>
  </p>
</div>

{% endblock %}
''',

"forgot_password.html": '''{% extends "base.html" %}
{% block content %}

<div class="section-title">🔒 Forgot Password</div>
<div class="info-card" style="max-width:400px;">
  <form method="POST" action="{{ url_for('forgot_password') }}" class="auth-form"><input type="hidden" name="csrf_token" value="{{ csrf_token() }}">
    <input type="email" name="email" placeholder="Your account email" required>
    <button class="btn btn-purple" type="submit">Send reset link</button>
  </form>
</div>

{% endblock %}
''',

"reset_password.html": '''{% extends "base.html" %}
{% block content %}

<div class="section-title">🔒 Reset Password</div>
<div class="info-card" style="max-width:400px;">
  <form method="POST" action="{{ url_for('reset_password', token=token) }}" class="auth-form"><input type="hidden" name="csrf_token" value="{{ csrf_token() }}">
    <input type="password" name="new_password" placeholder="New password (min 6 chars)" required>
    <button class="btn btn-purple" type="submit">Set new password</button>
  </form>
</div>

{% endblock %}
''',

"andybot_guide.html": '''{% extends "base.html" %}
{% block content %}

<div class="section-title">🤖 AndyBot Starter Guide</div>
<p style="font-size:13px;color:var(--text-muted);margin-bottom:16px;">Hi, I'm AndyBot! Here's a quick tour of the app.</p>

<div class="guide-list">
  <div class="guide-item"><b>🏠 Home</b> — Learn what Andy does, and get started requesting a service.</div>
  <div class="guide-item"><b>🎬 Reels</b> — Free how-to video clips from Andy and our artisans. Swipe through and learn quick fixes.</div>
  <div class="guide-item"><b>🛒 Catalogue</b> — Browse standard products like windows and doors, with prices and sizes, ready to order.</div>
  <div class="guide-item"><b>⭐ Tipped Videos</b> — Deeper paid tutorials from artisans (launching soon).</div>
  <div class="guide-item"><b>🤍 Like</b> — Tap the heart on a Reel to show you enjoyed it.</div>
  <div class="guide-item"><b>💬 Comment</b> — Tap the comment icon on a Reel to leave a note or question.</div>
  <div class="guide-item"><b>↗️ Share</b> — Send a Reel to a friend or copy its link.</div>
  <div class="guide-item"><b>💚 Add to Collection</b> — Save a Reel to watch again later, found under "My Collection."</div>
  <div class="guide-item"><b>💬 Live Chat</b> — Once you request a service or tap "Contact Andy," you can chat directly, with photos and files.</div>
  <div class="guide-item"><b>🔔 Notifications</b> — Find these under "My Account" — see when Andy or your artisan has replied.</div>
  <div class="guide-item"><b>💬 Help icon</b> — Tap it anytime (top of the screen) to reach Andy directly.</div>
  <div class="guide-item"><b>My section</b> — Your Notifications, Jobs, Collection, Wallet, Cart, and Settings all live here.</div>
</div>

<form method="POST" action="{{ url_for('dismiss_guide') }}" style="margin-top:20px;"><input type="hidden" name="csrf_token" value="{{ csrf_token() }}">
  <button class="btn btn-purple" type="submit">Got it — take me to Andy</button>
</form>

{% endblock %}
''',

"reels.html": '''{% extends "base.html" %}
{% block content %}

<div class="section-title">🎬 Reels</div>
<p style="font-size:13px;color:var(--text-muted);margin-bottom:16px;">Quick, free how-to clips from Andy and our artisans.</p>

<div class="reels-feed">
  {% for v in videos %}
    <div class="reel-card">
      {% if v.video_url %}
        <video class="reel-video" controls muted src="{{ v.video_url|photo_url('videos') }}"></video>
      {% else %}
        <div class="video-thumb" style="height:220px;">▶</div>
      {% endif %}
      <div class="reel-info">
        <div class="video-title">{{ v.title }}</div>
        <div style="font-size:11px;color:var(--text-muted);margin-bottom:4px;">by {{ v.artisan_name }}</div>
        {% if v.description %}<div style="font-size:12px;color:var(--navy);margin-bottom:8px;">{{ v.description }}</div>{% endif %}
        <div class="reel-actions">
          <form method="POST" action="{{ url_for('like_video', video_id=v.id) }}" style="display:inline;"><input type="hidden" name="csrf_token" value="{{ csrf_token() }}">
            <button type="submit" class="reel-action-btn {{ 'active' if v.liked_by_me }}">{{ '❤️' if v.liked_by_me else '🤍' }} {{ v.like_count }}</button>
          </form>
          <button type="button" class="reel-action-btn" onclick="document.getElementById('comments-{{ v.id }}').classList.toggle('open')">💬 {{ v.comment_count }}</button>
          <button type="button" class="reel-action-btn" onclick="shareReel('{{ v.title|replace(\"'\", \"\") }}', window.location.origin + '{{ url_for('reels') }}')">↗️ Share</button>
          <form method="POST" action="{{ url_for('save_video', video_id=v.id) }}" style="display:inline;"><input type="hidden" name="csrf_token" value="{{ csrf_token() }}">
            <button type="submit" class="reel-action-btn {{ 'active' if v.saved_by_me }}">{{ '💚' if v.saved_by_me else '🤍' }} Save</button>
          </form>
        </div>
        <div id="comments-{{ v.id }}" class="reel-comments">
          {% if user %}
          <form method="POST" action="{{ url_for('comment_video', video_id=v.id) }}" style="display:flex;gap:6px;margin-top:8px;"><input type="hidden" name="csrf_token" value="{{ csrf_token() }}">
            <input type="text" name="text" placeholder="Add a comment..." style="flex:1;padding:8px;border:1px solid var(--border);border-radius:8px;font-size:12px;">
            <button class="btn btn-purple" type="submit" style="font-size:11px;padding:8px 12px;">Post</button>
          </form>
          {% endif %}
        </div>
      </div>
    </div>
  {% endfor %}
</div>

{% if not videos %}
  <div class="empty-state">No Reels yet.</div>
{% endif %}

<script>
function shareReel(title, url) {
  if (navigator.share) {
    navigator.share({title: title, url: url}).catch(function(){});
  } else {
    navigator.clipboard.writeText(url);
    alert('Link copied!');
  }
}
</script>

{% endblock %}
''',

"tipped_videos.html": '''{% extends "base.html" %}
{% block content %}

<div class="section-title">⭐ Tipped Videos</div>
<p style="font-size:13px;color:var(--text-muted);margin-bottom:16px;">Deeper, paid how-to guidance from our artisans. This feature is launching soon.</p>

<div class="video-grid">
  {% for v in videos %}
    <div class="video-card">
      <div class="video-thumb locked">⏳</div>
      <div class="video-info">
        <div class="video-title">{{ v.title }}</div>
        <div style="font-size:11px;color:var(--text-muted);margin-bottom:4px;">by {{ v.artisan_name }}</div>
        {% if v.description %}<div style="font-size:12px;color:var(--navy);margin-bottom:6px;">{{ v.description }}</div>{% endif %}
        <div class="coming-soon-badge">⏳ Coming Soon — {{ v.price }} CONNECT</div>
      </div>
    </div>
  {% endfor %}
</div>

{% if not videos %}
  <div class="empty-state">No tipped videos yet.</div>
{% endif %}

{% endblock %}
''',

"my_collection.html": '''{% extends "base.html" %}
{% block content %}

<div class="section-title">💚 My Collection</div>

<div class="video-grid">
  {% for v in videos %}
    <div class="video-card">
      {% if v.video_url %}
        <video class="video-thumb" style="width:100%;object-fit:cover;" controls muted src="{{ v.video_url|photo_url('videos') }}"></video>
      {% else %}
        <div class="video-thumb">▶</div>
      {% endif %}
      <div class="video-info">
        <div class="video-title">{{ v.title }}</div>
        <div style="font-size:11px;color:var(--text-muted);">by {{ v.artisan_name }}</div>
        <form method="POST" action="{{ url_for('save_video', video_id=v.id) }}" style="margin-top:6px;"><input type="hidden" name="csrf_token" value="{{ csrf_token() }}">
          <button class="btn btn-outline" type="submit" style="width:100%;padding:6px;font-size:11px;">Remove from Collection</button>
        </form>
      </div>
    </div>
  {% endfor %}
</div>

{% if not videos %}
  <div class="empty-state">Nothing saved yet — tap 💚 Save on any Reel to add it here.</div>
{% endif %}

{% endblock %}
''',

"notifications.html": '''{% extends "base.html" %}
{% block content %}

<div class="section-title">🔔 Notifications</div>
<p style="font-size:13px;color:var(--text-muted);margin-bottom:16px;">Messages from Andy or your artisan that need your attention.</p>

{% for c in conversations %}
  <a href="{{ url_for('job_thread', job_id=c.job_id) }}" class="chat-row-link">
    <div class="chat-row {{ 'chat-row-unread' if c.unread }}">
      {% if c.unread %}<span class="unread-dot">{{ c.unread }}</span>{% endif %}
      <div class="profile-avatar profile-avatar-placeholder chat-row-avatar">🔔</div>
      <div class="chat-row-body">
        <div class="chat-row-top">
          <span class="chat-row-name">{{ c.title }}</span>
          <span class="status-badge status-{{ c.status }}">{{ c.status.replace('_',' ')|title }}</span>
        </div>
        {% if c.last_text %}
          <div class="chat-row-preview {{ 'chat-row-preview-unread' if c.unread }}">{{ c.last_text[:90] }}{% if c.last_text|length > 90 %}...{% endif %}</div>
        {% endif %}
      </div>
    </div>
  </a>
{% endfor %}

{% if not conversations %}
  <div class="empty-state">No notifications yet.</div>
{% endif %}

{% endblock %}
''',

"measure.html": '''{% extends "base.html" %}
{% block content %}

<div class="section-title">📐 Camera Window Measurement Assistant</div>
<p style="font-size:13px;color:var(--text-muted);margin-bottom:16px;">A quick preliminary estimate — not a replacement for a tape measure. Always confirm the real opening before fabrication.</p>

<div id="step-camera" class="measure-step">
  <div class="info-card" style="margin-bottom:14px;">
    <b>Before you take the photo:</b>
    <ol style="margin:8px 0 0 18px;padding:0;font-size:13px;line-height:1.7;">
      <li>Stand directly in front of the window, phone level.</li>
      <li>Make sure the whole opening is visible.</li>
      <li>Good lighting, avoid blur.</li>
      <li>Align the opening inside the guide frame below.</li>
    </ol>
  </div>
  <div class="camera-wrap">
    <video id="cameraFeed" autoplay playsinline muted></video>
    <div id="guideFrame" class="guide-frame"></div>
    <div id="captureFlash" class="capture-flash">✅</div>
  </div>
  <div style="display:flex;gap:10px;margin-top:12px;flex-wrap:wrap;">
    <button type="button" class="btn btn-purple" id="captureBtn" onclick="capturePhoto()">📸 Capture</button>
    <label class="btn btn-outline" style="cursor:pointer;">
      Upload a photo instead
      <input type="file" id="uploadFallback" accept="image/*" capture="environment" style="display:none;" onchange="handleUpload(event)">
    </label>
  </div>
  <p id="cameraError" style="font-size:12px;color:var(--gold);margin-top:8px;display:none;">Couldn't access your camera — use "Upload a photo instead."</p>
</div>

<div id="step-reference" class="measure-step" style="display:none;">
  <canvas id="photoCanvas"></canvas>
  <div class="info-card" style="margin-top:12px;">
    <b>Step 2 — Pick a reference</b>
    <p style="font-size:12px;color:var(--text-muted);margin-top:4px;">No tape? Use something you already have.</p>
    <select id="referenceSelect" onchange="onReferenceChange()" style="margin-top:8px;width:100%;padding:10px;border:1px solid var(--border);border-radius:8px;">
      {% for r in references %}
        <option value="{{ r.id }}" data-cm="{{ r.cm or '' }}">{{ r.label }}</option>
      {% endfor %}
    </select>
    <input type="number" id="customCm" placeholder="Exact length in cm" style="display:none;margin-top:8px;width:100%;padding:10px;border:1px solid var(--border);border-radius:8px;">
    <p id="refInstruction" style="font-size:12px;color:var(--text-muted);margin-top:10px;">Tap the two ends of your reference object in the photo above.</p>
  </div>
  <button type="button" class="btn btn-purple" id="toEdgesBtn" onclick="goToEdges()" disabled style="margin-top:10px;width:100%;">Next: Mark Window Edges</button>
</div>

<div id="step-edges" class="measure-step" style="display:none;">
  <canvas id="photoCanvas2"></canvas>
  <p id="edgeInstruction" class="info-card" style="margin-top:12px;font-size:13px;">Tap the <b>LEFT</b> edge of the window, then the <b>RIGHT</b> edge.</p>
  <button type="button" class="btn btn-purple" id="calcBtn" onclick="calculateMeasurement()" disabled style="width:100%;">Calculate</button>
</div>

<div id="step-result" class="measure-step" style="display:none;">
  <div id="confidenceBanner" class="info-card" style="display:none;background:rgba(217,166,61,0.1);border-color:var(--gold);">
    <b>⚠️ Low-confidence estimate</b>
    <p style="font-size:12px;margin-top:4px;">We couldn't confidently determine the measurement from this photo. Try again with the reference object fully visible and placed further apart.</p>
  </div>
  <div class="settings-card">
    <div class="settings-card-title">Estimated Measurement</div>
    <div style="font-size:28px;font-family:'Sora',sans-serif;font-weight:700;margin:10px 0;">
      <span id="resultWidth">0</span> cm × <span id="resultHeight">0</span> cm
    </div>
    <p style="font-size:12px;color:var(--text-muted);">These measurements are estimates based on the photo and reference scale. Confirm the actual opening dimensions before fabrication.</p>
  </div>

  <form method="POST" action="{{ url_for('save_measurement') }}" class="auth-form settings-card" id="saveForm">
    <input type="hidden" name="csrf_token" value="{{ csrf_token() }}">
    <input type="hidden" name="width_cm" id="formWidth">
    <input type="hidden" name="height_cm" id="formHeight">
    <input type="hidden" name="reference_cm" id="formRefCm">
    <input type="hidden" name="reference_label" id="formRefLabel">
    <input type="hidden" name="confidence" id="formConfidence">
    <input type="hidden" name="photo_data" id="formPhotoData">
    <input type="text" name="project_name" placeholder="Project / customer name (optional)">
    <textarea name="notes" placeholder="Notes (optional)" rows="2"></textarea>
    <div style="display:flex;gap:10px;">
      <button type="button" class="btn btn-outline" style="flex:1;" onclick="location.reload()">Measure Again</button>
      <button type="submit" class="btn btn-gold" style="flex:1;">Save Measurement</button>
    </div>
  </form>
</div>

<script>
var video = document.getElementById('cameraFeed');
var stream = null;
var capturedDataUrl = null;

navigator.mediaDevices && navigator.mediaDevices.getUserMedia({ video: { facingMode: "environment" } })
  .then(function(s) { stream = s; video.srcObject = s; })
  .catch(function() { document.getElementById('cameraError').style.display = 'block'; });

function capturePhoto() {
  var canvas = document.createElement('canvas');
  canvas.width = video.videoWidth || 640;
  canvas.height = video.videoHeight || 480;
  canvas.getContext('2d').drawImage(video, 0, 0, canvas.width, canvas.height);
  capturedDataUrl = canvas.toDataURL('image/jpeg', 0.85);
  flashCaptureSuccess();
  if (stream) { stream.getTracks().forEach(function(t){ t.stop(); }); }
  setTimeout(function() { showReferenceStep(capturedDataUrl); }, 650);
}

function handleUpload(evt) {
  var file = evt.target.files[0];
  if (!file) return;
  var reader = new FileReader();
  reader.onload = function(e) {
    capturedDataUrl = e.target.result;
    showReferenceStep(capturedDataUrl);
  };
  reader.readAsDataURL(file);
}

function flashCaptureSuccess() {
  var frame = document.getElementById('guideFrame');
  var flash = document.getElementById('captureFlash');
  frame.classList.add('guide-frame-good');
  flash.classList.add('capture-flash-show');
  setTimeout(function() {
    frame.classList.remove('guide-frame-good');
    flash.classList.remove('capture-flash-show');
  }, 600);
}

// ---- Canvas marking engine (kept isolated so it can be swapped for real
// computer-vision edge/reference detection later without touching the rest
// of this page) ----
var refPoints = [];
var edgePoints = []; // [leftX,leftY, rightX,rightY, topX,topY, bottomX,bottomY]
var imgNatural = { w: 0, h: 0 };

function drawPhotoOnCanvas(canvasEl, dataUrl, onReady) {
  var img = new Image();
  img.onload = function() {
    imgNatural.w = img.width; imgNatural.h = img.height;
    var maxW = Math.min(500, window.innerWidth - 40);
    var scale = maxW / img.width;
    canvasEl.width = maxW;
    canvasEl.height = img.height * scale;
    canvasEl._scale = scale;
    canvasEl._img = img;
    canvasEl.getContext('2d').drawImage(img, 0, 0, canvasEl.width, canvasEl.height);
    if (onReady) onReady();
  };
  img.src = dataUrl;
}

function showReferenceStep(dataUrl) {
  document.getElementById('step-camera').style.display = 'none';
  document.getElementById('step-reference').style.display = 'block';
  var canvas = document.getElementById('photoCanvas');
  drawPhotoOnCanvas(canvas, dataUrl);
  canvas.onclick = function(e) {
    if (refPoints.length >= 2) return;
    var rect = canvas.getBoundingClientRect();
    var x = e.clientX - rect.left, y = e.clientY - rect.top;
    refPoints.push({x:x, y:y});
    redrawReferenceCanvas();
    if (refPoints.length === 2) checkReferenceReady();
  };
}

function redrawReferenceCanvas() {
  var canvas = document.getElementById('photoCanvas');
  var ctx = canvas.getContext('2d');
  ctx.drawImage(canvas._img, 0, 0, canvas.width, canvas.height);
  ctx.fillStyle = '#22C55E'; ctx.strokeStyle = '#22C55E'; ctx.lineWidth = 2;
  refPoints.forEach(function(p) { ctx.beginPath(); ctx.arc(p.x, p.y, 5, 0, 7); ctx.fill(); });
  if (refPoints.length === 2) {
    ctx.beginPath(); ctx.moveTo(refPoints[0].x, refPoints[0].y); ctx.lineTo(refPoints[1].x, refPoints[1].y); ctx.stroke();
  }
}

function onReferenceChange() {
  var sel = document.getElementById('referenceSelect');
  var isCustom = sel.value === 'custom';
  document.getElementById('customCm').style.display = isCustom ? 'block' : 'none';
  checkReferenceReady();
}

function checkReferenceReady() {
  var sel = document.getElementById('referenceSelect');
  var isCustom = sel.value === 'custom';
  var cmOk = isCustom ? parseFloat(document.getElementById('customCm').value) > 0 : true;
  document.getElementById('toEdgesBtn').disabled = !(refPoints.length === 2 && cmOk);
}
document.getElementById('customCm').addEventListener('input', checkReferenceReady);

function getReferenceCm() {
  var sel = document.getElementById('referenceSelect');
  if (sel.value === 'custom') return parseFloat(document.getElementById('customCm').value) || 0;
  return parseFloat(sel.selectedOptions[0].getAttribute('data-cm')) || 0;
}
function getReferenceLabel() {
  var sel = document.getElementById('referenceSelect');
  return sel.selectedOptions[0].textContent;
}

function dist(a, b) { return Math.sqrt(Math.pow(a.x-b.x,2) + Math.pow(a.y-b.y,2)); }

function goToEdges() {
  document.getElementById('step-reference').style.display = 'none';
  document.getElementById('step-edges').style.display = 'block';
  var canvas2 = document.getElementById('photoCanvas2');
  drawPhotoOnCanvas(canvas2, capturedDataUrl, function() {
    canvas2.onclick = function(e) {
      if (edgePoints.length >= 4) return;
      var rect = canvas2.getBoundingClientRect();
      var x = e.clientX - rect.left, y = e.clientY - rect.top;
      edgePoints.push({x:x, y:y});
      redrawEdgeCanvas();
      updateEdgeInstruction();
    };
  });
}

function redrawEdgeCanvas() {
  var canvas = document.getElementById('photoCanvas2');
  var ctx = canvas.getContext('2d');
  ctx.drawImage(canvas._img, 0, 0, canvas.width, canvas.height);
  ctx.fillStyle = '#22C55E'; ctx.strokeStyle = '#22C55E'; ctx.lineWidth = 2;
  edgePoints.forEach(function(p) { ctx.beginPath(); ctx.arc(p.x, p.y, 5, 0, 7); ctx.fill(); });
  if (edgePoints.length >= 2) { ctx.beginPath(); ctx.moveTo(edgePoints[0].x, edgePoints[0].y); ctx.lineTo(edgePoints[1].x, edgePoints[1].y); ctx.stroke(); }
  if (edgePoints.length >= 4) { ctx.beginPath(); ctx.moveTo(edgePoints[2].x, edgePoints[2].y); ctx.lineTo(edgePoints[3].x, edgePoints[3].y); ctx.stroke(); }
}

function updateEdgeInstruction() {
  var msgs = [
    'Tap the <b>LEFT</b> edge of the window, then the <b>RIGHT</b> edge.',
    'Tap the <b>LEFT</b> edge of the window, then the <b>RIGHT</b> edge.',
    'Now tap the <b>TOP</b> edge, then the <b>BOTTOM</b> edge.',
    'Now tap the <b>TOP</b> edge, then the <b>BOTTOM</b> edge.',
    'Ready to calculate.'
  ];
  document.getElementById('edgeInstruction').innerHTML = msgs[edgePoints.length];
  document.getElementById('calcBtn').disabled = edgePoints.length < 4;
}

function calculateMeasurement() {
  var canvas = document.getElementById('photoCanvas');
  var refPx = dist(refPoints[0], refPoints[1]) / canvas._scale;
  var refCm = getReferenceCm();
  var scaleCmPerPx = refCm / refPx;

  var canvas2 = document.getElementById('photoCanvas2');
  var widthPx = dist(edgePoints[0], edgePoints[1]) / canvas2._scale;
  var heightPx = dist(edgePoints[2], edgePoints[3]) / canvas2._scale;

  var widthCm = widthPx * scaleCmPerPx;
  var heightCm = heightPx * scaleCmPerPx;

  var lowConfidence = (refPx < 25) || (widthPx < 15) || (heightPx < 15);

  document.getElementById('resultWidth').textContent = widthCm.toFixed(1);
  document.getElementById('resultHeight').textContent = heightCm.toFixed(1);
  document.getElementById('confidenceBanner').style.display = lowConfidence ? 'block' : 'none';

  document.getElementById('formWidth').value = widthCm.toFixed(1);
  document.getElementById('formHeight').value = heightCm.toFixed(1);
  document.getElementById('formRefCm').value = refCm;
  document.getElementById('formRefLabel').value = getReferenceLabel();
  document.getElementById('formConfidence').value = lowConfidence ? 'low' : 'normal';
  document.getElementById('formPhotoData').value = capturedDataUrl;

  document.getElementById('step-edges').style.display = 'none';
  document.getElementById('step-result').style.display = 'block';
}
</script>

{% endblock %}
''',

"measurement_history.html": '''{% extends "base.html" %}
{% block content %}

<div class="section-title">📐 Saved Measurements</div>

<div class="video-grid">
  {% for m in measurements %}
    <div class="video-card">
      {% if m.photo_filename %}
        <div class="gallery-photo" style="height:120px;background-image:url('{{ m.photo_filename|photo_url('measurements') }}');"></div>
      {% endif %}
      <div class="video-info">
        <div class="video-title">{{ m.project_name or "Untitled" }}{% if m.user_name %} — {{ m.user_name }}{% endif %}</div>
        <div style="font-size:13px;margin:4px 0;">{{ m.width_cm }} cm × {{ m.height_cm }} cm</div>
        {% if m.confidence == 'low' %}<div class="coming-soon-badge" style="background:rgba(217,166,61,0.15);">⚠️ Low confidence</div>{% endif %}
        {% if m.notes %}<div style="font-size:12px;color:var(--text-muted);margin-top:4px;">{{ m.notes }}</div>{% endif %}
      </div>
    </div>
  {% endfor %}
</div>

{% if not measurements %}
  <div class="empty-state">No measurements saved yet. <a href="{{ url_for('measure_tool') }}" style="color:var(--accent);font-weight:600;">Take one now</a>.</div>
{% endif %}

{% endblock %}
''',

"pro.html": '''{% extends "base.html" %}
{% block content %}

<div class="section-title">⭐ Andy Pro</div>
<div class="info-card">
  <p>Pro members can purchase tipped videos from our artisans — deeper, paid how-to guidance for jobs you might want to tackle yourself.</p>
</div>

{% if user.is_pro %}
  <div class="empty-state">You're already a Pro member. ⭐</div>
{% else %}
  <form method="POST" action="{{ url_for('pro_page') }}" style="margin-top:16px;"><input type="hidden" name="csrf_token" value="{{ csrf_token() }}">
    <button class="btn btn-gold" type="submit">Upgrade to Pro — {{ pro_cost }} CONNECT</button>
  </form>
{% endif %}

{% endblock %}
''',

"works.html": '''{% extends "base.html" %}
{% block content %}

<div class="section-title">📸 Our Work</div>

{% if is_owner_view %}
  <div class="post-composer">
    <form method="POST" action="{{ url_for('works') }}" enctype="multipart/form-data" class="auth-form"><input type="hidden" name="csrf_token" value="{{ csrf_token() }}">
      <input type="text" name="title" placeholder="Project title" required>
      <textarea name="description" placeholder="What was the job?" rows="2"></textarea>
      <input type="file" name="photos" accept=".jpg,.jpeg,.png,.webp" multiple>
      <button class="btn btn-purple" type="submit">Post this work</button>
    </form>
  </div>
{% endif %}

{% for w in work_posts %}
  <div class="feed-post">
    <div class="job-title" style="margin-bottom:6px;">{{ w.title }}</div>
    {% if w.description %}<div class="feed-post-caption">{{ w.description }}</div>{% endif %}
    {% if w.photos %}
      <div class="ba-grid">
        {% for ph in w.photos %}
          <div class="gallery-photo" style="background-image:url('{{ ph.filename|photo_url('works') }}');"></div>
        {% endfor %}
      </div>
    {% endif %}
    {% if is_owner_view %}
      <form method="POST" action="{{ url_for('delete_work', work_id=w.id) }}" style="margin-top:10px;"><input type="hidden" name="csrf_token" value="{{ csrf_token() }}">
        <button class="btn btn-outline" type="submit" style="font-size:11px;padding:6px 10px;">Remove</button>
      </form>
    {% endif %}
  </div>
{% endfor %}

{% if not work_posts %}
  <div class="empty-state">No completed work posted yet.</div>
{% endif %}

{% endblock %}
''',

"help.html": '''{% extends "base.html" %}
{% block content %}

<div class="section-title">Help</div>
<div class="info-card">
  <p>Log in to chat directly with Andy about anything you need help with.</p>
</div>
{% endblock %}
''',

"maintenance.html": '''<!DOCTYPE html><html><head><meta charset="UTF-8"><meta name="viewport" content="width=device-width, initial-scale=1.0"><title>ANDY — Back soon</title>
<style>body{margin:0;background:#050705;color:#fff;font-family:-apple-system,sans-serif;display:flex;align-items:center;justify-content:center;min-height:100vh;text-align:center;padding:20px;}.box{max-width:360px;}.logo{font-size:40px;margin-bottom:10px;}h1{font-size:22px;margin:10px 0;}p{color:#9ca3af;font-size:14px;line-height:1.6;}</style>
</head><body><div class="box"><div class="logo">🔺</div><h1>ANDY is taking a short break</h1><p>We are doing some maintenance right now. Please check back shortly.</p></div></body></html>
''',

}

TEMPLATES.update(MORE_TEMPLATES_1)
TEMPLATES.update(MORE_TEMPLATES_2)
TEMPLATES.update(MORE_TEMPLATES_3)

STYLE_CSS = '''
:root {
  --purple: #6C4FD6;
  --purple-dark: #5539B8;
  --navy: #1B1F3B;
  --bg: #F5F4FA;
  --border: #E1DFF0;
  --text-muted: #6B6F85;
  --teal: #2E9E7C;
  --gold: #D9A63D;
  --sidebar-bg: #1B1F3B;
  --accent: #6C4FD6;
  --accent-dark: #5539B8;
}
body.theme-teal {
  --accent: #1F8A70;
  --accent-dark: #17654F;
  --sidebar-bg: #142622;
  --gold: #D9A63D;
}
body.theme-green {
  --bg: #050705;
  --navy: #EAF5EC;
  --border: #1C2B1F;
  --text-muted: #86A18C;
  --sidebar-bg: #000000;
  --accent: #22C55E;
  --accent-dark: #16A34A;
  --gold: #22C55E;
  --teal: #22C55E;
}
body.theme-green .card,
body.theme-green .job-card,
body.theme-green .feed-post,
body.theme-green .info-card,
body.theme-green .video-card,
body.theme-green .post-composer,
body.theme-green .chat-box,
body.theme-green .referral-box,
body.theme-green .modal-box,
body.theme-green .video-thumb.locked {
  background: #0B0F0C;
  border-color: var(--border);
  color: var(--navy);
}
body.theme-green .msg.them { background: #101410; }
body.theme-green .phone-locked { background: #0B0F0C; }
body.theme-green .auth-form input,
body.theme-green .auth-form select,
body.theme-green .auth-form textarea,
body.theme-green .search-bar input {
  background: #0B0F0C;
  border-color: var(--border);
  color: var(--navy);
}
body.theme-green .theme-option { background: #0B0F0C; }
body.theme-green .close-btn { color: #86A18C; }
body.theme-green .btn-purple,
body.theme-green .btn-teal,
body.theme-green .btn-gold { color: #04140A; }
body.dark-mode {
  --bg: #14161F;
  --navy: #F2F2F7;
  --border: #2B2E3D;
  --text-muted: #9A9DB0;
  --sidebar-bg: #0D0E15;
}
body.dark-mode .card,
body.dark-mode .job-card,
body.dark-mode .feed-post,
body.dark-mode .info-card,
body.dark-mode .video-card,
body.dark-mode .post-composer,
body.dark-mode .chat-box,
body.dark-mode .referral-box,
body.dark-mode .modal-box {
  background: #1B1E2B;
  border-color: var(--border);
  color: var(--navy);
}
body.dark-mode .msg.them { background: #262A3A; }
body.dark-mode .phone-locked { background: #1B1E2B; }
body.dark-mode .auth-form input,
body.dark-mode .auth-form select,
body.dark-mode .auth-form textarea,
body.dark-mode .search-bar input {
  background: #1B1E2B;
  border-color: var(--border);
  color: var(--navy);
}
body.dark-mode .theme-option { background: #1B1E2B; }
body.dark-mode .close-btn { color: #9A9DB0; }
* { box-sizing: border-box; margin: 0; padding: 0; }
body {
  font-family: 'Inter', -apple-system, sans-serif;
  background: var(--bg);
  color: var(--navy);
}
a { text-decoration: none; color: inherit; }

.app-shell { display: flex; min-height: 100vh; }
.sidebar {
  width: 220px;
  background: var(--sidebar-bg);
  color: #fff;
  display: flex;
  flex-direction: column;
  padding: 20px 0;
  flex-shrink: 0;
}
.sidebar .logo {
  font-family: 'Sora', sans-serif;
  font-weight: 700;
  font-size: 20px;
  padding: 0 22px 20px;
}
.sidebar .logo span { color: var(--accent); }
.sidebar .logo { display: flex; align-items: center; gap: 8px; }
.logo-mark {
  display: inline-block;
  width: 0; height: 0;
  border-left: 11px solid transparent;
  border-right: 11px solid transparent;
  border-bottom: 19px solid var(--accent);
  position: relative;
}
.logo-mark::after {
  content: "";
  position: absolute;
  left: -6px; top: 7px;
  width: 12px; height: 12px;
  border: 2px solid var(--sidebar-bg);
  background: rgba(255,255,255,0.15);
}
.sidebar nav { flex: 1; display: flex; flex-direction: column; gap: 2px; }
.sidebar nav a, .sidebar nav button {
  display: flex; align-items: center; gap: 12px;
  padding: 11px 22px; color: rgba(255,255,255,0.75);
  font-size: 14px; background: none; border: none; width: 100%; text-align: left; cursor: pointer;
}
.sidebar nav a:hover, .sidebar nav button:hover { background: rgba(255,255,255,0.06); color: #fff; }
.sidebar nav a.active { background: rgba(255,255,255,0.1); color: #fff; border-left: 3px solid var(--accent); }
.nav-section-label {
  font-size: 10px;
  font-weight: 700;
  letter-spacing: 0.08em;
  text-transform: uppercase;
  color: rgba(255,255,255,0.35);
  padding: 16px 22px 6px;
}
.sidebar .icon { font-size: 16px; width: 18px; text-align: center; }
.sidebar .wallet-pill {
  margin: 10px 22px; background: rgba(255,255,255,0.08); padding: 8px 12px;
  border-radius: 10px; font-size: 13px; font-family: 'IBM Plex Mono', monospace;
}
.sidebar .bottom-links { border-top: 1px solid rgba(255,255,255,0.08); padding-top: 8px; margin-top: 8px; }

.content-area { flex: 1; min-width: 0; }
main { max-width: 900px; margin: 0 auto; padding: 28px 20px 60px; }

/* ===== Hero (personal brand) ===== */
.hero {
  position: relative;
  border-radius: 18px;
  min-height: 340px;
  background-color: var(--navy);
  background-size: cover;
  background-position: center;
  display: flex;
  align-items: flex-end;
  overflow: hidden;
}
.hero-default-bg { position: absolute; inset: 0; z-index: 0; }
.hero-default-bg svg { width: 100%; height: 100%; display: block; }
.hero-overlay {
  position: relative;
  z-index: 1;
  width: 100%;
  padding: 30px 28px;
  background: linear-gradient(0deg, rgba(10,12,26,0.88) 0%, rgba(10,12,26,0.15) 70%, transparent 100%);
  color: #fff;
}
.hero-name { font-family: 'Sora', sans-serif; font-weight: 700; font-size: 30px; }
.hero-title { font-size: 15px; color: var(--gold); font-weight: 600; margin-top: 2px; letter-spacing: 0.3px; }
.hero-actions { display: flex; gap: 10px; margin-top: 16px; flex-wrap: wrap; }

/* ===== Buttons ===== */
.btn { border: none; border-radius: 8px; padding: 10px 18px; font-size: 13px; font-weight: 600; cursor: pointer; }
.btn-purple { background: var(--accent); color: #fff; }
.btn-purple:hover { background: var(--accent-dark); }
.btn-outline { background: transparent; border: 1px solid var(--border); color: var(--navy); }
.btn-outline-light { background: transparent; border: 1px solid rgba(255,255,255,0.5); color: #fff; }
.btn-teal { background: var(--teal); color: #fff; }
.btn-gold { background: var(--gold); color: #fff; }

/* ===== Sections ===== */
.section { margin-top: 28px; }
.section-title { font-family: 'Sora', sans-serif; font-weight: 600; font-size: 16px; margin-bottom: 12px; }

.video-grid { display: grid; grid-template-columns: repeat(auto-fill, minmax(160px, 1fr)); gap: 12px; margin-top: 10px; }
.video-card { background: #fff; border: 1px solid var(--border); border-radius: 12px; overflow: hidden; }
.video-thumb { background: var(--navy); height: 90px; display: flex; align-items: center; justify-content: center; color: #fff; font-size: 24px; position: relative; }
.video-thumb.locked { background: #3a3f5c; }
.video-price-tag { position: absolute; top: 6px; right: 6px; background: var(--gold); color: #fff; font-size: 10px; padding: 2px 6px; border-radius: 6px; }
.video-info { padding: 8px 10px; }
.video-title { font-size: 12px; font-weight: 600; margin-bottom: 4px; }
.video-rating { font-size: 11px; color: var(--gold); }

.ba-grid { display: grid; grid-template-columns: 1fr 1fr; gap: 10px; margin-top: 10px; }
.gallery-photo { background-color: var(--navy); background-size: cover; background-position: center; border-radius: 10px; height: 130px; }

/* ===== Chat ===== */
.chat-box { background: #fff; border: 1px solid var(--border); border-radius: 14px; margin-top: 20px; display: flex; flex-direction: column; height: 400px; }
.chat-messages { flex: 1; overflow-y: auto; padding: 16px; display: flex; flex-direction: column; gap: 8px; }
.msg { max-width: 70%; padding: 8px 12px; border-radius: 12px; font-size: 14px; }
.msg.me { align-self: flex-end; background: var(--accent); color: #fff; }
.msg.them { align-self: flex-start; background: var(--bg); }
.msg-row { display: flex; align-items: flex-end; gap: 8px; }
.msg-row-me { justify-content: flex-end; }
.msg-row-them { justify-content: flex-start; }
.msg-avatar { width: 26px; height: 26px; font-size: 11px; flex-shrink: 0; border-width: 1px; }
.sidebar-profile { display: flex; align-items: center; gap: 10px; padding: 0 22px 14px; }
.sidebar-avatar { width: 34px; height: 34px; font-size: 14px; border-width: 1px; }
.sidebar-profile-name { color: #fff; font-size: 13px; font-weight: 600; overflow: hidden; text-overflow: ellipsis; white-space: nowrap; }
.chat-input { display: flex; gap: 8px; padding: 12px; border-top: 1px solid var(--border); align-items: center; }
.chat-input input { flex: 1; border: 1px solid var(--border); border-radius: 8px; padding: 10px 12px; font-size: 14px; }
.telegram-composer { gap: 8px; }
.chat-text-input { border-radius: 20px !important; background: var(--bg); }
.attach-btn {
  width: 38px; height: 38px; border-radius: 50%; border: none; flex-shrink: 0;
  background: var(--bg); color: var(--text-muted); display: flex; align-items: center; justify-content: center; cursor: pointer;
}
.send-btn {
  width: 38px; height: 38px; border-radius: 50%; border: none; flex-shrink: 0;
  background: #000; display: flex; align-items: center; justify-content: center; cursor: pointer;
}
.send-btn:hover { background: #1a1a1a; }
.phone-locked { font-size: 12px; color: var(--text-muted); background: var(--bg); padding: 8px 12px; border-radius: 8px; margin-top: 10px; }

/* ===== Wallet ===== */
.wallet-card { background: linear-gradient(135deg, var(--accent), var(--navy)); color: #fff; border-radius: 16px; padding: 24px; }
.wallet-balance { font-family: 'Sora', sans-serif; font-size: 32px; font-weight: 700; margin: 6px 0 16px; }
.tx-row { display: flex; justify-content: space-between; padding: 12px 0; border-bottom: 1px solid var(--border); font-size: 13px; }
.tx-row.positive { color: var(--teal); }
.tx-row.negative { color: #c0392b; }
.referral-box { background: #fff; border: 1px dashed var(--accent); border-radius: 10px; padding: 14px; margin-top: 16px; text-align: center; font-size: 13px; }

/* ===== Auth modal ===== */
.modal-overlay { display: none; position: fixed; inset: 0; background: rgba(27,31,59,0.6); align-items: center; justify-content: center; z-index: 100; }
.modal-overlay.open { display: flex; }
.modal-box { background: #fff; border-radius: 16px; padding: 26px; width: 320px; position: relative; max-height: 90vh; overflow-y: auto; }
.close-btn { position: absolute; top: 10px; right: 16px; cursor: pointer; font-size: 20px; color: #999; }
.auth-form { display: flex; flex-direction: column; gap: 10px; margin-top: 14px; }
.auth-form input, .auth-form select, .auth-form textarea { padding: 10px 12px; border: 1px solid var(--border); border-radius: 8px; font-size: 14px; font-family: inherit; }
.btn-google {
  background: #fff; color: #3c4043; border: 1px solid #dadce0;
  display: flex; align-items: center; justify-content: center; gap: 10px; width: 100%;
}
.divider-or { display: flex; align-items: center; gap: 10px; margin: 12px 0; font-size: 11px; color: var(--text-muted); }
.divider-or::before, .divider-or::after { content: ""; flex: 1; height: 1px; background: var(--border); }

.flash { padding: 10px 14px; border-radius: 8px; margin-bottom: 16px; font-size: 14px; }
.flash-error { background: #fbeaea; color: #c0392b; }
.flash-success { background: #e9f7f1; color: #1f7a52; }
.empty-state { text-align: center; padding: 40px 20px; color: var(--text-muted); font-size: 14px; }

/* ===== Workshop (feed) ===== */
.feed-post { background: #fff; border: 1px solid var(--border); border-radius: 14px; padding: 18px; margin-bottom: 14px; }
.feed-post-header { display: flex; align-items: center; gap: 10px; margin-bottom: 10px; }
.feed-post-caption { font-size: 14px; margin-bottom: 10px; line-height: 1.5; }
.feed-post-media { background: var(--navy); color: #fff; border-radius: 10px; height: 140px; display: flex; align-items: center; justify-content: center; font-size: 13px; opacity: 0.8; margin-bottom: 10px; }
.feed-actions { display: flex; gap: 16px; font-size: 13px; color: var(--text-muted); }
.feed-actions button { background: none; border: none; cursor: pointer; font-size: 13px; color: var(--text-muted); display: flex; align-items: center; gap: 4px; }
.feed-actions button.liked { color: var(--accent); font-weight: 600; }
.post-composer { background: #fff; border: 1px solid var(--border); border-radius: 14px; padding: 16px; margin-bottom: 20px; }
.avatar {
  width: 50px; height: 50px; border-radius: 12px; background: var(--navy); color: #fff;
  font-family: 'Sora', sans-serif; font-weight: 700; font-size: 16px;
  display: flex; align-items: center; justify-content: center; flex-shrink: 0; position: relative;
}

/* ===== Job vacancies ===== */
.job-card { background: #fff; border: 1px solid var(--border); border-radius: 14px; padding: 16px 18px; margin-bottom: 12px; }
.job-title { font-family: 'Sora', sans-serif; font-weight: 600; font-size: 15px; }
.job-meta { font-size: 12px; color: var(--text-muted); margin: 4px 0 8px; }
.job-desc { font-size: 13px; margin-bottom: 10px; color: var(--navy); }

/* ===== Catalog ===== */
.cat-filter-row { display: flex; gap: 8px; flex-wrap: wrap; }
.cat-filter { padding: 8px 14px; border-radius: 20px; border: 1px solid var(--border); font-size: 12px; font-weight: 600; background: #fff; }
body.dark-mode .cat-filter, body.theme-green .cat-filter { background: #0B0F0C; }
.cat-filter.active { background: var(--accent); color: #fff; border-color: var(--accent); }
.product-card select { padding: 8px; border: 1px solid var(--border); border-radius: 8px; font-size: 12px; }

/* ===== Settings ===== */
.theme-option { display: flex; align-items: center; gap: 12px; padding: 14px; border: 1px solid var(--border); border-radius: 10px; margin-bottom: 10px; cursor: pointer; }
.theme-option.selected { border-color: var(--accent); background: rgba(108,79,214,0.05); }
.theme-swatch { width: 28px; height: 28px; border-radius: 50%; }

/* ===== About ===== */
.info-card { background: #fff; border: 1px solid var(--border); border-radius: 14px; padding: 22px; line-height: 1.7; font-size: 14px; }
.stat-row { display: flex; gap: 20px; font-size: 13px; color: var(--text-muted); flex-wrap: wrap; }
.stat-row b { color: var(--navy); }

/* ===== Bottom mobile tab bar (hidden on desktop) ===== */
.bottom-tabs { display: none; }
.mobile-topbar { display: none; }
.menu-overlay { display: none; }

@media (max-width: 720px) {
  .mobile-topbar {
    display: flex;
    align-items: center;
    gap: 10px;
    position: sticky;
    top: 0;
    background: var(--sidebar-bg);
    color: #fff;
    padding: 14px 16px;
    z-index: 95;
  }
  .mobile-topbar-title { font-family: 'Sora', sans-serif; font-weight: 700; flex: 1; }
  .hamburger-btn { background: none; border: none; color: #fff; font-size: 20px; }
  .help-icon-btn { text-decoration: none; font-size: 18px; padding: 4px; }
  .sidebar {
    position: fixed;
    top: 0; left: 0; bottom: 0;
    width: 250px;
    transform: translateX(-100%);
    transition: transform 0.25s ease;
    z-index: 110;
    overflow-y: auto;
  }
  body.menu-open .sidebar { transform: translateX(0); }
  body.menu-open .menu-overlay {
    display: block;
    position: fixed;
    inset: 0;
    background: rgba(0,0,0,0.5);
    z-index: 100;
  }
  .app-shell { display: block; }
  .content-area { width: 100%; }
  main { padding: 16px 14px 90px; max-width: 100%; }
  .bottom-tabs {
    display: flex;
    position: fixed;
    bottom: 0; left: 0; right: 0;
    background: var(--sidebar-bg);
    border-top: 1px solid rgba(255,255,255,0.08);
    z-index: 90;
  }
  .bottom-tabs a, .bottom-tabs button {
    flex: 1;
    display: flex; flex-direction: column; align-items: center; gap: 2px;
    padding: 10px 0 8px;
    color: rgba(255,255,255,0.6);
    font-size: 11px;
    background: none; border: none;
  }
  .bottom-tabs a span, .bottom-tabs button span { font-size: 18px; }
  .bottom-tabs a.active { color: var(--accent); }
  .hero { min-height: 220px; border-radius: 12px; }
  .hero-overlay { padding: 18px 16px; }
  .hero-name { font-size: 22px; }
  .hero-title { font-size: 13px; }
  .hero-actions { flex-direction: column; }
  .hero-actions .btn { width: 100%; text-align: center; }
  .profile-header { flex-direction: column; align-items: flex-start; padding: 16px; }
  .video-grid { grid-template-columns: repeat(auto-fill, minmax(120px, 1fr)); }
  .ba-grid { grid-template-columns: 1fr 1fr; gap: 8px; }
  .gallery-photo { height: 100px; }
  .modal-box { width: 90vw; padding: 20px; }
  .chat-box { height: 320px; }
  .stat-row { gap: 12px; }
  .job-card, .feed-post, .info-card, .card { padding: 14px; }
}
@media (max-width: 420px) {
  .ba-grid { grid-template-columns: 1fr; }
  main { padding: 14px 10px 40px; }
  .hero-name { font-size: 19px; }
}

/* ===== New role-based components ===== */
.pro-badge { background: var(--gold); color: #fff; font-size: 9px; font-weight: 700; padding: 2px 6px; border-radius: 6px; margin-left: 6px; }
.eas-badge { background: #C0392B; color: #fff; font-size: 10px; font-weight: 700; padding: 2px 8px; border-radius: 6px; margin-left: 6px; }
.status-badge { font-size: 11px; font-weight: 600; padding: 2px 8px; border-radius: 6px; display: inline-block; }
.status-submitted { background: rgba(217,166,61,0.15); color: var(--gold); }
.status-assigned { background: rgba(108,79,214,0.15); color: var(--accent); }
.status-in_progress { background: rgba(46,158,124,0.15); color: var(--teal); }
.status-completed { background: rgba(46,158,124,0.25); color: var(--teal); }
.status-cancelled { background: rgba(192,57,43,0.15); color: #c0392b; }
.unread-badge { background: #C0392B; color: #fff; font-size: 10px; font-weight: 700; padding: 1px 7px; border-radius: 10px; margin-left: 6px; display: inline-block; }
.steps-grid { display: grid; grid-template-columns: repeat(auto-fit, minmax(180px, 1fr)); gap: 14px; margin-top: 10px; }
.step-card { background: #fff; border: 1px solid var(--border); border-radius: 14px; padding: 18px; }
body.dark-mode .step-card, body.theme-green .step-card { background: #0B0F0C; }
.step-num { width: 28px; height: 28px; border-radius: 50%; background: var(--accent); color: #fff; display: flex; align-items: center; justify-content: center; font-weight: 700; font-size: 13px; margin-bottom: 10px; }
.step-title { font-weight: 600; font-size: 14px; margin-bottom: 4px; }
.step-desc { font-size: 12px; color: var(--text-muted); }
.stats-grid { display: grid; grid-template-columns: repeat(auto-fit, minmax(130px, 1fr)); gap: 12px; }
.stat-tile { background: #fff; border: 1px solid var(--border); border-radius: 14px; padding: 18px; text-align: center; }
body.dark-mode .stat-tile, body.theme-green .stat-tile { background: #0B0F0C; }
.stat-num { font-family: 'Sora', sans-serif; font-size: 26px; font-weight: 700; color: var(--accent); }
.stat-label { font-size: 11px; color: var(--text-muted); margin-top: 4px; }
.file-chip { display: inline-block; background: var(--bg); border: 1px solid var(--border); border-radius: 8px; padding: 8px 12px; font-size: 12px; margin: 4px 4px 0 0; color: var(--navy); }
.cta-section { background: var(--sidebar-bg); color: #fff; border-radius: 16px; padding: 24px; }
.cta-section .section-title { color: #fff; }
.coming-soon-badge { display: inline-block; background: rgba(217,166,61,0.15); color: var(--gold); font-size: 11px; font-weight: 600; padding: 5px 10px; border-radius: 8px; }
.settings-card-header.toggle-row { margin-bottom: 0; }
.settings-card-header.toggle-row > div { flex: 1; }
.toggle-switch { position: relative; display: inline-block; width: 46px; height: 26px; flex-shrink: 0; }
.toggle-switch input { opacity: 0; width: 0; height: 0; }
.toggle-slider { position: absolute; cursor: pointer; inset: 0; background: var(--border); border-radius: 26px; transition: background 0.2s; }
.toggle-slider::before { position: absolute; content: ""; height: 20px; width: 20px; left: 3px; bottom: 3px; background: #fff; border-radius: 50%; transition: transform 0.2s; }
.toggle-switch input:checked + .toggle-slider { background: var(--accent); }
.toggle-switch input:checked + .toggle-slider::before { transform: translateX(20px); }
.reels-feed { display: flex; flex-direction: column; gap: 20px; max-width: 480px; margin: 0 auto; }
.reel-card { background: #fff; border: 1px solid var(--border); border-radius: 16px; overflow: hidden; }
body.dark-mode .reel-card, body.theme-green .reel-card { background: #0B0F0C; }
.reel-video { width: 100%; max-height: 420px; object-fit: cover; background: #000; display: block; }
.reel-info { padding: 12px 14px; }
.reel-actions { display: flex; gap: 14px; margin-top: 6px; }
.reel-action-btn { background: none; border: none; font-size: 13px; color: var(--text-muted); cursor: pointer; padding: 4px 0; }
.reel-action-btn.active { color: var(--accent); font-weight: 600; }
.reel-comments { display: none; }
.reel-comments.open { display: block; }
.category-graphic { border-radius: 10px; overflow: hidden; }
.category-graphic svg { width: 100%; height: 100%; display: block; }
.settings-card { background: #fff; border: 1px solid var(--border); border-radius: 14px; padding: 20px; margin-bottom: 16px; }
body.dark-mode .settings-card, body.theme-green .settings-card { background: #0B0F0C; }
.settings-card-header { display: flex; align-items: center; gap: 12px; margin-bottom: 16px; }
.settings-icon { font-size: 22px; }
.settings-card-title { font-family: 'Sora', sans-serif; font-weight: 600; font-size: 15px; }
.settings-card-sub { font-size: 12px; color: var(--text-muted); }
.profile-avatar {
  width: 56px; height: 56px; border-radius: 50%; background-size: cover; background-position: center;
  background-color: var(--navy); flex-shrink: 0; border: 2px solid var(--accent);
}
.profile-avatar-placeholder {
  display: flex; align-items: center; justify-content: center; color: #fff;
  font-family: 'Sora', sans-serif; font-weight: 700; font-size: 22px; background: var(--accent);
}
.modal-brand { display: flex; align-items: center; gap: 8px; justify-content: center; margin-bottom: 18px; }
.modal-brand-name { font-family: 'Sora', sans-serif; font-weight: 700; font-size: 18px; color: var(--navy); }
.modal-headline { font-family: 'Sora', sans-serif; font-size: 19px; font-weight: 700; }
.chat-search-bar { display: flex; align-items: center; gap: 8px; background: #fff; border: 1px solid var(--border); border-radius: 20px; padding: 10px 16px; margin-bottom: 16px; }
body.dark-mode .chat-search-bar, body.theme-green .chat-search-bar { background: #0B0F0C; }
.chat-search-bar input { flex: 1; border: none; outline: none; background: transparent; font-size: 14px; color: var(--navy); }
.chat-search-icon { font-size: 14px; opacity: 0.6; }
.chat-row-link { text-decoration: none; }
.chat-row {
  position: relative; display: flex; align-items: center; gap: 12px;
  background: #fff; border: 1px solid var(--border); border-radius: 14px; padding: 14px; margin-bottom: 10px;
}
body.dark-mode .chat-row, body.theme-green .chat-row { background: #0B0F0C; }
.chat-row-unread { border-color: var(--accent); }
.chat-row-avatar { width: 44px; height: 44px; font-size: 17px; flex-shrink: 0; border-width: 1px; }
.unread-dot {
  position: absolute; left: -6px; top: -6px;
  background: var(--accent); color: #fff; font-size: 10px; font-weight: 700;
  min-width: 18px; height: 18px; border-radius: 9px; display: flex; align-items: center; justify-content: center;
  padding: 0 4px; border: 2px solid var(--bg);
}
.chat-row-body { flex: 1; min-width: 0; }
.chat-row-top { display: flex; align-items: center; justify-content: space-between; gap: 8px; }
.chat-row-name { font-weight: 600; font-size: 14px; }
.chat-row-job { font-size: 12px; color: var(--text-muted); margin-top: 1px; }
.chat-row-preview { font-size: 12px; color: var(--text-muted); margin-top: 4px; white-space: nowrap; overflow: hidden; text-overflow: ellipsis; }
.chat-row-preview-unread { color: var(--navy); font-weight: 600; }
.measure-step canvas { width: 100%; max-width: 500px; border-radius: 12px; display: block; margin: 0 auto; cursor: crosshair; border: 1px solid var(--border); }
.camera-wrap { position: relative; max-width: 500px; margin: 0 auto; border-radius: 14px; overflow: hidden; background: #000; }
.camera-wrap video { width: 100%; display: block; }
.guide-frame {
  position: absolute; top: 15%; left: 10%; width: 80%; height: 70%;
  border: 3px dashed rgba(255,255,255,0.7); border-radius: 10px;
  transition: border-color 0.2s, background 0.2s; pointer-events: none;
}
.guide-frame-good { border-color: #22C55E; border-style: solid; background: rgba(34,197,94,0.15); }
.capture-flash {
  position: absolute; inset: 0; display: flex; align-items: center; justify-content: center;
  font-size: 56px; opacity: 0; transition: opacity 0.2s; pointer-events: none;
}
.capture-flash-show { opacity: 1; }
'''


app.jinja_loader = DictLoader(TEMPLATES)


@app.context_processor
def inject_unread_count():
    user = current_user()
    if user and is_owner(user):
        conn = get_db()
        count = conn.execute(
            "SELECT COUNT(*) AS c FROM messages WHERE sender_role != 'owner' AND read_by_owner = 0"
        ).fetchone()["c"]
        conn.close()
        return {"admin_unread_count": count, "customer_unread_count": 0}
    if user and is_customer(user):
        conn = get_db()
        count = conn.execute("""
            SELECT COUNT(*) AS c FROM messages
            JOIN jobs ON messages.job_id = jobs.id
            WHERE jobs.customer_id = ? AND messages.sender_role != 'customer' AND messages.read_by_customer = 0
        """, (user["id"],)).fetchone()["c"]
        conn.close()
        return {"admin_unread_count": 0, "customer_unread_count": count}
    return {"admin_unread_count": 0, "customer_unread_count": 0}


@app.route("/static/style.css")
def style_css():
    return Response(STYLE_CSS, mimetype="text/css")


@app.template_filter("photo_url")
def photo_url_filter(value, folder):
    if not value:
        return ""
    if value.startswith("http://") or value.startswith("https://"):
        return value
    return url_for("static", filename=f"uploads/{folder}/{value}")


@app.template_global("category_graphic")
def category_graphic(category):
    return CATEGORY_GRAPHICS.get(category, DEFAULT_CATEGORY_GRAPHIC)


class _FakeFileStorage:
    """Minimal stand-in for werkzeug's FileStorage, so a base64 photo captured
    in the browser (no real file input) can reuse the same upload pipeline
    (Cloudinary-first, local-disk fallback) as every other upload in ANDY."""
    def __init__(self, data_bytes, filename, mimetype):
        self.filename = filename
        self.mimetype = mimetype
        self.stream = io.BytesIO(data_bytes)

    def save(self, path):
        with open(path, "wb") as f:
            f.write(self.stream.getvalue())


def _save_base64_photo(data_url, upload_dir):
    """Decodes a data:image/...;base64,... string (from a <canvas> capture)
    and saves it via the normal upload pipeline. Returns stored value or ''."""
    if not data_url or "base64," not in data_url:
        return ""
    try:
        header, b64data = data_url.split("base64,", 1)
        raw = base64.b64decode(b64data)
        mimetype = header.split(":")[1].split(";")[0] if ":" in header else "image/jpeg"
        ext = mimetype.split("/")[-1] if "/" in mimetype else "jpg"
        if ext == "jpeg":
            ext = "jpg"
        fake = _FakeFileStorage(raw, f"capture.{ext}", mimetype)
        stored, kind = _save_attachment(fake, upload_dir)
        return stored if kind == "image" else ""
    except Exception:
        return ""


def _save_attachment(file_storage, upload_dir, allow_video=False):
    """Saves an image, doc, or video attachment. Returns (stored_value, kind)
    or (None, None) if no usable file was given."""
    if not file_storage or file_storage.filename == "":
        return None, None
    ext = file_storage.filename.rsplit(".", 1)[-1].lower() if "." in file_storage.filename else ""
    if ext in ALLOWED_PHOTO_EXT:
        cloud_url = upload_media(file_storage)
        if cloud_url:
            return cloud_url, "image"
        safe_name = f"{int(time.time()*1000)}_{secure_filename(file_storage.filename)}"
        file_storage.save(os.path.join(upload_dir, safe_name))
        return safe_name, "image"
    if allow_video and ext in ALLOWED_VIDEO_EXT:
        cloud_url = upload_video_media(file_storage)
        if cloud_url:
            return cloud_url, "video"
        safe_name = f"{int(time.time()*1000)}_{secure_filename(file_storage.filename)}"
        file_storage.save(os.path.join(upload_dir, safe_name))
        return safe_name, "video"
    if ext in ALLOWED_FILE_EXT:
        safe_name = f"{int(time.time()*1000)}_{secure_filename(file_storage.filename)}"
        file_storage.save(os.path.join(upload_dir, safe_name))
        return safe_name, "file"
    return None, None


# ---------------------------------------------------------------------------
# HOME / ABOUT
# ---------------------------------------------------------------------------

@app.route("/")
def home():
    user = current_user()
    return render_template("home.html", user=user, site=get_site_content(), hero_photos=get_hero_photos(),
                            active_page="home", auto_open_auth=False)


@app.route("/about")
def about():
    return render_template("about.html", user=current_user(), site=get_site_content(),
                            active_page="about", auto_open_auth=False)


@app.route("/help")
def help_page():
    user = current_user()
    if is_customer(user):
        return redirect(url_for("contact_support"))
    return render_template("help.html", user=user, active_page="help", auto_open_auth=False)


# ---------------------------------------------------------------------------
# AUTH
# ---------------------------------------------------------------------------

@app.route("/signup/customer", methods=["POST"])
def signup_customer():
    name = request.form.get("name", "").strip()
    email = request.form.get("email", "").strip().lower()
    password = request.form.get("password", "")

    if _login_rate_limited(f"signup:{request.remote_addr}"):
        flash("Too many signup attempts from this device. Please wait a few minutes.", "error")
        return redirect(url_for("home"))
    _record_login_attempt(f"signup:{request.remote_addr}")

    conn = get_db()
    if conn.execute("SELECT 1 FROM users WHERE email = ?", (email,)).fetchone():
        conn.close()
        flash("An account with that email already exists.", "error")
        return redirect(url_for("home"))

    cur = conn.execute(
        "INSERT INTO users (name, email, password_hash, role, wallet, referral_code) VALUES (?, ?, ?, 'customer', 500, ?)",
        (name, email, generate_password_hash(password), ""),
    )
    uid = cur.lastrowid
    conn.execute("UPDATE users SET referral_code = ? WHERE id = ?", (f"ANDY{uid:04d}", uid))
    conn.execute("INSERT INTO transactions (user_id, label, amount) VALUES (?, 'Welcome bonus', 500)", (uid,))
    conn.commit()
    conn.close()
    session["user_id"] = uid
    flash(f"Welcome, {name}!", "success")
    return redirect(url_for("andybot_guide"))


@app.route("/login", methods=["POST"])
def login():
    email = request.form.get("email", "").strip().lower()
    password = request.form.get("password", "")

    rate_key = f"login:{email}:{request.remote_addr}"
    if _login_rate_limited(rate_key):
        flash("Too many login attempts. Please wait a few minutes and try again.", "error")
        return redirect(url_for("home"))

    conn = get_db()
    user = conn.execute("SELECT * FROM users WHERE email = ?", (email,)).fetchone()
    conn.close()
    if not user or not check_password_hash(user["password_hash"], password):
        _record_login_attempt(rate_key)
        flash("Invalid email or password.", "error")
        return redirect(url_for("home"))
    if user["role"] == "artisan":
        tech = get_artisan_profile(user["id"])
        if tech and not tech["active"]:
            flash("Your artisan access has been deactivated. Contact Andy for help.", "error")
            return redirect(url_for("home"))
    session["user_id"] = user["id"]
    flash(f"Welcome back, {user['name']}!", "success")
    return redirect(url_for("home"))


@app.route("/login/google")
def login_google():
    if not google_configured():
        flash("Google sign-in isn't set up yet.", "error")
        return redirect(url_for("home"))
    redirect_uri = url_for("google_callback", _external=True)
    params = {
        "client_id": GOOGLE_CLIENT_ID, "redirect_uri": redirect_uri, "response_type": "code",
        "scope": "openid email profile", "access_type": "online", "prompt": "select_account",
    }
    return redirect(f"https://accounts.google.com/o/oauth2/v2/auth?{urlencode(params)}")


@app.route("/login/google/callback")
def google_callback():
    if not google_configured():
        return redirect(url_for("home"))
    code = request.args.get("code")
    if not code:
        flash("Google sign-in was cancelled.", "error")
        return redirect(url_for("home"))
    redirect_uri = url_for("google_callback", _external=True)
    try:
        token_resp = requests.post("https://oauth2.googleapis.com/token", data={
            "client_id": GOOGLE_CLIENT_ID, "client_secret": GOOGLE_CLIENT_SECRET,
            "code": code, "grant_type": "authorization_code", "redirect_uri": redirect_uri,
        }, timeout=15)
        access_token = token_resp.json().get("access_token")
        if not access_token:
            raise ValueError("no access token")
        info_resp = requests.get("https://www.googleapis.com/oauth2/v3/userinfo",
                                  headers={"Authorization": f"Bearer {access_token}"}, timeout=15)
        info = info_resp.json()
        email = info.get("email", "").strip().lower()
        name = info.get("name", "").strip() or (email.split("@")[0] if email else "")
    except Exception:
        flash("Google sign-in failed. Please try again.", "error")
        return redirect(url_for("home"))

    if not email:
        flash("Google sign-in failed. Please try again.", "error")
        return redirect(url_for("home"))

    conn = get_db()
    user = conn.execute("SELECT * FROM users WHERE email = ?", (email,)).fetchone()
    if user:
        conn.close()
        session["user_id"] = user["id"]
        flash(f"Welcome back, {user['name']}!", "success")
        return redirect(url_for("home"))

    random_password = pysecrets.token_hex(16)
    cur = conn.execute(
        "INSERT INTO users (name, email, password_hash, role, wallet, referral_code) VALUES (?, ?, ?, 'customer', 500, ?)",
        (name, email, generate_password_hash(random_password), ""),
    )
    uid = cur.lastrowid
    conn.execute("UPDATE users SET referral_code = ? WHERE id = ?", (f"ANDY{uid:04d}", uid))
    conn.execute("INSERT INTO transactions (user_id, label, amount) VALUES (?, 'Welcome bonus', 500)", (uid,))
    conn.commit()
    conn.close()
    session["user_id"] = uid
    flash(f"Welcome, {name}!", "success")
    return redirect(url_for("andybot_guide"))


@app.route("/logout")
def logout():
    session.pop("user_id", None)
    flash("Logged out.", "success")
    return redirect(url_for("home"))


@app.route("/andybot-guide")
def andybot_guide():
    user = require_login()
    if not user:
        return redirect(url_for("home"))
    return render_template("andybot_guide.html", user=user, active_page="guide", auto_open_auth=False)


@app.route("/dismiss-guide", methods=["POST"])
def dismiss_guide():
    user = require_login()
    if not user:
        return redirect(url_for("home"))
    conn = get_db()
    conn.execute("UPDATE users SET has_seen_guide = 1 WHERE id = ?", (user["id"],))
    conn.commit()
    conn.close()
    return redirect(url_for("home"))


@app.route("/forgot-password", methods=["GET", "POST"])
def forgot_password():
    if request.method == "POST":
        email = request.form.get("email", "").strip().lower()
        if _login_rate_limited(f"forgot:{request.remote_addr}"):
            flash("Too many reset attempts. Please wait a few minutes.", "error")
            return redirect(url_for("forgot_password"))
        _record_login_attempt(f"forgot:{request.remote_addr}")
        conn = get_db()
        user = conn.execute("SELECT * FROM users WHERE email = ?", (email,)).fetchone()
        if user:
            token = pysecrets.token_urlsafe(24)
            expires = (__import__("datetime").datetime.utcnow() + __import__("datetime").timedelta(hours=1)).isoformat()
            conn.execute("UPDATE users SET reset_token = ?, reset_token_expires = ? WHERE id = ?", (token, expires, user["id"]))
            conn.commit()
            reset_link = url_for("reset_password", token=token, _external=True)
            # NOTE: no email service is wired up yet, so the reset link is shown directly here
            # instead of being emailed. Once an email provider is configured, send `reset_link`
            # to the user's email instead of flashing it.
            flash(f"Password reset isn't emailed yet — here's your link: {reset_link}", "success")
        else:
            flash("If that email exists, a reset link has been generated.", "success")
        conn.close()
        return redirect(url_for("forgot_password"))
    return render_template("forgot_password.html", user=None, active_page="forgot_password", auto_open_auth=False)


@app.route("/reset-password/<token>", methods=["GET", "POST"])
def reset_password(token):
    conn = get_db()
    user = conn.execute("SELECT * FROM users WHERE reset_token = ?", (token,)).fetchone()
    if not user:
        conn.close()
        flash("That reset link is invalid or has already been used.", "error")
        return redirect(url_for("forgot_password"))
    expires = user["reset_token_expires"]
    is_expired = False
    try:
        if expires:
            is_expired = __import__("datetime").datetime.fromisoformat(str(expires)) < __import__("datetime").datetime.utcnow()
    except Exception:
        is_expired = True
    if is_expired:
        conn.close()
        flash("That reset link has expired. Please request a new one.", "error")
        return redirect(url_for("forgot_password"))

    if request.method == "POST":
        new_password = request.form.get("new_password", "")
        if len(new_password) < 6:
            conn.close()
            flash("New password must be at least 6 characters.", "error")
            return redirect(url_for("reset_password", token=token))
        conn.execute("UPDATE users SET password_hash = ?, reset_token = '', reset_token_expires = '' WHERE id = ?",
                     (generate_password_hash(new_password), user["id"]))
        conn.commit()
        conn.close()
        flash("Password updated! You can log in now.", "success")
        return redirect(url_for("home"))
    conn.close()
    return render_template("reset_password.html", user=None, token=token, active_page="reset_password", auto_open_auth=False)


# ---------------------------------------------------------------------------
# SERVICE REQUESTS + JOB THREAD (chat lives here, tied to a job)
# ---------------------------------------------------------------------------

@app.route("/request-service", methods=["GET", "POST"])
def request_service():
    user = require_login()
    if not user or not is_customer(user):
        flash("Log in as a customer to request a service.", "error")
        return redirect(url_for("home"))

    if request.method == "POST":
        title = request.form.get("title", "").strip()
        category = request.form.get("category", "Other")
        description = request.form.get("description", "").strip()
        if not title or not description:
            flash("Please fill in a title and description.", "error")
            return redirect(url_for("request_service"))

        conn = get_db()
        cur = conn.execute(
            "INSERT INTO jobs (customer_id, title, description, category, track, status) VALUES (?, ?, ?, ?, 'standard', 'submitted')",
            (user["id"], title, description, category),
        )
        job_id = cur.lastrowid
        files = request.files.getlist("attachments")
        for f in files:
            stored, kind = _save_attachment(f, ATTACHMENTS_UPLOAD_DIR)
            if stored:
                conn.execute("INSERT INTO job_attachments (job_id, filename, kind) VALUES (?, ?, ?)", (job_id, stored, kind))
        conn.commit()
        conn.close()
        flash("Request submitted! Andy will review it shortly.", "success")
        return redirect(url_for("job_thread", job_id=job_id))

    return render_template("request_service.html", user=user, categories=JOB_CATEGORIES,
                            active_page="request_service", auto_open_auth=False)


@app.route("/contact-support")
def contact_support():
    user = require_login()
    if not user or not is_customer(user):
        return redirect(url_for("home"))
    conn = get_db()
    existing = conn.execute(
        "SELECT * FROM jobs WHERE customer_id=? AND category='General Support' AND status != 'completed' AND status != 'cancelled' ORDER BY id DESC LIMIT 1",
        (user["id"],),
    ).fetchone()
    if existing:
        conn.close()
        return redirect(url_for("job_thread", job_id=existing["id"]))
    cur = conn.execute(
        "INSERT INTO jobs (customer_id, title, description, category, track, status) VALUES (?, 'General Support', 'Support conversation with Andy.', 'General Support', 'standard', 'submitted')",
        (user["id"],),
    )
    job_id = cur.lastrowid
    conn.commit()
    conn.close()
    return redirect(url_for("job_thread", job_id=job_id))


@app.route("/my-jobs")
def my_jobs():
    user = require_login()
    if not user or not is_customer(user):
        return redirect(url_for("home"))
    conn = get_db()
    rows = conn.execute("SELECT * FROM jobs WHERE customer_id=? ORDER BY id DESC", (user["id"],)).fetchall()
    conn.close()
    return render_template("my_jobs.html", user=user, jobs=[dict(r) for r in rows],
                            active_page="my_jobs", auto_open_auth=False)


@app.route("/artisan/jobs")
def artisan_jobs():
    user = require_login()
    if not user or not is_artisan(user):
        return redirect(url_for("home"))
    tech = get_artisan_profile(user["id"])
    conn = get_db()
    rows = conn.execute("""
        SELECT jobs.*, users.name AS customer_name FROM jobs
        JOIN users ON jobs.customer_id = users.id
        WHERE jobs.artisan_id = ? ORDER BY jobs.id DESC
    """, (tech["id"] if tech else -1,)).fetchall()
    conn.close()
    return render_template("artisan_jobs.html", user=user, jobs=[dict(r) for r in rows],
                            active_page="artisan_jobs", auto_open_auth=False)


@app.route("/job/<int:job_id>")
def job_thread(job_id):
    user = require_login()
    if not user:
        return redirect(url_for("home"))
    conn = get_db()
    job = conn.execute("SELECT * FROM jobs WHERE id=?", (job_id,)).fetchone()
    if not job:
        conn.close()
        flash("Job not found.", "error")
        return redirect(url_for("home"))
    job = dict(job)
    if not job_visible_to(user, job):
        conn.close()
        flash("You don't have access to that job.", "error")
        return redirect(url_for("home"))

    customer = conn.execute("SELECT name FROM users WHERE id=?", (job["customer_id"],)).fetchone()
    artisan_name = None
    if job["artisan_id"]:
        trow = conn.execute("""
            SELECT users.name FROM artisans JOIN users ON artisans.user_id = users.id
            WHERE artisans.id = ?
        """, (job["artisan_id"],)).fetchone()
        artisan_name = trow["name"] if trow else None

    attachments = [dict(a) for a in conn.execute("SELECT * FROM job_attachments WHERE job_id=?", (job_id,)).fetchall()]
    messages = [dict(m) for m in conn.execute("""
        SELECT messages.*, users.name AS sender_name, users.avatar_filename AS sender_avatar
        FROM messages JOIN users ON messages.sender_id = users.id
        WHERE messages.job_id=? ORDER BY messages.id
    """, (job_id,)).fetchall()]

    if is_owner(user):
        conn.execute("UPDATE messages SET read_by_owner = 1 WHERE job_id = ?", (job_id,))
        conn.commit()
    if is_customer(user):
        conn.execute("UPDATE messages SET read_by_customer = 1 WHERE job_id = ?", (job_id,))
        conn.commit()

    artisans = []
    if is_owner(user):
        rows = conn.execute("""
            SELECT artisans.id, artisans.category, users.name FROM artisans
            JOIN users ON artisans.user_id = users.id WHERE artisans.active = 1
        """).fetchall()
        artisans = [dict(r) for r in rows]

    review = conn.execute("SELECT * FROM reviews WHERE job_id = ?", (job_id,)).fetchone()
    review = dict(review) if review else None
    conn.close()

    return render_template(
        "job_thread.html", user=user, job=job, customer_name=customer["name"] if customer else "",
        artisan_name=artisan_name, attachments=attachments, messages=messages, artisans=artisans,
        review=review, is_owner_view=is_owner(user), is_customer_view=is_customer(user),
        active_page="my_jobs", auto_open_auth=False,
    )


@app.route("/job/<int:job_id>/message", methods=["POST"])
def post_job_message(job_id):
    user = require_login()
    if not user:
        return redirect(url_for("home"))
    conn = get_db()
    job = conn.execute("SELECT * FROM jobs WHERE id=?", (job_id,)).fetchone()
    if not job or not job_visible_to(user, dict(job)):
        conn.close()
        flash("You don't have access to that job.", "error")
        return redirect(url_for("home"))

    text = request.form.get("text", "").strip()
    if job["status"] not in ("in_progress",):
        text = mask_phone_numbers(text) if text else text

    attachment_value, attachment_kind = _save_attachment(request.files.get("attachment"), ATTACHMENTS_UPLOAD_DIR)

    if text or attachment_value:
        owner_read_flag = 1 if user["role"] == "owner" else 0
        customer_read_flag = 1 if user["role"] == "customer" else 0
        conn.execute(
            "INSERT INTO messages (job_id, sender_id, sender_role, text, attachment_filename, attachment_kind, read_by_owner, read_by_customer) VALUES (?, ?, ?, ?, ?, ?, ?, ?)",
            (job_id, user["id"], user["role"], text, attachment_value or "", attachment_kind or "", owner_read_flag, customer_read_flag),
        )
        conn.commit()
    conn.close()
    return redirect(url_for("job_thread", job_id=job_id))


@app.route("/admin/job/<int:job_id>/update", methods=["POST"])
def admin_update_job(job_id):
    user = require_owner()
    if not user:
        return redirect(url_for("home"))
    conn = get_db()
    job = conn.execute("SELECT * FROM jobs WHERE id=?", (job_id,)).fetchone()
    if not job:
        conn.close()
        flash("Job not found.", "error")
        return redirect(url_for("admin_jobs"))

    artisan_id = request.form.get("artisan_id") or None
    track = request.form.get("track", "standard")
    try:
        amount = int(request.form.get("amount", 0))
    except ValueError:
        amount = 0

    new_status = job["status"]
    if artisan_id and job["status"] == "submitted":
        new_status = "assigned"

    conn.execute(
        "UPDATE jobs SET artisan_id=?, track=?, amount=?, status=? WHERE id=?",
        (artisan_id, track, amount, new_status, job_id),
    )
    conn.commit()
    conn.close()
    flash("Job updated.", "success")
    return redirect(url_for("job_thread", job_id=job_id))


@app.route("/job/<int:job_id>/pay", methods=["POST"])
def pay_for_job(job_id):
    user = require_login()
    if not user or not is_customer(user):
        return redirect(url_for("home"))
    conn = get_db()
    job = conn.execute("SELECT * FROM jobs WHERE id=? AND customer_id=?", (job_id, user["id"])).fetchone()
    if not job or job["status"] != "assigned" or not job["amount"]:
        conn.close()
        flash("This job isn't ready for payment yet.", "error")
        return redirect(url_for("job_thread", job_id=job_id))
    fresh = conn.execute("SELECT wallet FROM users WHERE id=?", (user["id"],)).fetchone()
    if fresh["wallet"] < job["amount"]:
        conn.close()
        flash("Not enough CONNECT coins. Top up your wallet first.", "error")
        return redirect(url_for("job_thread", job_id=job_id))

    conn.execute("UPDATE users SET wallet = wallet - ? WHERE id=?", (job["amount"], user["id"]))
    conn.execute("INSERT INTO transactions (user_id, label, amount) VALUES (?, ?, ?)",
                 (user["id"], f"Payment for job: {job['title']} (held in escrow)", -job["amount"]))
    conn.execute("UPDATE jobs SET status='in_progress' WHERE id=?", (job_id,))
    conn.commit()
    conn.close()
    flash("Payment held in escrow. Your artisan has been notified.", "success")
    return redirect(url_for("job_thread", job_id=job_id))


@app.route("/job/<int:job_id>/complete", methods=["POST"])
def complete_service_job(job_id):
    user = require_login()
    if not user or not is_customer(user):
        return redirect(url_for("home"))
    conn = get_db()
    job = conn.execute("SELECT * FROM jobs WHERE id=? AND customer_id=?", (job_id, user["id"])).fetchone()
    if not job or job["status"] != "in_progress":
        conn.close()
        flash("This job isn't ready to complete yet.", "error")
        return redirect(url_for("job_thread", job_id=job_id))

    tech = conn.execute("SELECT * FROM artisans WHERE id=?", (job["artisan_id"],)).fetchone()
    conn.execute("UPDATE jobs SET status='completed' WHERE id=?", (job_id,))
    if tech:
        conn.execute("UPDATE artisans SET jobs_completed = jobs_completed + 1 WHERE id=?", (tech["id"],))
        conn.execute("UPDATE users SET wallet = wallet + ? WHERE id=?", (job["amount"], tech["user_id"]))
        conn.execute("INSERT INTO transactions (user_id, label, amount) VALUES (?, ?, ?)",
                     (tech["user_id"], f"Payment released: {job['title']}", job["amount"]))
    conn.commit()
    conn.close()
    flash("Job marked complete — payment released to your artisan.", "success")
    return redirect(url_for("job_thread", job_id=job_id))


@app.route("/job/<int:job_id>/review", methods=["POST"])
def submit_review(job_id):
    user = require_login()
    if not user or not is_customer(user):
        return redirect(url_for("home"))
    conn = get_db()
    job = conn.execute("SELECT * FROM jobs WHERE id=? AND customer_id=?", (job_id, user["id"])).fetchone()
    if not job or job["status"] != "completed" or not job["artisan_id"]:
        conn.close()
        flash("This job can't be reviewed.", "error")
        return redirect(url_for("job_thread", job_id=job_id))
    existing = conn.execute("SELECT 1 FROM reviews WHERE job_id = ?", (job_id,)).fetchone()
    if existing:
        conn.close()
        flash("You've already reviewed this job.", "error")
        return redirect(url_for("job_thread", job_id=job_id))

    try:
        rating = int(request.form.get("rating", 0))
    except ValueError:
        rating = 0
    rating = max(1, min(5, rating))
    text = request.form.get("text", "").strip()

    conn.execute(
        "INSERT INTO reviews (job_id, artisan_id, customer_id, rating, text) VALUES (?, ?, ?, ?, ?)",
        (job_id, job["artisan_id"], user["id"], rating, text),
    )
    agg = conn.execute(
        "SELECT AVG(rating) AS avg_rating, COUNT(*) AS cnt FROM reviews WHERE artisan_id = ?",
        (job["artisan_id"],),
    ).fetchone()
    conn.execute(
        "UPDATE artisans SET rating = ?, reviews = ? WHERE id = ?",
        (round(agg["avg_rating"], 1), agg["cnt"], job["artisan_id"]),
    )
    conn.commit()
    conn.close()
    flash("Thanks for your review!", "success")
    return redirect(url_for("job_thread", job_id=job_id))


# ---------------------------------------------------------------------------
# CAMERA WINDOW MEASUREMENT ASSISTANT
# ---------------------------------------------------------------------------

@app.route("/measure")
def measure_tool():
    user = require_login()
    if not user:
        return redirect(url_for("home"))
    return render_template("measure.html", user=user, references=MEASUREMENT_REFERENCES,
                            active_page="measure", auto_open_auth=False)


@app.route("/measure/save", methods=["POST"])
def save_measurement():
    user = require_login()
    if not user:
        return redirect(url_for("home"))

    try:
        width_cm = float(request.form.get("width_cm", 0))
        height_cm = float(request.form.get("height_cm", 0))
        reference_cm = float(request.form.get("reference_cm", 0))
    except ValueError:
        flash("Something went wrong with that measurement. Please try again.", "error")
        return redirect(url_for("measure_tool"))

    if width_cm <= 0 or height_cm <= 0:
        flash("Couldn't save an empty measurement — please mark the edges first.", "error")
        return redirect(url_for("measure_tool"))

    photo_value = _save_base64_photo(request.form.get("photo_data", ""), MEASUREMENTS_UPLOAD_DIR)

    conn = get_db()
    conn.execute(
        "INSERT INTO measurements (user_id, project_name, photo_filename, reference_label, reference_cm, "
        "width_cm, height_cm, confidence, notes) VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?)",
        (
            user["id"],
            request.form.get("project_name", "").strip(),
            photo_value,
            request.form.get("reference_label", "").strip(),
            reference_cm,
            round(width_cm, 1),
            round(height_cm, 1),
            request.form.get("confidence", "normal"),
            request.form.get("notes", "").strip(),
        ),
    )
    conn.commit()
    conn.close()
    flash("Measurement saved.", "success")
    return redirect(url_for("measurement_history"))


@app.route("/measure/history")
def measurement_history():
    user = require_login()
    if not user:
        return redirect(url_for("home"))
    conn = get_db()
    if is_owner(user):
        rows = conn.execute("""
            SELECT measurements.*, users.name AS user_name FROM measurements
            JOIN users ON measurements.user_id = users.id ORDER BY measurements.id DESC
        """).fetchall()
    else:
        rows = conn.execute(
            "SELECT * FROM measurements WHERE user_id = ? ORDER BY id DESC", (user["id"],)
        ).fetchall()
    conn.close()
    return render_template("measurement_history.html", user=user, measurements=[dict(r) for r in rows],
                            active_page="measure_history", auto_open_auth=False)


# ---------------------------------------------------------------------------
# ADMIN
# ---------------------------------------------------------------------------

@app.route("/admin")
def admin_dashboard():
    user = require_owner()
    if not user:
        return redirect(url_for("home"))
    conn = get_db()
    customers = conn.execute("SELECT COUNT(*) c FROM users WHERE role='customer'").fetchone()["c"]
    artisans = conn.execute("SELECT COUNT(*) c FROM artisans WHERE active=1").fetchone()["c"]
    pending_jobs = conn.execute("SELECT COUNT(*) c FROM jobs WHERE status='submitted'").fetchone()["c"]
    eas_jobs = conn.execute("SELECT COUNT(*) c FROM jobs WHERE track='eas'").fetchone()["c"]
    recent = conn.execute("""
        SELECT jobs.*, users.name AS customer_name FROM jobs
        JOIN users ON jobs.customer_id = users.id ORDER BY jobs.id DESC LIMIT 10
    """).fetchall()
    conn.close()
    stats = {"customers": customers, "artisans": artisans, "pending_jobs": pending_jobs, "eas_jobs": eas_jobs}
    return render_template("admin_dashboard.html", user=user, stats=stats, recent_jobs=[dict(r) for r in recent],
                            active_page="admin_dashboard", auto_open_auth=False)


@app.route("/admin/chats")
def admin_chats():
    user = require_owner()
    if not user:
        return redirect(url_for("home"))
    conn = get_db()
    rows = conn.execute("""
        SELECT jobs.id AS job_id, jobs.title, jobs.category, jobs.status, users.name AS customer_name,
               users.avatar_filename AS customer_avatar,
               (SELECT text FROM messages WHERE job_id = jobs.id ORDER BY id DESC LIMIT 1) AS last_text,
               (SELECT sender_role FROM messages WHERE job_id = jobs.id ORDER BY id DESC LIMIT 1) AS last_sender_role,
               (SELECT created_at FROM messages WHERE job_id = jobs.id ORDER BY id DESC LIMIT 1) AS last_at,
               (SELECT COUNT(*) FROM messages WHERE job_id = jobs.id AND sender_role != 'owner' AND read_by_owner = 0) AS unread
        FROM jobs JOIN users ON jobs.customer_id = users.id
        WHERE EXISTS (SELECT 1 FROM messages WHERE messages.job_id = jobs.id)
        ORDER BY last_at DESC
    """).fetchall()
    conn.close()
    return render_template("admin_chats.html", user=user, conversations=[dict(r) for r in rows],
                            active_page="admin_chats", auto_open_auth=False)


@app.route("/admin/artisans")
def admin_artisans():
    user = require_owner()
    if not user:
        return redirect(url_for("home"))
    conn = get_db()
    rows = conn.execute("""
        SELECT artisans.*, users.name AS name, users.email AS email FROM artisans
        JOIN users ON artisans.user_id = users.id ORDER BY artisans.id DESC
    """).fetchall()
    artisans = [dict(r) for r in rows]
    for t in artisans:
        rev_rows = conn.execute("""
            SELECT reviews.*, users.name AS customer_name FROM reviews
            JOIN users ON reviews.customer_id = users.id
            WHERE reviews.artisan_id = ? ORDER BY reviews.id DESC LIMIT 3
        """, (t["id"],)).fetchall()
        t["recent_reviews"] = [dict(r) for r in rev_rows]
    conn.close()
    return render_template("admin_artisans.html", user=user, artisans=artisans,
                            categories=JOB_CATEGORIES, active_page="admin_artisans", auto_open_auth=False)


@app.route("/admin/artisans/add", methods=["POST"])
def add_artisan():
    user = require_owner()
    if not user:
        return redirect(url_for("home"))
    name = request.form.get("name", "").strip()
    email = request.form.get("email", "").strip().lower()
    password = request.form.get("password", "")
    category = request.form.get("category", "Aluminum Fabrication")
    phone = request.form.get("phone", "").strip()

    conn = get_db()
    if conn.execute("SELECT 1 FROM users WHERE email=?", (email,)).fetchone():
        conn.close()
        flash("An account with that email already exists.", "error")
        return redirect(url_for("admin_artisans"))

    initials = "".join([p[0] for p in name.split()[:2]]).upper()
    cur = conn.execute(
        "INSERT INTO users (name, email, password_hash, role, wallet, referral_code) VALUES (?, ?, ?, 'artisan', 0, '')",
        (name, email, generate_password_hash(password)),
    )
    uid = cur.lastrowid
    conn.execute(
        "INSERT INTO artisans (user_id, category, phone, active, initials) VALUES (?, ?, ?, 1, ?)",
        (uid, category, phone, initials),
    )
    conn.commit()
    conn.close()
    flash(f"Artisan {name} added.", "success")
    return redirect(url_for("admin_artisans"))


@app.route("/admin/artisans/<int:artisan_id>/toggle", methods=["POST"])
def toggle_artisan(artisan_id):
    user = require_owner()
    if not user:
        return redirect(url_for("home"))
    conn = get_db()
    tech = conn.execute("SELECT * FROM artisans WHERE id=?", (artisan_id,)).fetchone()
    if tech:
        conn.execute("UPDATE artisans SET active=? WHERE id=?", (0 if tech["active"] else 1, artisan_id))
        conn.commit()
    conn.close()
    flash("Artisan status updated.", "success")
    return redirect(url_for("admin_artisans"))


@app.route("/admin/jobs")
def admin_jobs():
    user = require_owner()
    if not user:
        return redirect(url_for("home"))
    status = request.args.get("status", "").strip()
    conn = get_db()
    query = """
        SELECT jobs.*, users.name AS customer_name,
               (SELECT u2.name FROM artisans t2 JOIN users u2 ON t2.user_id = u2.id WHERE t2.id = jobs.artisan_id) AS artisan_name
        FROM jobs JOIN users ON jobs.customer_id = users.id
    """
    if status:
        rows = conn.execute(query + " WHERE jobs.status=? ORDER BY jobs.id DESC", (status,)).fetchall()
    else:
        rows = conn.execute(query + " ORDER BY jobs.id DESC").fetchall()
    conn.close()
    return render_template("admin_jobs.html", user=user, jobs=[dict(r) for r in rows], statuses=JOB_STATUSES,
                            active_status=status, active_page="admin_jobs", auto_open_auth=False)


@app.route("/admin/site", methods=["GET", "POST"])
def admin_site():
    user = require_owner()
    if not user:
        return redirect(url_for("home"))
    conn = get_db()
    if request.method == "POST":
        tagline = request.form.get("tagline", "").strip()
        what_offers = request.form.get("what_offers", "").strip()
        about_text = request.form.get("about_text", "").strip()
        conn.execute("UPDATE site_content SET tagline=?, what_offers=?, about_text=? WHERE id=(SELECT id FROM site_content ORDER BY id LIMIT 1)",
                     (tagline, what_offers, about_text))
        conn.commit()
        conn.close()
        flash("Site content updated.", "success")
        return redirect(url_for("admin_site"))
    conn.close()
    return render_template("admin_site.html", user=user, site=get_site_content(), hero_photos=get_hero_photos(),
                            active_page="admin_site", auto_open_auth=False)


@app.route("/admin/controls", methods=["GET", "POST"])
def admin_controls():
    user = require_owner()
    if not user:
        return redirect(url_for("home"))
    conn = get_db()
    if request.method == "POST":
        flags = ["maintenance_mode", "signups_enabled", "catalog_enabled", "reels_enabled",
                 "tipped_videos_enabled", "measure_enabled"]
        values = [1 if request.form.get(f) == "on" else 0 for f in flags]
        conn.execute(
            f"UPDATE site_content SET {', '.join(f + '=?' for f in flags)} "
            f"WHERE id=(SELECT id FROM site_content ORDER BY id LIMIT 1)",
            values,
        )
        conn.commit()
        conn.close()
        flash("Site controls updated.", "success")
        return redirect(url_for("admin_controls"))
    conn.close()
    return render_template("admin_controls.html", user=user, site=get_site_content(),
                            active_page="admin_controls", auto_open_auth=False)


@app.route("/dashboard/upload_photo", methods=["POST"])
def upload_photo():
    user = require_owner()
    if not user:
        return redirect(url_for("home"))
    file = request.files.get("photo")
    stored, kind = _save_attachment(file, UPLOAD_DIR) if file else (None, None)
    if not stored or kind != "image":
        flash("Choose a valid photo (jpg, jpeg, png, webp).", "error")
        return redirect(url_for("admin_site"))
    conn = get_db()
    conn.execute("INSERT INTO hero_photos (filename) VALUES (?)", (stored,))
    conn.commit()
    conn.close()
    flash("Photo uploaded.", "success")
    return redirect(url_for("admin_site"))


@app.route("/dashboard/delete_photo/<int:photo_id>", methods=["POST"])
def delete_photo(photo_id):
    user = require_owner()
    if not user:
        return redirect(url_for("home"))
    conn = get_db()
    row = conn.execute("SELECT * FROM hero_photos WHERE id=?", (photo_id,)).fetchone()
    if row:
        if not row["filename"].startswith("http"):
            try:
                os.remove(os.path.join(UPLOAD_DIR, row["filename"]))
            except OSError:
                pass
        conn.execute("DELETE FROM hero_photos WHERE id=?", (photo_id,))
        conn.commit()
    conn.close()
    flash("Photo removed.", "success")
    return redirect(url_for("admin_site"))


# ---------------------------------------------------------------------------
# ARTISAN DASHBOARD (own video uploads)
# ---------------------------------------------------------------------------

@app.route("/dashboard")
def dashboard():
    user = current_user()
    if not is_artisan(user):
        flash("Artisan dashboard only.", "error")
        return redirect(url_for("home"))
    tech = get_artisan_profile(user["id"])
    conn = get_db()
    videos = conn.execute("SELECT * FROM videos WHERE artisan_id=?", (tech["id"],)).fetchall()
    conn.close()
    tech_full = dict(tech)
    tech_full["name"] = user["name"]
    return render_template("dashboard.html", user=user, artisan=tech_full, videos=[dict(v) for v in videos],
                            active_page="dashboard", auto_open_auth=False)


@app.route("/upload_clip", methods=["POST"])
def upload_clip():
    user = current_user()
    if not (is_artisan(user) or is_owner(user)):
        return redirect(url_for("home"))
    tech_id = get_artisan_profile(user["id"])["id"] if is_artisan(user) else 0
    title = request.form.get("title", "").strip()
    description = request.form.get("description", "").strip()
    video_url, _kind = _save_attachment(request.files.get("video"), VIDEOS_UPLOAD_DIR, allow_video=True)
    if title:
        conn = get_db()
        conn.execute(
            "INSERT INTO videos (artisan_id, title, description, is_paid, price, video_url) VALUES (?, ?, ?, 0, 0, ?)",
            (tech_id, title, description, video_url or ""),
        )
        conn.commit()
        conn.close()
        flash("Clip uploaded.", "success")
    return redirect(url_for("admin_learning") if is_owner(user) else url_for("dashboard"))


@app.route("/upload_paid_clip", methods=["POST"])
def upload_paid_clip():
    user = current_user()
    if not (is_artisan(user) or is_owner(user)):
        return redirect(url_for("home"))
    tech_id = get_artisan_profile(user["id"])["id"] if is_artisan(user) else 0
    title = request.form.get("title", "").strip()
    description = request.form.get("description", "").strip()
    try:
        price = int(request.form.get("price", 0))
    except ValueError:
        price = 0
    video_url, _kind = _save_attachment(request.files.get("video"), VIDEOS_UPLOAD_DIR, allow_video=True)
    if title and price > 0:
        conn = get_db()
        conn.execute(
            "INSERT INTO videos (artisan_id, title, description, is_paid, price, video_url) VALUES (?, ?, ?, 1, ?, ?)",
            (tech_id, title, description, price, video_url or ""),
        )
        conn.commit()
        conn.close()
        flash("Paid clip uploaded (shows as 'Coming Soon' to customers until you're ready to sell it).", "success")
    return redirect(url_for("admin_learning") if is_owner(user) else url_for("dashboard"))


@app.route("/admin/learning")
def admin_learning():
    user = require_owner()
    if not user:
        return redirect(url_for("home"))
    conn = get_db()
    videos = conn.execute("SELECT * FROM videos WHERE artisan_id=0 ORDER BY id DESC").fetchall()
    conn.close()
    return render_template("admin_learning.html", user=user, videos=[dict(v) for v in videos],
                            active_page="admin_learning", auto_open_auth=False)


@app.route("/dashboard/delete_video/<int:video_id>", methods=["POST"])
def delete_video(video_id):
    user = current_user()
    conn = get_db()
    v = conn.execute("SELECT * FROM videos WHERE id=?", (video_id,)).fetchone()
    if not v:
        conn.close()
        return redirect(url_for("home"))
    allowed = is_owner(user) and v["artisan_id"] == 0
    if not allowed and is_artisan(user):
        tech = get_artisan_profile(user["id"])
        allowed = tech and v["artisan_id"] == tech["id"]
    if not allowed:
        conn.close()
        flash("You can't remove that video.", "error")
        return redirect(url_for("home"))
    if v["video_url"] and not v["video_url"].startswith("http"):
        try:
            os.remove(os.path.join(VIDEOS_UPLOAD_DIR, v["video_url"]))
        except OSError:
            pass
    conn.execute("DELETE FROM videos WHERE id=?", (video_id,))
    conn.commit()
    conn.close()
    flash("Video removed.", "success")
    return redirect(url_for("admin_learning") if is_owner(user) else url_for("dashboard"))




# ---------------------------------------------------------------------------
# PRODUCT CATALOG (managed by owner/admin; customers browse + buy)
# ---------------------------------------------------------------------------

@app.route("/catalog")
def catalog():
    user = current_user()
    active_cat = request.args.get("cat", "").strip()
    conn = get_db()
    if active_cat:
        rows = conn.execute("SELECT * FROM products WHERE category=? ORDER BY id DESC", (active_cat,)).fetchall()
    else:
        rows = conn.execute("SELECT * FROM products ORDER BY id DESC").fetchall()
    conn.close()
    products = [_product_dict(r) for r in rows]
    return render_template("catalog.html", user=user, products=products, categories=PRODUCT_CATEGORIES,
                            active_cat=active_cat, active_page="catalog", auto_open_auth=False)


@app.route("/catalog/add_to_cart/<int:product_id>", methods=["POST"])
def add_to_cart(product_id):
    user = require_login()
    if not user or not is_customer(user):
        return redirect(url_for("catalog"))
    conn = get_db()
    product = conn.execute("SELECT * FROM products WHERE id=?", (product_id,)).fetchone()
    if not product:
        conn.close()
        flash("Product not found.", "error")
        return redirect(url_for("catalog"))
    size = request.form.get("size", "").strip()
    try:
        quantity = max(1, int(request.form.get("quantity", 1)))
    except ValueError:
        quantity = 1
    amount = product["price"] * quantity
    conn.execute(
        "INSERT INTO product_orders (customer_id, product_id, size, quantity, amount, status) VALUES (?, ?, ?, ?, ?, 'cart')",
        (user["id"], product_id, size, quantity, amount),
    )
    conn.commit()
    conn.close()
    flash(f"Added {product['name']} to your cart.", "success")
    return redirect(url_for("catalog"))


@app.route("/cart")
def cart():
    user = require_login()
    if not user or not is_customer(user):
        return redirect(url_for("catalog"))
    conn = get_db()
    cart_rows = conn.execute("""
        SELECT product_orders.*, products.name AS name, products.price AS unit_price
        FROM product_orders JOIN products ON product_orders.product_id = products.id
        WHERE product_orders.customer_id=? AND product_orders.status='cart' ORDER BY product_orders.id
    """, (user["id"],)).fetchall()
    other_rows = conn.execute("""
        SELECT product_orders.*, products.name AS name FROM product_orders
        JOIN products ON product_orders.product_id = products.id
        WHERE product_orders.customer_id=? AND product_orders.status!='cart' ORDER BY product_orders.id DESC
    """, (user["id"],)).fetchall()
    conn.close()
    cart_items = [dict(r) for r in cart_rows]
    total = sum(i["amount"] for i in cart_items)
    return render_template("cart.html", user=user, cart_items=cart_items, total=total,
                            my_orders=[dict(r) for r in other_rows], active_page="cart", auto_open_auth=False)


@app.route("/cart/remove/<int:order_id>", methods=["POST"])
def remove_from_cart(order_id):
    user = require_login()
    if not user:
        return redirect(url_for("cart"))
    conn = get_db()
    conn.execute("DELETE FROM product_orders WHERE id=? AND customer_id=? AND status='cart'", (order_id, user["id"]))
    conn.commit()
    conn.close()
    return redirect(url_for("cart"))


@app.route("/cart/checkout", methods=["POST"])
def checkout_cart():
    user = require_login()
    if not user or not is_customer(user):
        return redirect(url_for("cart"))
    conn = get_db()
    cart_rows = conn.execute("SELECT * FROM product_orders WHERE customer_id=? AND status='cart'", (user["id"],)).fetchall()
    if not cart_rows:
        conn.close()
        flash("Your cart is empty.", "error")
        return redirect(url_for("cart"))
    total = sum(r["amount"] for r in cart_rows)
    fresh_user = conn.execute("SELECT * FROM users WHERE id=?", (user["id"],)).fetchone()
    if fresh_user["wallet"] < total:
        conn.close()
        flash("Not enough CONNECT coins. Top up your wallet first.", "error")
        return redirect(url_for("cart"))

    conn.execute("UPDATE users SET wallet = wallet - ? WHERE id=?", (total, user["id"]))
    conn.execute("INSERT INTO transactions (user_id, label, amount) VALUES (?, ?, ?)",
                 (user["id"], "Catalog order (held in escrow)", -total))
    conn.execute("UPDATE product_orders SET status='paid' WHERE customer_id=? AND status='cart'", (user["id"],))
    conn.commit()
    conn.close()
    flash("Order placed! Payment held until Andy fulfills it.", "success")
    return redirect(url_for("cart"))


@app.route("/dashboard/catalog")
def dashboard_catalog():
    user = require_owner()
    if not user:
        return redirect(url_for("home"))
    conn = get_db()
    products = [_product_dict(r) for r in conn.execute("SELECT * FROM products ORDER BY id DESC").fetchall()]
    orders = conn.execute("""
        SELECT product_orders.*, products.name AS name, users.name AS customer_name
        FROM product_orders
        JOIN products ON product_orders.product_id = products.id
        JOIN users ON product_orders.customer_id = users.id
        WHERE product_orders.status != 'cart' ORDER BY product_orders.id DESC
    """).fetchall()
    conn.close()
    return render_template("dashboard_catalog.html", user=user, products=products, orders=[dict(o) for o in orders],
                            categories=PRODUCT_CATEGORIES, active_page="dashboard_catalog", auto_open_auth=False)


@app.route("/dashboard/add_product", methods=["POST"])
def add_product():
    user = require_owner()
    if not user:
        return redirect(url_for("home"))
    name = request.form.get("name", "").strip()
    category = request.form.get("category", "Windows")
    description = request.form.get("description", "").strip()
    try:
        price = int(request.form.get("price", 0))
    except ValueError:
        price = 0
    sizes = request.form.get("sizes", "").strip()
    if not name or price <= 0:
        flash("Give the product a name and a valid price.", "error")
        return redirect(url_for("dashboard_catalog"))

    image_value = ""
    file = request.files.get("image")
    if file and file.filename:
        stored, kind = _save_attachment(file, PRODUCTS_UPLOAD_DIR)
        if stored and kind == "image":
            image_value = stored

    video_value = ""
    video_file = request.files.get("video")
    if video_file and video_file.filename:
        stored_v, kind_v = _save_attachment(video_file, PRODUCTS_UPLOAD_DIR, allow_video=True)
        if stored_v and kind_v == "video":
            video_value = stored_v

    conn = get_db()
    conn.execute(
        "INSERT INTO products (name, category, description, price, sizes_csv, image_filename, video_url) VALUES (?, ?, ?, ?, ?, ?, ?)",
        (name, category, description, price, sizes, image_value, video_value),
    )
    conn.commit()
    conn.close()
    flash("Product added to catalog.", "success")
    return redirect(url_for("dashboard_catalog"))


@app.route("/dashboard/delete_product/<int:product_id>", methods=["POST"])
def delete_product(product_id):
    user = require_owner()
    if not user:
        return redirect(url_for("home"))
    conn = get_db()
    row = conn.execute("SELECT * FROM products WHERE id=?", (product_id,)).fetchone()
    if row and row["image_filename"] and not row["image_filename"].startswith("http"):
        try:
            os.remove(os.path.join(PRODUCTS_UPLOAD_DIR, row["image_filename"]))
        except OSError:
            pass
    if row and row["video_url"] and not row["video_url"].startswith("http"):
        try:
            os.remove(os.path.join(PRODUCTS_UPLOAD_DIR, row["video_url"]))
        except OSError:
            pass
    conn.execute("DELETE FROM products WHERE id=?", (product_id,))
    conn.commit()
    conn.close()
    flash("Product removed.", "success")
    return redirect(url_for("dashboard_catalog"))


@app.route("/dashboard/fulfill_order/<int:order_id>", methods=["POST"])
def fulfill_order(order_id):
    user = require_owner()
    if not user:
        return redirect(url_for("home"))
    conn = get_db()
    order = conn.execute("SELECT * FROM product_orders WHERE id=? AND status='paid'", (order_id,)).fetchone()
    if not order:
        conn.close()
        flash("Order not found or already handled.", "error")
        return redirect(url_for("dashboard_catalog"))
    conn.execute("UPDATE product_orders SET status='fulfilled' WHERE id=?", (order_id,))
    conn.execute("UPDATE users SET wallet = wallet + ? WHERE id=?", (order["amount"], user["id"]))
    conn.execute("INSERT INTO transactions (user_id, label, amount) VALUES (?, ?, ?)",
                 (user["id"], "Catalog order payment released", order["amount"]))
    conn.commit()
    conn.close()
    flash("Order marked fulfilled — payment released.", "success")
    return redirect(url_for("dashboard_catalog"))


# ---------------------------------------------------------------------------
# LEARNING CENTER + PRO
# ---------------------------------------------------------------------------

@app.route("/learning-center")
def learning_center():
    return redirect(url_for("reels"))


def _video_with_artisan_query(extra_where=""):
    return f"""
        SELECT videos.*, users.name AS artisan_name FROM videos
        LEFT JOIN artisans ON videos.artisan_id = artisans.id
        LEFT JOIN users ON artisans.user_id = users.id
        {extra_where}
        ORDER BY videos.id DESC
    """


@app.route("/reels")
def reels():
    user = current_user()
    conn = get_db()
    rows = conn.execute(_video_with_artisan_query("WHERE videos.is_paid = 0")).fetchall()
    vlist = []
    for r in rows:
        v = dict(r)
        v["artisan_name"] = v["artisan_name"] or "Andy Team"
        v["like_count"] = conn.execute("SELECT COUNT(*) c FROM video_likes WHERE video_id=?", (v["id"],)).fetchone()["c"]
        v["comment_count"] = conn.execute("SELECT COUNT(*) c FROM video_comments WHERE video_id=?", (v["id"],)).fetchone()["c"]
        v["liked_by_me"] = bool(user) and conn.execute("SELECT 1 FROM video_likes WHERE video_id=? AND user_id=?", (v["id"], user["id"] if user else -1)).fetchone() is not None
        v["saved_by_me"] = bool(user) and conn.execute("SELECT 1 FROM video_saves WHERE video_id=? AND user_id=?", (v["id"], user["id"] if user else -1)).fetchone() is not None
        vlist.append(v)
    conn.close()
    return render_template("reels.html", user=user, videos=vlist, active_page="reels", auto_open_auth=False)


@app.route("/reels/<int:video_id>/like", methods=["POST"])
def like_video(video_id):
    user = require_login()
    if not user:
        return redirect(url_for("reels"))
    conn = get_db()
    existing = conn.execute("SELECT 1 FROM video_likes WHERE video_id=? AND user_id=?", (video_id, user["id"])).fetchone()
    if existing:
        conn.execute("DELETE FROM video_likes WHERE video_id=? AND user_id=?", (video_id, user["id"]))
    else:
        conn.execute("INSERT INTO video_likes (video_id, user_id) VALUES (?, ?)", (video_id, user["id"]))
    conn.commit()
    conn.close()
    return redirect(url_for("reels"))


@app.route("/reels/<int:video_id>/save", methods=["POST"])
def save_video(video_id):
    user = require_login()
    if not user:
        return redirect(url_for("reels"))
    conn = get_db()
    existing = conn.execute("SELECT 1 FROM video_saves WHERE video_id=? AND user_id=?", (video_id, user["id"])).fetchone()
    if existing:
        conn.execute("DELETE FROM video_saves WHERE video_id=? AND user_id=?", (video_id, user["id"]))
        flash("Removed from your collection.", "success")
    else:
        conn.execute("INSERT INTO video_saves (video_id, user_id) VALUES (?, ?)", (video_id, user["id"]))
        flash("Saved to your collection.", "success")
    conn.commit()
    conn.close()
    return redirect(request.referrer or url_for("reels"))


@app.route("/reels/<int:video_id>/comment", methods=["POST"])
def comment_video(video_id):
    user = require_login()
    if not user:
        return redirect(url_for("reels"))
    text = request.form.get("text", "").strip()
    if text:
        conn = get_db()
        conn.execute("INSERT INTO video_comments (video_id, user_id, text) VALUES (?, ?, ?)", (video_id, user["id"], text))
        conn.commit()
        conn.close()
    return redirect(url_for("reels"))


@app.route("/my-collection")
def my_collection():
    user = require_login()
    if not user or not is_customer(user):
        return redirect(url_for("home"))
    conn = get_db()
    rows = conn.execute(f"""
        SELECT videos.*, users.name AS artisan_name FROM video_saves
        JOIN videos ON video_saves.video_id = videos.id
        LEFT JOIN artisans ON videos.artisan_id = artisans.id
        LEFT JOIN users ON artisans.user_id = users.id
        WHERE video_saves.user_id = ?
        ORDER BY videos.id DESC
    """, (user["id"],)).fetchall()
    videos = [dict(r) for r in rows]
    for v in videos:
        v["artisan_name"] = v["artisan_name"] or "Andy Team"
    conn.close()
    return render_template("my_collection.html", user=user, videos=videos, active_page="my_collection", auto_open_auth=False)


@app.route("/tipped-videos")
def tipped_videos():
    user = current_user()
    conn = get_db()
    rows = conn.execute(_video_with_artisan_query("WHERE videos.is_paid = 1")).fetchall()
    vlist = []
    for r in rows:
        v = dict(r)
        v["artisan_name"] = v["artisan_name"] or "Andy Team"
        vlist.append(v)
    conn.close()
    return render_template("tipped_videos.html", user=user, videos=vlist, active_page="tipped_videos", auto_open_auth=False)


@app.route("/notifications")
def notifications_page():
    user = require_login()
    if not user or not is_customer(user):
        return redirect(url_for("home"))
    conn = get_db()
    rows = conn.execute("""
        SELECT jobs.id AS job_id, jobs.title, jobs.status,
               (SELECT text FROM messages WHERE job_id = jobs.id ORDER BY id DESC LIMIT 1) AS last_text,
               (SELECT created_at FROM messages WHERE job_id = jobs.id ORDER BY id DESC LIMIT 1) AS last_at,
               (SELECT COUNT(*) FROM messages WHERE job_id = jobs.id AND sender_role != 'customer' AND read_by_customer = 0) AS unread
        FROM jobs WHERE jobs.customer_id = ?
        AND EXISTS (SELECT 1 FROM messages WHERE messages.job_id = jobs.id AND messages.sender_role != 'customer')
        ORDER BY last_at DESC
    """, (user["id"],)).fetchall()
    conn.close()
    return render_template("notifications.html", user=user, conversations=[dict(r) for r in rows],
                            active_page="notifications", auto_open_auth=False)


@app.route("/buy_video/<int:video_id>", methods=["POST"])
def buy_video(video_id):
    user = require_login()
    if not user or not is_customer(user):
        return redirect(url_for("learning_center"))
    if not user["is_pro"]:
        flash("Tipped videos are a Pro feature. Upgrade to Pro to unlock.", "error")
        return redirect(url_for("pro_page"))
    conn = get_db()
    v = conn.execute("SELECT * FROM videos WHERE id=?", (video_id,)).fetchone()
    if not v:
        conn.close()
        flash("Video not found.", "error")
        return redirect(url_for("learning_center"))
    already = conn.execute("SELECT 1 FROM video_purchases WHERE video_id=? AND user_id=?",
                            (video_id, user["id"])).fetchone()
    if already:
        conn.close()
        flash("You already own this video.", "success")
        return redirect(url_for("learning_center"))
    if user["wallet"] < v["price"]:
        conn.close()
        flash("Not enough CONNECT coins. Top up your wallet first.", "error")
        return redirect(url_for("learning_center"))

    conn.execute("UPDATE users SET wallet = wallet - ? WHERE id=?", (v["price"], user["id"]))
    conn.execute("INSERT INTO transactions (user_id, label, amount) VALUES (?, ?, ?)",
                 (user["id"], f"Bought video: {v['title']}", -v["price"]))
    conn.execute("INSERT INTO video_purchases (video_id, user_id) VALUES (?, ?)", (video_id, user["id"]))
    conn.commit()
    conn.close()
    flash("Video unlocked!", "success")
    return redirect(url_for("learning_center"))


@app.route("/pro", methods=["GET", "POST"])
def pro_page():
    user = require_login()
    if not user or not is_customer(user):
        return redirect(url_for("home"))
    if request.method == "POST":
        conn = get_db()
        fresh = conn.execute("SELECT wallet FROM users WHERE id=?", (user["id"],)).fetchone()
        if user["is_pro"]:
            conn.close()
            flash("You're already Pro.", "success")
            return redirect(url_for("pro_page"))
        if fresh["wallet"] < PRO_MEMBERSHIP_COST:
            conn.close()
            flash("Not enough CONNECT coins. Top up your wallet first.", "error")
            return redirect(url_for("pro_page"))
        conn.execute("UPDATE users SET wallet = wallet - ?, is_pro = 1 WHERE id=?", (PRO_MEMBERSHIP_COST, user["id"]))
        conn.execute("INSERT INTO transactions (user_id, label, amount) VALUES (?, 'Upgraded to Andy Pro', ?)",
                     (user["id"], -PRO_MEMBERSHIP_COST))
        conn.commit()
        conn.close()
        flash("Welcome to Andy Pro! ⭐", "success")
        return redirect(url_for("pro_page"))
    return render_template("pro.html", user=user, pro_cost=PRO_MEMBERSHIP_COST,
                            active_page="pro", auto_open_auth=False)


# ---------------------------------------------------------------------------
# OUR WORK (admin-posted portfolio)
# ---------------------------------------------------------------------------

@app.route("/works", methods=["GET", "POST"])
def works():
    user = current_user()
    if request.method == "POST":
        if not is_owner(user):
            flash("Only Andy can post completed works.", "error")
            return redirect(url_for("works"))
        title = request.form.get("title", "").strip()
        description = request.form.get("description", "").strip()
        if not title:
            flash("Give the project a title.", "error")
            return redirect(url_for("works"))
        conn = get_db()
        cur = conn.execute("INSERT INTO work_posts (title, description) VALUES (?, ?)", (title, description))
        work_id = cur.lastrowid
        for f in request.files.getlist("photos"):
            stored, kind = _save_attachment(f, WORKS_UPLOAD_DIR)
            if stored and kind == "image":
                conn.execute("INSERT INTO work_photos (work_id, filename) VALUES (?, ?)", (work_id, stored))
        conn.commit()
        conn.close()
        flash("Work posted.", "success")
        return redirect(url_for("works"))

    conn = get_db()
    rows = conn.execute("SELECT * FROM work_posts ORDER BY id DESC").fetchall()
    posts = []
    for r in rows:
        w = dict(r)
        photos = conn.execute("SELECT * FROM work_photos WHERE work_id=?", (w["id"],)).fetchall()
        w["photos"] = [dict(p) for p in photos]
        posts.append(w)
    conn.close()
    return render_template("works.html", user=user, work_posts=posts, is_owner_view=is_owner(user),
                            active_page="works", auto_open_auth=False)


@app.route("/works/delete/<int:work_id>", methods=["POST"])
def delete_work(work_id):
    user = current_user()
    if not is_owner(user):
        return redirect(url_for("works"))
    conn = get_db()
    photos = conn.execute("SELECT * FROM work_photos WHERE work_id=?", (work_id,)).fetchall()
    for p in photos:
        if not p["filename"].startswith("http"):
            try:
                os.remove(os.path.join(WORKS_UPLOAD_DIR, p["filename"]))
            except OSError:
                pass
    conn.execute("DELETE FROM work_photos WHERE work_id=?", (work_id,))
    conn.execute("DELETE FROM work_posts WHERE id=?", (work_id,))
    conn.commit()
    conn.close()
    flash("Work post removed.", "success")
    return redirect(url_for("works"))


# ---------------------------------------------------------------------------
# WALLET + PAYSTACK
# ---------------------------------------------------------------------------

@app.route("/wallet", methods=["GET", "POST"])
def wallet():
    user = require_login()
    if not user or not is_customer(user):
        return redirect(url_for("home"))
    if request.method == "POST":
        try:
            naira_amount = int(request.form.get("amount", 0))
        except ValueError:
            naira_amount = 0
        if naira_amount <= 0:
            flash("Enter a valid amount.", "error")
            return redirect(url_for("wallet"))
        return redirect(url_for("paystack_initiate", naira_amount=naira_amount))

    conn = get_db()
    txs = conn.execute("SELECT * FROM transactions WHERE user_id=? ORDER BY id", (user["id"],)).fetchall()
    user_fresh = dict(conn.execute("SELECT * FROM users WHERE id=?", (user["id"],)).fetchone())
    conn.close()
    user_fresh["transactions"] = [dict(t) for t in txs]
    return render_template("wallet.html", user=user_fresh, active_page="wallet", auto_open_auth=False)


@app.route("/paystack/initiate/<int:naira_amount>")
def paystack_initiate(naira_amount):
    user = require_login()
    if not user:
        return redirect(url_for("home"))
    kobo_amount = naira_amount * 100
    try:
        resp = requests.post(
            "https://api.paystack.co/transaction/initialize",
            headers={"Authorization": f"Bearer {PAYSTACK_SECRET_KEY}", "Content-Type": "application/json"},
            json={"email": user["email"], "amount": kobo_amount,
                  "callback_url": url_for("paystack_verify", _external=True),
                  "metadata": {"user_id": user["id"], "naira_amount": naira_amount}},
            timeout=10,
        )
        data = resp.json()
    except Exception:
        flash("Couldn't reach Paystack. Check your API keys and internet connection.", "error")
        return redirect(url_for("wallet"))
    if not data.get("status"):
        flash(f"Paystack error: {data.get('message', 'Unknown error.')}", "error")
        return redirect(url_for("wallet"))
    return redirect(data["data"]["authorization_url"])


@app.route("/paystack/verify")
def paystack_verify():
    user = require_login()
    if not user:
        return redirect(url_for("home"))
    reference = request.args.get("reference") or request.args.get("trxref")
    if not reference:
        flash("No payment reference found.", "error")
        return redirect(url_for("wallet"))

    conn = get_db()
    already = conn.execute("SELECT 1 FROM transactions WHERE user_id=? AND label LIKE ?",
                            (user["id"], f"%ref:{reference}%")).fetchone()
    if already:
        conn.close()
        flash("This payment was already processed.", "success")
        return redirect(url_for("wallet"))

    try:
        resp = requests.get(f"https://api.paystack.co/transaction/verify/{reference}",
                             headers={"Authorization": f"Bearer {PAYSTACK_SECRET_KEY}"}, timeout=10)
        data = resp.json()
    except Exception:
        conn.close()
        flash("Couldn't verify payment with Paystack.", "error")
        return redirect(url_for("wallet"))

    if data.get("status") and data["data"]["status"] == "success":
        naira_paid = data["data"]["amount"] / 100
        coins = int(naira_paid * CONNECT_COINS_PER_NAIRA)
        conn.execute("UPDATE users SET wallet = wallet + ? WHERE id=?", (coins, user["id"]))
        conn.execute("INSERT INTO transactions (user_id, label, amount) VALUES (?, ?, ?)",
                     (user["id"], f"Wallet top-up (₦{naira_paid:.0f} via Paystack, ref:{reference})", coins))
        conn.commit()
        conn.close()
        flash(f"Payment confirmed! {coins} CONNECT added to your wallet.", "success")
    else:
        conn.close()
        flash("Payment wasn't successful. No coins were added.", "error")
    return redirect(url_for("wallet"))


# ---------------------------------------------------------------------------
# SETTINGS
# ---------------------------------------------------------------------------

@app.route("/settings", methods=["GET", "POST"])
def settings():
    user = require_login()
    if not user:
        return redirect(url_for("home"))
    if request.method == "POST":
        form_type = request.form.get("form_type", "theme")
        conn = get_db()
        if form_type == "profile":
            bio = request.form.get("bio", "").strip()
            avatar_value = None
            file = request.files.get("avatar")
            if file and file.filename:
                stored, kind = _save_attachment(file, AVATARS_UPLOAD_DIR)
                if stored and kind == "image":
                    avatar_value = stored
            if avatar_value:
                conn.execute("UPDATE users SET bio=?, avatar_filename=? WHERE id=?", (bio, avatar_value, user["id"]))
            else:
                conn.execute("UPDATE users SET bio=? WHERE id=?", (bio, user["id"]))
            conn.commit()
            conn.close()
            flash("Profile updated.", "success")
            return redirect(url_for("settings"))
        if form_type == "password":
            current_password = request.form.get("current_password", "")
            new_password = request.form.get("new_password", "")
            row = conn.execute("SELECT * FROM users WHERE id=?", (user["id"],)).fetchone()
            if not check_password_hash(row["password_hash"], current_password):
                conn.close()
                flash("Current password is incorrect.", "error")
                return redirect(url_for("settings"))
            if len(new_password) < 6:
                conn.close()
                flash("New password must be at least 6 characters.", "error")
                return redirect(url_for("settings"))
            conn.execute("UPDATE users SET password_hash=? WHERE id=?",
                         (generate_password_hash(new_password), user["id"]))
            conn.commit()
            conn.close()
            flash("Password updated.", "success")
            return redirect(url_for("settings"))
        else:
            theme = request.form.get("theme")
            appearance = request.form.get("appearance")
            if theme is not None:
                if theme not in ("purple", "teal", "green"):
                    theme = "green"
                conn.execute("UPDATE users SET theme=? WHERE id=?", (theme, user["id"]))
                conn.commit()
                flash("Theme updated.", "success")
            elif appearance is not None:
                dark = 1 if appearance == "dark" else 0
                conn.execute("UPDATE users SET dark_mode=? WHERE id=?", (dark, user["id"]))
                conn.commit()
                flash("Appearance updated.", "success")
            conn.close()
            return redirect(url_for("settings"))
    return render_template("settings.html", user=user, active_page="settings", auto_open_auth=False)


if __name__ == "__main__":
    init_db()
    app.run(debug=FLASK_DEBUG)
