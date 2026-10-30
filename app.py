from flask import Flask, render_template, request, redirect, url_for, session, flash, Response, send_from_directory, jsonify
from jinja2 import DictLoader
from werkzeug.security import generate_password_hash, check_password_hash
from werkzeug.utils import secure_filename
import sqlite3
from datetime import datetime
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
_SECRET_KEY_ENV = os.environ.get("SECRET_KEY")
if _SECRET_KEY_ENV:
    app.secret_key = _SECRET_KEY_ENV
else:
    # No SECRET_KEY set — generate a random one for this process instead of
    # falling back to a fixed value (a fixed fallback baked into the source
    # code is effectively a leaked key). Everyone's sessions reset whenever
    # the server restarts until a real SECRET_KEY is set as an environment
    # variable — set one on Render before going live.
    app.secret_key = pysecrets.token_hex(32)
    print("[ANDY] WARNING: no SECRET_KEY environment variable set — using a "
          "temporary random key for this run. Sessions will reset on every "
          "restart. Set SECRET_KEY as an environment variable before going live.")

# ---------------------------------------------------------------------------
# SECURITY HARDENING
# ---------------------------------------------------------------------------
# Debug mode now defaults OFF and must be explicitly enabled — leaving
# Flask's debugger reachable in production allows remote code execution.
FLASK_DEBUG = os.environ.get("FLASK_DEBUG", "0") == "1"

# Cap request size so a huge upload can't be used to exhaust memory/disk.
app.config["MAX_CONTENT_LENGTH"] = 100 * 1024 * 1024  # 100 MB (videos with sound)

# Session cookie hardening. SESSION_COOKIE_SECURE is left off by default so
# local HTTP testing keeps working — set FORCE_HTTPS=1 once this is served
# over HTTPS (Render, your own domain, etc.) so the session cookie is only
# ever sent over an encrypted connection.
app.config["SESSION_COOKIE_HTTPONLY"] = True
app.config["SESSION_COOKIE_SAMESITE"] = "Lax"
app.config["SESSION_COOKIE_SECURE"] = os.environ.get("FORCE_HTTPS", "0") == "1" or bool(os.environ.get("RENDER"))


@app.after_request
def set_security_headers(response):
    response.headers["X-Content-Type-Options"] = "nosniff"
    response.headers["X-Frame-Options"] = "DENY"
    response.headers["Referrer-Policy"] = "strict-origin-when-cross-origin"
    response.headers["Permissions-Policy"] = "camera=(self), microphone=(), geolocation=()"
    if request.is_secure or request.headers.get("X-Forwarded-Proto") == "https":
        response.headers["Strict-Transport-Security"] = "max-age=15552000"
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
    "service_worker", "about_art", "services", "push_icon", "push_key", "push_subscribe", "push_unsubscribe", "set_mode", "terms", "privacy", "staff_login",
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
        url = data.get("secure_url")
        if not url:
            print("[ANDY] Cloudinary upload failed:", data.get("error", data))
            _rewind(file_storage)
        return url
    except Exception as exc:
        print("[ANDY] Cloudinary upload error:", exc)
        _rewind(file_storage)
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
        url = data.get("secure_url")
        if not url:
            print("[ANDY] Cloudinary upload failed:", data.get("error", data))
            _rewind(file_storage)
        return url
    except Exception as exc:
        print("[ANDY] Cloudinary upload error:", exc)
        _rewind(file_storage)
        return None


def upload_video_media(file_storage):
    return upload_video_to_cloudinary(file_storage)



# ---------------------------------------------------------------------------
# EMAIL ALERTS — the owner is emailed on every new customer/artisan message
# and every feedback / bug report. Uses plain SMTP (Gmail works with an
# "App Password"). Set these as environment variables:
#   SMTP_USER=yourgmail@gmail.com   SMTP_PASSWORD=<16-char app password>
# Optional: NOTIFY_EMAIL (who receives alerts), SMTP_HOST, SMTP_PORT.
# ---------------------------------------------------------------------------
import smtplib
import threading
from email.message import EmailMessage

NOTIFY_EMAIL = os.environ.get("NOTIFY_EMAIL", "oladimejipamilerin714@gmail.com")
SMTP_HOST = os.environ.get("SMTP_HOST", "smtp.gmail.com")
SMTP_PORT = int(os.environ.get("SMTP_PORT", "587"))
SMTP_USER = os.environ.get("SMTP_USER", "")
SMTP_PASSWORD = os.environ.get("SMTP_PASSWORD", "")


def email_configured():
    return bool(SMTP_USER and SMTP_PASSWORD and NOTIFY_EMAIL)


def _send_email_blocking(to, subject, body):
    msg = EmailMessage()
    msg["Subject"] = " ".join(str(subject).split())[:200]
    msg["From"] = SMTP_USER
    msg["To"] = to
    msg.set_content(body)
    with smtplib.SMTP(SMTP_HOST, SMTP_PORT, timeout=15) as server:
        server.starttls()
        server.login(SMTP_USER, SMTP_PASSWORD.replace(" ", ""))
        server.send_message(msg)


def send_email_async(to, subject, body):
    """Fire-and-forget so chatting never waits on the mail server."""
    if not email_configured():
        print("[ANDY] Email alert skipped (set SMTP_USER and SMTP_PASSWORD):", subject)
        return None

    def _run():
        try:
            _send_email_blocking(to, subject, body)
        except Exception as exc:
            print("[ANDY] Email alert failed:", exc)

    t = threading.Thread(target=_run, daemon=True)
    t.start()
    return t


def _notify_owner_of_message(sender, job, text, attachment_kind):
    category = (job.get("category") or "")
    name = sender.get("name") or "Someone"
    if category == "Feedback":
        subject = f"💡 New feedback from {name}"
    elif category == "Bug Report":
        subject = f"🐞 New bug report from {name}"
    else:
        subject = f"💬 New message from {name}"
    link = url_for("job_thread", job_id=job["id"], _external=True)
    body = (
        f"{name} ({sender.get('role', 'user')}) wrote in \"{job.get('title', 'a chat')}\":\n\n"
        f"{text or '(sent an attachment)'}\n"
        + (f"\n[attachment: {attachment_kind}]\n" if attachment_kind else "")
        + f"\nReply here: {link}\n"
    )
    send_email_async(NOTIFY_EMAIL, subject, body)


def _rewind(file_storage):
    """After a failed cloud upload, rewind so the local-disk fallback saves the full file."""
    try:
        file_storage.stream.seek(0)
    except Exception:
        pass


print("[ANDY] Cloudinary:", "ON" if cloudinary_configured() else "OFF — set CLOUDINARY_CLOUD_NAME / _API_KEY / _API_SECRET (uploads use local disk)")
print("[ANDY] Email alerts:", f"ON -> {NOTIFY_EMAIL}" if email_configured() else "OFF — set SMTP_USER and SMTP_PASSWORD")

# ---------------------------------------------------------------------------
# WEB PUSH — browser notifications (like Temu on the web). They appear even
# when the ANDY tab is closed. Needs HTTPS (Render has it) and `pywebpush` in
# requirements.txt. VAPID keys are created automatically the first time and
# kept in the database; set VAPID_PUBLIC_KEY / VAPID_PRIVATE_KEY to override.
# ---------------------------------------------------------------------------
import base64
import json as _json

_VAPID_CACHE = {}


def _b64url(raw):
    return base64.urlsafe_b64encode(raw).rstrip(b"=").decode()


def get_vapid_keys():
    """Return (public, private) VAPID keys, generating and storing them once."""
    if _VAPID_CACHE:
        return _VAPID_CACHE["pub"], _VAPID_CACHE["priv"]
    pub, priv = os.environ.get("VAPID_PUBLIC_KEY", ""), os.environ.get("VAPID_PRIVATE_KEY", "")
    if not (pub and priv):
        conn = get_db()
        rows = {r["k"]: r["v"] for r in conn.execute("SELECT k, v FROM app_kv WHERE k IN ('vapid_pub', 'vapid_priv')").fetchall()}
        pub, priv = rows.get("vapid_pub", ""), rows.get("vapid_priv", "")
        if not (pub and priv):
            try:
                from cryptography.hazmat.primitives.asymmetric import ec
                from cryptography.hazmat.primitives import serialization
                key = ec.generate_private_key(ec.SECP256R1())
                priv = _b64url(key.private_numbers().private_value.to_bytes(32, "big"))
                pub = _b64url(key.public_key().public_bytes(
                    serialization.Encoding.X962, serialization.PublicFormat.UncompressedPoint))
                conn.execute("INSERT INTO app_kv (k, v) VALUES ('vapid_pub', ?)", (pub,))
                conn.execute("INSERT INTO app_kv (k, v) VALUES ('vapid_priv', ?)", (priv,))
                conn.commit()
            except Exception as exc:
                print("[ANDY] Could not create push keys:", exc)
                pub = priv = ""
        conn.close()
    if pub and priv:
        _VAPID_CACHE.update(pub=pub, priv=priv)
    return pub, priv


def _push_blocking(subs, payload):
    try:
        from pywebpush import webpush, WebPushException
    except ImportError:
        print("[ANDY] Push skipped: add `pywebpush` to requirements.txt")
        return
    pub, priv = get_vapid_keys()
    if not priv:
        return
    dead = []
    for sub in subs:
        try:
            webpush(
                subscription_info={"endpoint": sub["endpoint"], "keys": {"p256dh": sub["p256dh"], "auth": sub["auth"]}},
                data=_json.dumps(payload),
                vapid_private_key=priv,
                vapid_claims={"sub": VAPID_SUBJECT},
                ttl=86400,
            )
        except WebPushException as exc:
            status = getattr(getattr(exc, "response", None), "status_code", None)
            if status in (404, 410):
                dead.append(sub["endpoint"])
            else:
                print("[ANDY] Push failed:", exc)
        except Exception as exc:
            print("[ANDY] Push error:", exc)
    if dead:
        conn = get_db()
        for ep in dead:
            conn.execute("DELETE FROM push_subscriptions WHERE endpoint=?", (ep,))
        conn.commit()
        conn.close()


def send_push_to_users(user_ids, payload):
    """Look up the users' devices, then send in the background so chat never waits."""
    user_ids = [u for u in set(user_ids) if u]
    if not user_ids:
        return None
    conn = get_db()
    marks = ",".join("?" for _ in user_ids)
    subs = [dict(r) for r in conn.execute(
        f"SELECT endpoint, p256dh, auth FROM push_subscriptions WHERE user_id IN ({marks})", tuple(user_ids)).fetchall()]
    conn.close()
    if not subs:
        return None
    t = threading.Thread(target=_push_blocking, args=(subs, payload), daemon=True)
    t.start()
    return t


def _notify_push(sender, job, text, attachment_kind):
    conn = get_db()
    owners = [r["id"] for r in conn.execute("SELECT id FROM users WHERE role='owner'").fetchall()]
    art_user = None
    if job.get("artisan_id"):
        row = conn.execute("SELECT user_id FROM artisans WHERE id=?", (job["artisan_id"],)).fetchone()
        art_user = row["user_id"] if row else None
    conn.close()
    role = sender.get("role")
    if role == "customer":
        ids = owners + [art_user]
    elif role == "owner":
        ids = [job.get("customer_id"), art_user]
    else:
        ids = [job.get("customer_id")] + owners
    ids = [i for i in ids if i and i != sender["id"]]
    category = job.get("category") or ""
    name = sender.get("name") or "Someone"
    if category == "Feedback":
        title = f"💡 Feedback from {name}"
    elif category == "Bug Report":
        title = f"🐞 Bug report from {name}"
    else:
        title = f"💬 {name}"
    body = (text or "").strip()[:140] or "📎 Sent an attachment"
    send_push_to_users(ids, {
        "title": title, "body": body,
        "url": url_for("job_thread", job_id=job["id"]), "tag": f"job-{job['id']}",
    })


def _notify_owner_new_request(sender, job, text, kind="service request"):
    """Email + push the owner when a customer opens a new request. Never raises:
    a failed alert must not turn a saved request into an error for the customer."""
    try:
        name = sender.get("name") or "A customer"
        link = url_for("job_thread", job_id=job["id"], _external=True)
        body = (f"{name} sent a new {kind}: \"{job.get('title', '')}\"\n\n"
                f"{(text or '').strip()[:1500]}\n\nOpen it here: {link}\n")
        send_email_async(NOTIFY_EMAIL, f"📋 New {kind} from {name}", body)
        _notify_push(sender, job, f"New {kind}: {job.get('title', '')}", None)
    except Exception as exc:
        print("[ANDY] New-request alert failed:", exc)


VAPID_SUBJECT = os.environ.get("VAPID_SUBJECT", "mailto:" + NOTIFY_EMAIL)
PUSH_ICON_PNG = base64.b64decode("iVBORw0KGgoAAAANSUhEUgAAAMAAAADACAYAAABS3GwHAAARkklEQVR42u2dXYxc5XnHf+97zpmZ/V6zBvNlQDZgL3a3a2yLxJgorZRAQAiBUr4kZAJucAjpVW+qVL1Ie9mLXlSRHHERGqS2l2maChKprSogIQ4EWUFuSGmjhhSIA8bG6905H+/biznHPrusvTu7s7szZ/4/aWxrdjwen3n+z9d53/cxrC0GCIAM8KXnh8JGOIVnymBuAg4AEXAzMJq/1iCqRPGdngHeAhLgFY//JYbj6Vx6HJhZhu103EDXAps/0uKJWq026XCfw3AQzz5jzA0yclGIw3v/Kww/xfOSxf4wjuMTpZ+HgMsfXS0Akxt+1vLzbInS6D7gceA2DHaBlt0Cb28kir6IBH5BVLDzLMjjgFeBbydh8l1meD//aVCyma4SwDzDj6JoN5ZDeB7DsKX0urRk5Fa2IBZxhj73+IVE3sfwHRzPJUny804LoRMCsOdD0xBXREn05xiewlDLP15WMnp5d9FOlPBAkEeFGM/RJEr+ihl++wnbWyHBKj9oocQorIdfDVzwDxj+MH8+LXl6Gb9o1zEXtuNzJxphuC1wwSEb2qbL3M/y54PVRAKzir9ngSyKoluxfBPDbSWPb2XwYg2igitFhFdxPJ0kyeurSYlWEgGK3N1F9egwhr8Hti3i8YVYiwZLERGuw/BoEAYnXeZeW/DzNYsARc4VRrXobzE8lT+fdSCdEqIdLtic52gSJ8/kTritusCswPg3RfXoe8DtSndE16RF8HLSTO4FTrUjArMC438R2J+rLdR3ILqAwhaPJc3kznZEYGX8ogKEuU3uz210U26zS9q3WaZAxqN69IKMX/RQJLgL+Ch/3q1EAEVV7aJ69ArwKRm/6CER/DhpJgdKGcyi3aFgibCSRbXoKIb7ZPyiRygWYV4XBMFVLnP/xIXFdMsWQABkUT36EpZvyPhFT4rAsj8Igv91mStulvnlpECttCeKprC8AjRQq1P0HkWLdA7HgSRJjrNIZ8guIggDhN7654ChZRbLQnQbhc0O5bYcssiaNLuI98/CenjEYKbz1Ed3eEWvEgCpwUyH9fAIF27cLpoCFX8ej+rR28AYWsUpqpEKeeB00ky2c6E16hcWwQHgolr01xg+wzJvJAjRA6mQAwaDIBh2mfuXckFsSqmPr9VqO73xx9EaflHNKOCMN1NxHP9nIQxbFoA3/jDmfM9Uxi+qFQUMoTf+cC4GywIvPxHVojcxXL5IfSBEFaIAeE4mcbIL+KDw/AHgo3r0AJYr5P1FpaOA5YqoHj2QCyKwJYM/jF+7A4iE6JI44IHD5RrAUeNmYDp/ifr+oqoUtj2d23yrCA4J78IQURxoJUR1yTBEIeFdRQ0AnoN58qPcX1S/FvC5zecCGDbG7M9/qBtfouq02p8tmx+2YRhOYrgWncgs+iUCgMdwbRiGk5aAvazydC0heozWkYsBe63BTJaeFKJfBIDBTFpaG91VAIt+S4MA9lu01VH0L6GJ6tFpNJZI9F8KZIAzJqpHyv1F39L2abpCVCkS6LQH0dfFsO78ir5PgcSG+R/FXwmgn8k8pCrBJIC+u+oG10wZOHgtY09M4ZoJBAoFEkC/4MEEhtFHb2H08d2EVwxBkikdkgD6gMDi5mKG77mRxr6rsIMR40/twSUZWH0dEkDVi94kJZwYZPzIHlwzxZ2NGbp7O43dW/DNBKzCgARQ2attcUnGyIOThFtHIc7Agx2IGP/KnlZRLCSAqha+fi6htu0yRh/bhTvTbB3KYQ3u4yaNA9cw9PltuNk4P6xDSACVK349Y09OYQdrn/T2qWP8yDTBWAMyFcQSQKUKX4ObjWnsv4ahe7bjPm7Ob3tagz+XEO2YYPShW3DNVAWxBFAhMo+thYw/PX3xG1+BxZ1uMvLIJLUbNuHjBIzCgATQ897f4poJw/fvoLH3Kvy5ePFOjwHSjGDzIGOHduNTp46QBNDjGPBJSnjZIGOHp3AzyaVTm8DiPppj6N4bGdh/DW62KRFIAL18dQ0+yRh7cqp1tzdOl1XcmsAy9sTvYQKdUikB9LLxz6XUbpxg+IEduLPLbG/mbdGBg1sZ/sJ2tUUlgB7GeTZ97VZsIwTn2xPPbMro47sJxgbUFpUAes/7u9mYgdu3MnDH1pb3byeXNwY/m1DbuZnRhybVFpUAes/z20bEpj+5dcFY5jYot0WvH9c6IQmgR8jbnqOP7qJ2y+UXb3suGQVotUUnBhh/ak97KZSQADaEYrXnlhFGHp5cuu25zCgwePc2GvuvyQtiRQEJoGuvZmu15/iXpwmvHF5223NJUs/409PYRqQVoxJA9xa+fi6msXsLQ3dvy9f72M6877mYxr6rWqtFm4naohJA90aA8WdW0PZcTmQ5mzB+ZJpwYgiSVG1RCaDLCt/ZmOEvbGfg9mta3r+THRsDxCnh1lFGHtyp7ZMSQJcVvllGMDbA6OO78bPZ2rQrA4s702T0sV3Utl2Gn1NbVALolsK3mTL60CS1nZvxs2u4jDnz2MEaY09OgVcxLAFsuPc3+DihdsMmRh6ZxJ1urm2BGrTWCQ3ds11tUQmgG66ewaeOsUO7CTYPQrpOa3aKtmgtVFtUAtg443fnmgzsu5qhe2/EfTS3Pu3Joi269yqG79+htqgEsEHk633Gn9m7/lsXrcXNJIwdniK8bBCvtqgEsK7k632GPr+Nxr4r8TPx+nZkirboFUOMPTmFTzJ1hCSAdTS+JCWcGGL8yDTubLIxPfnA4s7GDD+wg9qNE/i5VCKQANYp/UgyRh7cmZ/utoHph/PYRsimr92q1aISwPoUvoue7raRhfjZmIE7tjJw+9ZWW1RRQAJYS7y7xOluG1aQ09p6WQsVCSSANfS2szGDt29l6O5FTnfbyKh0LqY2uVltUQlgjfPtWp5vd9tYI2vxs+n5tqhWi0oAnaV0ulttcjO+23JtA75oiz4xla8WlQIkgA4ZF6XT3fxsl57QULRFv7gjH7ahtqgE0KncP8kYe6J1upuPuzi9yPK70xq2IQF0rMBspjR2b2H4i22c7rZhUSAftvHpq0vDNhQFJIBVetXxr+zprQ3pDsYOT2kTvQSwSm86G7fW+3z66u5pey4nap2Lqe2cYPTRXWqLSgCry6fHDk+t/HS3DftWLf5cysjDk4RbRtQWlQDa9f6l0912Tqz8dLeNomiLXjnM+JentYleAmjTeJKUcMtw63S3cz16MG1gW9sn796mGcQSQDsCaA21GP/jacItQzCXtDagu3V6dDqN0wziSxLqEswvIN1cwuAd1zPy8CR+LsWM1Ncvf/a0bmB1ylaD+TOIz/7gbexgHTKn77rwd1E9kmsoe//MUbt+jODKodZOq/Xa7pg57HCNia8fwAzl7ctO/NPOYxoh6a/P8O6Xvt/aOGNM50SmCFAhvMdYQ/z2Kfx/fbD+aftAHZ86jDF0zEIXzCA+9a3XFQUkgCUCQT1c333uBkgdZjham3SrNGxj5gf/Q/LOaUwY6nAtFcEXjwTrVvSuZRE8T2CaQSwB9DOaQdxjKZA5/0v1ostGXtZ8BvHcz96TU+hmAfjUterADtaDGy5oDyYw63+QVqkgLs8g/vh7b/V9Qdy1AghHGtjQVqtdZyCdifEbaXClGcTn/uPXrWPW+7gt2nUCMNaQzsbs/ZsH2XzwJpKzc5gK5KreecLBOseOPM/JH71NNFDDb8QJDgtmEPd7W7SrI0DtskFMaFtpQ68LIPOEw3VMGHRHQVy0RV/8b5J3zmD69EiVrq4BfJLh0wxcNSKAT7Lu6L0vmEF88uv/3rc1QPe2QU0rXFfu0S1oBnGXC0CsD30+g1gC6Gc0g1gCkAj6ewaxBNDv9PkMYglA9PUMYglAtOjTGcQSgMijQH/OIJYAxHz6bAaxBCBK1tB/M4glALHAIvprBrEEIObTZzOIJQCxSEHcPzOIJQCxOH0yg1gCEBctiPthBrEEIJaIBNWeQSwBiEtGgarPIJYAxBIWUu0ZxBKAuDQVn0EsAYilqfAMYglALI+KziCWAMQyo0A1ZxBLAKI9KjaDWAIQbVhL9WYQSwCiTYup1gxiCUC0R8VmEEsAYgUFcXVmEEsAYmVUZAaxBCBWGAXmzyButUWtBCD6jNQxfmSaYKwBWdZzBbEEIFZhPfNnELtm2nMFsQQgVl8Q58M2ajdswsdJdx0DLwGINaXHZxBLAKIzUaBHZxBLAKJzwSCfQWyCoGc+swQgOlYQl2cQ90pbVAIQHRVBMYM4GBvoibaoBCA6mAPNn0HcC21RCUB0viAu2qLXj3f9OiEJQHQ4CjBvBnG3nyUkAYi1iQIf9cYM4lDfVpfh/IVHL2+59R4Sx/iR36f5xntdu2JUAuiy9MEMRpihCFLX+wdQpY6Bz1zH8P07OPOPb2IHa10nBAmgK7wl+cKylJN/+q+t/rmn9wXgPSafQGmj7jxbVALoGu9v8Klj7ti7eKp1CK3BYOoh3fjfkgC6LQUaiKo3kcjTtaNXJYBuLILFuqE2qOhrujcCFGHTeyqREhf/FyEBLCsdDi0mCjBhgKnCxPLMY6Kgp3ZLSQAbSPrxHPGH50jOzmEqcBS3dx4XZ/g0k9V1k6ON6lFXxuVgsIYNLZXqCBpIZ2J85mR5EsASHjNzF24G+WoYP55WOqc0SCnQcmoAqKChqBCWAJZnKAAyFrG2WFmZ6GN8RfMMIZaXaVvgTDnpEKIfPH/++xkL/EICEH0qgF9YINX1EH1KaoFjigCiTyPAMevxJ4qCQNdF9Evx21KBP2HJeA3IJADRZwLIyHjNpml6As87VGfRgRBLpT8Gzztpmp6wwFnvfVEHaJWWqDoOILf5szYPCC/lCZAigKh+BDC5zZNviUxJX8CTAIGuj6g4AZ4kJX2hEIAl5i3gjfwF2rEhqkph22/kNm8tFxbEPYtRJ0hUnJaNP8v548gutD8nolr0JobLz79UiCrl/q1fTyZxsgv4gJL3D4DfYXg+V4jSIFG99MdgMDwP/C63eV+cC+QAY7x5Fk+K9gmI6nl/iyc13jybZzeuiACFAGwcxyfwHM2f1z0BURVcLoCjcRyfKNu3mVcetBiP6tHbwFj+nGoB0eve3wOnk2ayHfioXBPYT4QJOOXxf5H/WbWA6P3cH2xu06cWpvcLvbvJX2DCenjMYKbzN9ANMtGrxh94/BtpM92fG74rC8BeJFykxplDwEw5XAjRY6kPwExuy2nJvs8TXOQvBs6594IweBfD/UUY0TUVPeX9DSFwJImTF3Nb/0RjJ7iEekKXudcDG1yNYX+uIIlA9AIpEOL5VhInf0nr/KtF69lLdXiKesBF9egV4FPn31iIbjd++HHSTA5woeW5aBpvl8ihPGCSZnIPrb3DIdpEL7rf+I/lNmsWy/uXKwBKOdOHSTO5UyIQPWL8dwIfLrDhFQmgeAMLnJIIRI8Y/ymWuZphuUXtQhG8XCos1CIVG4XPbTAEXm7X+NsRwEIRfDZfMxSAVo+KDaE4ySTAczRpJp9t1/ih/Tu8xXIJ5zL3z0EY/Ab4A6CRhyGtHRLr6fU/Bp5J4uQbZdts582CFX4AAwQuc68FNngRwzSG60rRQEIQa2H4rSzEYIFXcfxREiffz+3YryQdD1b5gQLn3P+5zD1nA3vSYPYCI7nxKyKITnr8IPfwv/X4P0ub6Vedc7/Jn19xCh504MNZIHOZ+4lruL8LsqCBYQ+GaJH6QGIQy7WrhR4/xvPNJEoecbPu30o16ar2rXTKIIu7xhlAFEW7sRzC8xiGLaXXlaOCllWIhU2WwvDDkhTex/AdHM8lSfLzkuN2dKAD2WmPPE8IDLElSqP7gMeB2zDYBR/ZlWoKlDL1lXcv15N2ngV5HPAq8O0kTL7LDO932vDXOiUpjls5f7OsVqtNOtznMBzEs88Yc4OMXRRC8N7/CsNP8bxksT/Mty4WhLnhd3yb7loboCkVKWXVDoWNcArPlMHcBBwAIuBmYHRBVBDV8fyG1kiut4AEeMXjf4nheDqXHufC/pNL2U5H+X9q+Gtc9mSKHgAAAABJRU5ErkJggg==")

SERVICE_WORKER_JS = """
self.addEventListener('install', function(e) { self.skipWaiting(); });
self.addEventListener('activate', function(e) { e.waitUntil(self.clients.claim()); });

self.addEventListener('push', function(event) {
  var data = {};
  try { data = event.data ? event.data.json() : {}; } catch (e) {}
  var url = data.url || '/';
  event.waitUntil(
    self.clients.matchAll({ type: 'window', includeUncontrolled: true }).then(function(list) {
      for (var i = 0; i < list.length; i++) {
        var c = list[i];
        try { if (c.focused && new URL(c.url).pathname === url) return; } catch (e) {}
      }
      return self.registration.showNotification(data.title || 'ANDY', {
        body: data.body || '',
        icon: '/push-icon.png',
        badge: '/push-icon.png',
        tag: data.tag || 'andy',
        renotify: true,
        data: { url: url }
      });
    })
  );
});

self.addEventListener('notificationclick', function(event) {
  event.notification.close();
  var url = (event.notification.data && event.notification.data.url) || '/';
  event.waitUntil(
    self.clients.matchAll({ type: 'window', includeUncontrolled: true }).then(function(list) {
      for (var i = 0; i < list.length; i++) {
        if ('focus' in list[i]) { list[i].navigate(url); return list[i].focus(); }
      }
      return self.clients.openWindow(url);
    })
  );
});
"""


STAFF_LOGIN_HTML = """<!DOCTYPE html><html><head><meta charset="UTF-8"><meta name="viewport" content="width=device-width, initial-scale=1.0"><title>ANDY staff login</title>
<style>body{margin:0;background:#0A1020;color:#fff;font-family:-apple-system,Segoe UI,sans-serif;display:flex;align-items:center;justify-content:center;min-height:100vh;padding:20px}
.box{width:100%;max-width:340px}h1{font-size:22px;margin:0 0 6px}p{color:#9ca3af;font-size:14px;margin:0 0 18px}
input{width:100%;box-sizing:border-box;padding:14px;margin-bottom:12px;border-radius:10px;border:1px solid #1E2D4A;background:#111A2E;color:#fff;font-size:16px}
button{width:100%;padding:14px;border:none;border-radius:10px;background:#22C55E;color:#04140A;font-weight:700;font-size:16px;cursor:pointer}a{color:#22C55E;font-size:13px}</style></head>
<body><form class="box" method="POST" action="/login"><input type="hidden" name="csrf_token" value="__TOKEN__">
<h1>Staff login</h1><p>For the ANDY owner and team.</p>
<input type="email" name="email" placeholder="Email" autocomplete="username" required>
<input type="password" name="password" placeholder="Password" autocomplete="current-password" required>
<button type="submit">Log in</button><p style="margin-top:14px"><a href="/forgot-password">Forgot password?</a></p></form></body></html>"""


@app.route("/staff-login")
def staff_login():
    return Response(STAFF_LOGIN_HTML.replace("__TOKEN__", get_csrf_token()), mimetype="text/html")


@app.route("/mode", methods=["POST"])
def set_mode():
    user = current_user()
    if user:
        conn = get_db()
        conn.execute("UPDATE users SET dark_mode=? WHERE id=?", (1 if request.form.get("dark") == "1" else 0, user["id"]))
        conn.commit()
        conn.close()
    return jsonify({"ok": True})


@app.route("/terms")
def terms():
    return render_template("terms.html", user=current_user(), active_page="terms", auto_open_auth=False)


@app.route("/privacy")
def privacy():
    return render_template("privacy.html", user=current_user(), active_page="privacy", auto_open_auth=False)


@app.route("/sw.js")
def service_worker():
    resp = Response(SERVICE_WORKER_JS, mimetype="application/javascript")
    resp.headers["Cache-Control"] = "no-cache"
    resp.headers["Service-Worker-Allowed"] = "/"
    return resp


@app.route("/push-icon.png")
def push_icon():
    resp = Response(PUSH_ICON_PNG, mimetype="image/png")
    resp.headers["Cache-Control"] = "public, max-age=86400"
    return resp


@app.route("/push/key")
def push_key():
    pub, priv = get_vapid_keys()
    return jsonify({"enabled": bool(pub and priv), "key": pub})


@app.route("/push/subscribe", methods=["POST"])
def push_subscribe():
    user = current_user()
    if not user:
        return jsonify({"error": "auth"}), 401
    try:
        sub = _json.loads(request.form.get("subscription", ""))
        endpoint = sub["endpoint"]
        p256dh = sub["keys"]["p256dh"]
        auth = sub["keys"]["auth"]
    except Exception:
        return jsonify({"error": "bad subscription"}), 400
    if not str(endpoint).startswith("https://"):
        return jsonify({"error": "bad endpoint"}), 400
    conn = get_db()
    conn.execute("DELETE FROM push_subscriptions WHERE endpoint=?", (endpoint,))
    conn.execute("INSERT INTO push_subscriptions (user_id, endpoint, p256dh, auth) VALUES (?, ?, ?, ?)",
                 (user["id"], endpoint, p256dh, auth))
    conn.commit()
    conn.close()
    return jsonify({"ok": True})


@app.route("/push/unsubscribe", methods=["POST"])
def push_unsubscribe():
    endpoint = request.form.get("endpoint", "")
    if endpoint:
        conn = get_db()
        conn.execute("DELETE FROM push_subscriptions WHERE endpoint=?", (endpoint,))
        conn.commit()
        conn.close()
    return jsonify({"ok": True})


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
    {"id": "a4", "label": "A4 paper, 29.7 x 21 cm (most accurate)", "mode": "rect", "w": 29.7, "h": 21.0},
    {"id": "card", "label": "Bank / ID card, 8.56 x 5.4 cm (close-ups only)", "mode": "rect", "w": 8.56, "h": 5.398},
    {"id": "custom_rect", "label": "Another rectangle (enter its size)", "mode": "rect", "w": None, "h": None},
    {"id": "tape", "label": "Known length, two points (less accurate)", "mode": "line", "w": None, "h": None},
]

PAYSTACK_SECRET_KEY = os.environ.get("PAYSTACK_SECRET_KEY", "")


def paystack_configured():
    return PAYSTACK_SECRET_KEY.startswith("sk_")
PAYSTACK_PUBLIC_KEY = "pk_test_REPLACE_WITH_YOUR_OWN_TEST_KEY"
CONNECT_COINS_PER_NAIRA = 1
PRO_MEMBERSHIP_COST = 200  # CONNECT coins for a Pro upgrade

PHONE_PATTERN = re.compile(r"\d[\d\s\-]{5,}\d")

JOB_CATEGORIES = ["Windows", "Doors", "Partitions", "Curtain Walls", "Maintenance", "Aluminum Fabrication", "Repair", "Other"]
PRODUCT_CATEGORIES = ["Windows", "Doors", "Partitions", "Curtain Walls", "Maintenance", "Custom Solutions"]
# Shown as quick replies in the "Request a Service" chat ("Repair" still works for old requests)
REQUEST_CHIPS = [("Windows", "Windows"), ("Doors", "Doors"), ("Partitions", "Partitioning"), ("Curtain Walls", "Curtain walls"),
                 ("Maintenance", "Repairs & maintenance"), ("Aluminum Fabrication", "Custom aluminum work"), ("Other", "Something else")]
# The "Explore Services" page: one section per service. Photos come from the catalogue (products table).
SERVICES = [
    {"slug": "windows", "name": "Windows", "cat": "Windows", "art": 0, "blurb": "Sliding and fixed aluminum windows, made to size.",
     "good_for": "Homes, shops and offices.",
     "consider": "The room and how the window should open, ventilation, security, weather exposure, and an accurate opening size."},
    {"slug": "doors", "name": "Doors", "cat": "Doors", "art": 1, "blurb": "Strong, smooth-running aluminum and glass doors.",
     "good_for": "Entrances and other openings in homes and commercial buildings.",
     "consider": "Where the door will be used, how it should open, glass choice, security, and the size and condition of the opening."},
    {"slug": "partitioning", "name": "Partitioning", "cat": "Partitions", "art": 2, "blurb": "Glass and aluminum partitions for offices and homes.",
     "good_for": "Dividing offices, shops and rooms at home.",
     "consider": "The layout, how much light and privacy you want, whether you need a door, and the condition of the floor and ceiling."},
    {"slug": "curtain-walls", "name": "Curtain Walls", "cat": "Curtain Walls", "art": 3, "blurb": "Sleek glass facades for modern buildings.",
     "good_for": "Glazed building fronts and facades.",
     "consider": "These depend on the building's structure and its exposure to wind and weather, so they need professional assessment and installation."},
    {"slug": "maintenance", "name": "Maintenance", "cat": "Maintenance", "art": 4, "blurb": "Repairs, servicing and quick fixes.",
     "good_for": "Existing aluminium windows, doors and fittings that need attention.",
     "consider": "Describe the problem and add photos. Please don't remove heavy glass or work at height yourself."},
    {"slug": "custom", "name": "Custom Solutions", "cat": "Custom Solutions", "art": None, "blurb": "Gates, rails and other made-to-order aluminum work.",
     "good_for": "Gates, rails and other made-to-order aluminium work.",
     "consider": "Tell us what it is for and where it will go. A photo or sketch helps, and the design may need on-site measurement."},
]
JOB_STATUSES = ["submitted", "assigned", "in_progress", "completed", "cancelled"]
# Guided consultation (Explore Services > "Start your consultation"). Everything the customer reads comes from this
# structure: edit the wording here. Rules show their text when every key in "when" matches the customer's answers
# ("*" = any answer given, "__none" = question skipped). Nothing here is a price, specification or promise.
_NOT_SURE = {"v": "unsure", "label": "Not sure yet"}
_FLOOR = [{"v": "ground", "label": "Ground floor"}, {"v": "upper", "label": "Upper floor"}, {"v": "unsure", "label": "Not sure"}]
_JOB = [{"v": "new", "label": "New (nothing there now)"}, {"v": "replace", "label": "Replacing an existing one"}, {"v": "repair", "label": "Repairing an existing one"}]
_SIZE_HINT = "Only measure what you can reach safely from the floor. A rough estimate is fine, for example 120 cm wide by 100 cm high."
_COST_TXT = "Cost mostly depends on the size, the number of panels or openings, the glass, the hardware, and how difficult the installation is."
_PRO_NEXT = "Request professional assistance so the opening can be measured and checked on site before you decide."

CONSULT_GUIDE = {
    "cost": "A price can't be given here because it depends on the details of your project. The main factors are the size, the number of panels or openings, the glass and hardware, how complicated the installation is, and the condition of and access to the site. You can request professional assistance to ask about pricing once these details are known.",
    "danger": "If anyone could be hurt right now, keep people and pets away from the area and don't try to fix it yourself. Get a qualified professional, and if someone is at immediate risk, contact your local emergency services.",
    "cats": [
        {"id": "windows", "label": "Windows", "icon": "🪟", "job_cat": "Windows", "topic": "Window selection",
         "intro": "Let's work out what suits your window. A few short questions, then your options and what still needs checking."},
        {"id": "doors", "label": "Doors", "icon": "🚪", "job_cat": "Doors", "topic": "Door selection",
         "intro": "Let's work out what suits your door. A few short questions, then your options and what still needs checking."},
        {"id": "partitions", "label": "Aluminum partitions", "icon": "🏢", "job_cat": "Partitions", "topic": "Partition planning",
         "intro": "Let's think through your partition. A few short questions, then your options and what still needs checking."},
        {"id": "measure", "label": "Measurements & project planning", "icon": "📏", "job_cat": "Other", "topic": "Measurements and project planning",
         "intro": "Let's see what to prepare before a professional assessment. Nothing you enter here counts as a verified measurement."},
        {"id": "care", "label": "Installation, maintenance & precautions", "icon": "🛠️", "job_cat": "Maintenance", "topic": "Installation, maintenance or precautions",
         "intro": "Let's look at what you can safely do yourself and when a professional is needed."},
        {"id": "general", "label": "Another aluminum project", "icon": "💬", "job_cat": "Aluminum Fabrication", "topic": "General aluminum project",
         "intro": "Tell us about your project and we'll point you to the right next step."},
    ],
    "questions": {
        "windows": [
            {"id": "w_room", "kind": "choice", "text": "Where will the window go?", "short": "Room or building", "group": "detail",
             "options": [{"v": "living", "label": "Living room or bedroom"}, {"v": "wet", "label": "Kitchen or bathroom"}, {"v": "work", "label": "Office or shop"}, {"v": "other", "label": "Somewhere else"}]},
            {"id": "w_job", "kind": "choice", "text": "Is this a new window, a replacement, or a repair?", "short": "Type of job", "group": "req", "options": _JOB},
            {"id": "w_prio", "kind": "choice", "text": "What matters most to you?", "short": "Main priority", "group": "req",
             "options": [{"v": "vent", "label": "Fresh air"}, {"v": "light", "label": "Light and view"}, {"v": "sec", "label": "Security"}, {"v": "priv", "label": "Privacy"},
                         {"v": "weather", "label": "Keeping out rain and wind"}, {"v": "maint", "label": "Low maintenance"}, {"v": "cost", "label": "Keeping cost down"}]},
            {"id": "w_floor", "kind": "choice", "text": "Which floor is the window on?", "short": "Floor", "group": "detail", "options": _FLOOR},
            {"id": "w_size", "kind": "text", "optional": True, "text": "Do you know the approximate size?", "hint": _SIZE_HINT, "short": "Approximate size (estimate, not verified)", "group": "detail", "dims": True},
        ],
        "doors": [
            {"id": "d_where", "kind": "choice", "text": "Where will the door be used?", "short": "Where the door is", "group": "detail",
             "options": [{"v": "main", "label": "Main entrance"}, {"v": "back", "label": "Back, patio or balcony"}, {"v": "inner", "label": "Inside a home or office"}, {"v": "shop", "label": "Shop or commercial entrance"}]},
            {"id": "d_job", "kind": "choice", "text": "Is this a new door, a replacement, or a repair?", "short": "Type of job", "group": "req", "options": _JOB},
            {"id": "d_prio", "kind": "choice", "text": "What matters most to you?", "short": "Main priority", "group": "req",
             "options": [{"v": "sec", "label": "Security"}, {"v": "dur", "label": "Heavy daily use"}, {"v": "space", "label": "Saving space"}, {"v": "look", "label": "Appearance"},
                         {"v": "maint", "label": "Low maintenance"}, {"v": "cost", "label": "Keeping cost down"}]},
            {"id": "d_open", "kind": "choice", "text": "How would you like the door to open?", "short": "Opening style", "group": "req",
             "options": [{"v": "swing", "label": "Swinging on hinges"}, {"v": "slide", "label": "Sliding sideways"}, _NOT_SURE]},
            {"id": "d_size", "kind": "text", "optional": True, "text": "Do you know the approximate size of the opening?", "hint": _SIZE_HINT, "short": "Approximate size (estimate, not verified)", "group": "detail", "dims": True},
        ],
        "partitions": [
            {"id": "p_where", "kind": "choice", "text": "What kind of space is it?", "short": "Type of space", "group": "detail",
             "options": [{"v": "home", "label": "Home"}, {"v": "office", "label": "Office"}, {"v": "shop", "label": "Shop or commercial space"}, {"v": "other", "label": "Something else"}]},
            {"id": "p_goal", "kind": "choice", "text": "What do you mainly want the partition to do?", "short": "Main goal", "group": "req",
             "options": [{"v": "priv", "label": "More privacy"}, {"v": "light", "label": "Keep the space bright"}, {"v": "split", "label": "Divide a large space"}, {"v": "noise", "label": "Reduce noise"}, {"v": "cost", "label": "Keep cost down"}]},
            {"id": "p_door", "kind": "choice", "text": "Will you need a door in the partition?", "short": "Door needed", "group": "req",
             "options": [{"v": "yes", "label": "Yes"}, {"v": "no", "label": "No"}, _NOT_SURE]},
            {"id": "p_size", "kind": "text", "optional": True, "text": "Roughly how long and how high is the area to divide?", "hint": _SIZE_HINT, "short": "Approximate size (estimate, not verified)", "group": "detail", "dims": True},
        ],
        "measure": [
            {"id": "m_for", "kind": "choice", "text": "What are you measuring for?", "short": "Item", "group": "req",
             "options": [{"v": "window", "label": "A window"}, {"v": "door", "label": "A door"}, {"v": "part", "label": "A partition"}, {"v": "other", "label": "Something else"}]},
            {"id": "m_have", "kind": "choice", "text": "Do you already have measurements?", "short": "Measurements", "group": "detail",
             "options": [{"v": "exact", "label": "Yes, measured carefully"}, {"v": "rough", "label": "Only a rough estimate"}, {"v": "none", "label": "No measurements yet"}]},
            {"id": "m_floor", "kind": "choice", "text": "Is the opening on the ground floor or higher up?", "short": "Floor", "group": "detail", "options": _FLOOR},
            {"id": "m_size", "kind": "text", "optional": True, "text": "Enter any sizes you have, and say if they are rough.", "hint": "For example: about 120 cm wide by 100 cm high, rough.", "short": "Sizes given (estimate, not verified)", "group": "detail", "dims": True},
        ],
        "care": [
            {"id": "c_what", "kind": "choice", "text": "What do you need help with?", "short": "Situation", "group": "req",
             "options": [{"v": "clean", "label": "Routine cleaning and upkeep"}, {"v": "stuck", "label": "Something is stuck or hard to move"}, {"v": "loose", "label": "Something is loose, rattling or leaking"},
                         {"v": "glass", "label": "Cracked or broken glass", "danger": True}, {"v": "diy", "label": "I'm thinking of fitting or repairing it myself"}, {"v": "unsure", "label": "Not sure"}]},
            {"id": "c_item", "kind": "choice", "text": "Which item is it?", "short": "Item", "group": "detail",
             "options": [{"v": "window", "label": "A window"}, {"v": "door", "label": "A door"}, {"v": "part", "label": "A partition"}, {"v": "other", "label": "Something else"}]},
            {"id": "c_floor", "kind": "choice", "text": "Is it on the ground floor or higher up?", "short": "Floor", "group": "detail", "options": _FLOOR},
            {"id": "c_risk", "kind": "choice", "text": "Is anything at risk of falling, or could anyone be hurt right now?", "short": "Immediate risk", "group": "req",
             "ask_if": {"c_what": ["stuck", "loose", "glass", "diy", "unsure"]},
             "options": [{"v": "yes", "label": "Yes", "danger": True}, {"v": "no", "label": "No"}, {"v": "unsure", "label": "Not sure", "danger": True}]},
        ],
        "general": [
            {"id": "g_what", "kind": "choice", "text": "What kind of project is it?", "short": "Project type", "group": "req",
             "options": [{"v": "gate", "label": "Gate, railing or similar"}, {"v": "facade", "label": "Large glass front or facade"}, {"v": "repair", "label": "Repair or change to something existing"}, {"v": "other", "label": "Something else"}]},
            {"id": "g_desc", "kind": "text", "text": "Describe what you want to build, fix or change, and where it will go.", "short": "Description", "group": "req"},
            {"id": "g_size", "kind": "text", "optional": True, "text": "Do you know the approximate size?", "hint": _SIZE_HINT, "short": "Approximate size (estimate, not verified)", "group": "detail", "dims": True},
        ],
        "common": [
            {"id": "loc", "kind": "text", "optional": True, "text": "Where is the project? An area or town is enough.", "short": "Project area", "group": "detail", "loc": True},
            {"id": "photos", "kind": "photos"},
        ],
    },
    "rules": {
        "all": [
            {"kind": "safety", "when": {"__danger": ["1"]}, "text": "You described a possible immediate hazard. Keep people away from it and get professional help rather than trying to fix it yourself."},
            {"kind": "verify", "when": {"loc": ["__none"]}, "text": "Project location has not been provided yet."},
            {"kind": "next", "when": {"__danger": ["1"]}, "text": "Get a qualified professional to look at this as soon as possible and explain the risk when you request assistance. If anyone is at immediate risk, contact your local emergency services."},
        ],
        "windows": [
            {"kind": "option", "when": {}, "text": "A sliding window saves space because nothing swings into the room, but it opens only part of its frame at a time. A fixed window has no moving parts and lets in light, but it does not open."},
            {"kind": "option", "when": {"w_prio": ["vent"]}, "text": "If fresh air matters most, a sliding window gives less airflow than a fully opening one. Ask which opening styles are available for your opening."},
            {"kind": "option", "when": {"w_prio": ["light"]}, "text": "A fixed panel gives the most uninterrupted light and view but no ventilation. Combining a fixed panel with an opening one is a common approach."},
            {"kind": "option", "when": {"w_prio": ["sec"]}, "text": "Security depends on the locks, the glass and how the frame is fixed into the wall, not only on the window style. Ask what locking and glass options are available, and have the fixing checked on site."},
            {"kind": "option", "when": {"w_prio": ["priv"]}, "text": "Privacy usually comes from the type of glass, for example frosted or tinted. Ask what glass options are available."},
            {"kind": "option", "when": {"w_prio": ["weather"]}, "text": "Resistance to rain and wind depends on sealing and correct installation as well as the window itself. Exposed or upper-floor openings need extra care."},
            {"kind": "option", "when": {"w_prio": ["maint"]}, "text": "Keep sliding tracks clean and check seals and locks from time to time. Ask how to look after the frames in your location."},
            {"kind": "option", "when": {"w_prio": ["cost"]}, "text": _COST_TXT},
            {"kind": "option", "when": {"w_room": ["wet"]}, "text": "Kitchens and bathrooms usually need both ventilation and privacy, so think about both."},
            {"kind": "option", "when": {"w_room": ["work"]}, "text": "Offices and shops often need security and easy cleaning as well as light. Mention how the space is used."},
            {"kind": "safety", "when": {}, "text": "Glass and aluminum edges can cause serious cuts and window frames can be heavy. Leave removal, fitting and glass handling to professionals."},
            {"kind": "safety", "when": {"w_floor": ["upper"]}, "text": "Upper-floor openings carry a risk of falling. Don't lean out, climb or stand on unstable supports to measure or work. Measuring and fitting here should be done by a professional."},
            {"kind": "safety", "when": {"w_job": ["replace", "repair"]}, "text": "Don't remove an existing window or its glass yourself. It can be heavy, brittle and hard to hold safely."},
            {"kind": "verify", "when": {"w_size": ["__none"]}, "text": "Approximate size has not been provided yet."},
            {"kind": "verify", "when": {"w_size": ["*"]}, "text": "The size you gave is an estimate. Exact measurements must be confirmed on site before anything is made."},
            {"kind": "verify", "when": {}, "text": "The condition of the wall and frame around the opening."},
            {"kind": "verify", "when": {"w_floor": ["unsure"]}, "text": "Which floor the opening is on."},
            {"kind": "next", "when": {"w_floor": ["upper"]}, "text": "An on-site assessment is strongly recommended. Request professional assistance so the opening can be measured and checked safely."},
            {"kind": "next", "when": {"w_job": ["replace", "repair"]}, "text": "Request professional assistance so the existing window can be inspected before deciding between repair and replacement."},
            {"kind": "next", "when": {}, "text": _PRO_NEXT},
        ],
        "doors": [
            {"kind": "option", "when": {}, "text": "A hinged door needs clear floor space to swing. A sliding door avoids that, but relies on a track that needs cleaning and good locking."},
            {"kind": "option", "when": {"d_prio": ["sec"]}, "text": "Door security comes from the lock, the frame fixing and the glass together. Ask what locking and glass options are available, and have the fixing checked on site."},
            {"kind": "option", "when": {"d_prio": ["dur"]}, "text": "Doors in heavy daily use need sturdy hardware and solid fixing. Tell us roughly how many people use the door."},
            {"kind": "option", "when": {"d_prio": ["space"]}, "text": "If space is tight, a sliding door avoids the swing area, but check there is room for it to slide."},
            {"kind": "option", "when": {"d_prio": ["look"]}, "text": "Frame finish and glass choice affect the look. Ask what finishes and glass options are available."},
            {"kind": "option", "when": {"d_prio": ["maint"]}, "text": "Keep tracks and hinges clean and check locks and seals from time to time."},
            {"kind": "option", "when": {"d_prio": ["cost"]}, "text": _COST_TXT},
            {"kind": "option", "when": {"d_where": ["main"]}, "text": "Main entrances usually need strong locking and good weather sealing."},
            {"kind": "option", "when": {"d_where": ["shop"]}, "text": "Shop and commercial doors take heavy use and need reliable, secure locking. Mention how many people use the entrance."},
            {"kind": "safety", "when": {}, "text": "Glass and aluminum doors are heavy and can be dangerous to lift, remove or hang. Don't try to fit or remove one yourself."},
            {"kind": "safety", "when": {"d_job": ["replace", "repair"]}, "text": "Don't take a door off its frame or track yourself. Doors can fall and glass can break."},
            {"kind": "verify", "when": {"d_size": ["__none"]}, "text": "Approximate size has not been provided yet."},
            {"kind": "verify", "when": {"d_size": ["*"]}, "text": "The size you gave is an estimate. Exact measurements must be confirmed on site before anything is made."},
            {"kind": "verify", "when": {}, "text": "Whether the floor and threshold are level, and how much clear space there is around the opening."},
            {"kind": "verify", "when": {"d_open": ["unsure"]}, "text": "How the door should open (swinging or sliding)."},
            {"kind": "next", "when": {"d_job": ["replace", "repair"]}, "text": "Request professional assistance so the existing door can be inspected before deciding between repair and replacement."},
            {"kind": "next", "when": {}, "text": _PRO_NEXT},
        ],
        "partitions": [
            {"kind": "option", "when": {}, "text": "Glass and aluminum partitions divide a space while letting light through. The layout, how the space is used and the privacy you need decide the details."},
            {"kind": "option", "when": {"p_goal": ["priv"]}, "text": "Privacy usually comes from the type of glass, for example frosted or tinted. Ask what glass options are available."},
            {"kind": "option", "when": {"p_goal": ["light"]}, "text": "Clear glass keeps a space bright and open but gives less privacy, so decide which matters more."},
            {"kind": "option", "when": {"p_goal": ["split"]}, "text": "Plan around how people will move through the space, including any exits and clear walkways."},
            {"kind": "option", "when": {"p_goal": ["noise"]}, "text": "Partitions are not automatically soundproof. How much noise they reduce depends on the materials and how they are built, so ask what is possible before relying on it."},
            {"kind": "option", "when": {"p_goal": ["cost"]}, "text": _COST_TXT},
            {"kind": "option", "when": {"p_door": ["yes"]}, "text": "A door adds a moving part, so plan where it swings or slides and make sure it can open freely."},
            {"kind": "safety", "when": {}, "text": "Partitions are tall and heavy and depend on sound floors, walls or ceilings for fixing. Installation should be done by professionals."},
            {"kind": "safety", "when": {"p_where": ["office", "shop"]}, "text": "In offices and shops, check building, landlord or safety rules (for example exit routes) before dividing a space."},
            {"kind": "verify", "when": {"p_size": ["__none"]}, "text": "Approximate size has not been provided yet."},
            {"kind": "verify", "when": {"p_size": ["*"]}, "text": "The size you gave is an estimate. Exact measurements must be confirmed on site before anything is made."},
            {"kind": "verify", "when": {}, "text": "The condition and levelness of the floor, walls and ceiling the partition will fix to."},
            {"kind": "verify", "when": {}, "text": "Whether any building, landlord or safety rules apply."},
            {"kind": "next", "when": {}, "text": "Request professional assistance so the space can be measured and assessed on site before you decide."},
        ],
        "measure": [
            {"kind": "option", "when": {}, "text": "Helpful to prepare: photos of the opening from inside and outside, a rough width and height, what the space is used for, and anything in the way such as furniture, pipes or steps."},
            {"kind": "option", "when": {"m_have": ["exact"]}, "text": "Even careful customer measurements can't replace a professional measurement. Keep yours to compare."},
            {"kind": "option", "when": {"m_have": ["rough"]}, "text": "Rough sizes are fine for a first discussion but must not be used to order or make anything."},
            {"kind": "option", "when": {"m_have": ["none"]}, "text": "You don't need exact numbers to start. Photos and a description of the space are enough for a first conversation."},
            {"kind": "safety", "when": {}, "text": "Only measure from the floor, on stable footing. Never climb, lean out of a window or work at height to take a measurement."},
            {"kind": "safety", "when": {"m_floor": ["upper"]}, "text": "For upper-floor openings, don't try to measure from outside. Leave it to a professional."},
            {"kind": "verify", "when": {}, "text": "All sizes must be confirmed by a professional measurement on site. Anything you give is an estimate, not a verified site measurement."},
            {"kind": "verify", "when": {"m_floor": ["unsure"]}, "text": "Which floor the opening is on."},
            {"kind": "next", "when": {}, "text": "Request professional assistance to arrange a proper on-site measurement and assessment."},
        ],
        "care": [
            {"kind": "option", "when": {"c_what": ["clean"]}, "text": "Wipe frames and glass with a soft cloth and mild soapy water. Clear dust and grit from sliding tracks, and check that locks, seals and handles still work. Avoid harsh abrasives that can scratch."},
            {"kind": "option", "when": {"c_what": ["stuck"]}, "text": "Dirt or grit in a track is a common reason for a sliding window or door sticking. Clean the track gently, but don't force it or lift it off its track."},
            {"kind": "option", "when": {"c_what": ["loose"]}, "text": "Loose, rattling or leaking items can come from worn seals or fittings, or a frame that has shifted. A professional should look at them, especially if the frame may have moved."},
            {"kind": "option", "when": {"c_what": ["glass"]}, "text": "Cracked glass can fail suddenly. Keep people and pets away, don't touch or press on it, and don't try to remove it yourself."},
            {"kind": "option", "when": {"c_what": ["diy"]}, "text": "Fitting or repairing windows and doors involves heavy glass, sharp edges and often heights. We recommend leaving fitting and repairs to professionals."},
            {"kind": "option", "when": {"c_what": ["unsure"]}, "text": "If you are not sure what is wrong, don't take anything apart. Photos and a description are the safest way to start."},
            {"kind": "safety", "when": {}, "text": "Don't use force or makeshift tools on frames, glass or fittings."},
            {"kind": "safety", "when": {"c_what": ["diy"]}, "text": "Do not attempt installation or structural repairs unless you are qualified. Heavy glass, sharp edges, unstable frames and heights can cause serious injury."},
            {"kind": "safety", "when": {"c_floor": ["upper"]}, "text": "Don't lean out of upper-floor windows or climb to clean, check or repair them."},
            {"kind": "verify", "when": {"c_what": ["unsure"]}, "text": "What exactly is wrong with the item."},
            {"kind": "verify", "when": {"c_what": ["loose", "glass", "stuck"]}, "text": "Whether the frame or the wall around it is damaged."},
            {"kind": "next", "when": {"c_what": ["glass"]}, "text": "Keep people away and get a qualified professional to look at it as soon as possible. Request professional assistance and explain the risk."},
            {"kind": "next", "when": {"c_risk": ["yes", "unsure"]}, "text": "Keep people away from the area and get a qualified professional to look at it as soon as possible. Request professional assistance and explain the risk."},
            {"kind": "next", "when": {"c_what": ["clean"]}, "text": "Routine upkeep like this is usually fine to do yourself. If you notice damage, request professional assistance."},
            {"kind": "next", "when": {}, "text": "Request professional assistance so the problem can be inspected before anything is repaired."},
        ],
        "general": [
            {"kind": "option", "when": {}, "text": "Custom aluminum projects depend on the exact space, the purpose and how it will be used. Photos and a clear description help us understand it."},
            {"kind": "option", "when": {"g_what": ["gate"]}, "text": "Gates and railings must be strong and fixed properly. Safety around heights and children matters."},
            {"kind": "option", "when": {"g_what": ["facade"]}, "text": "Large glass fronts depend on the building's structure and its exposure to wind and weather, so they need professional assessment."},
            {"kind": "safety", "when": {}, "text": "Large or heavy aluminum and glass work, and anything at height, should be assessed and installed by professionals."},
            {"kind": "verify", "when": {"g_size": ["__none"]}, "text": "Approximate size has not been provided yet."},
            {"kind": "verify", "when": {"g_size": ["*"]}, "text": "The size you gave is an estimate. Exact measurements must be confirmed on site before anything is made."},
            {"kind": "verify", "when": {}, "text": "Whether the work depends on the strength or condition of the existing structure."},
            {"kind": "next", "when": {}, "text": "Request professional assistance so the project can be discussed and assessed on site if needed."},
        ],
    },
}

# ---------------------------------------------------------------------------
# DATABASE
# ---------------------------------------------------------------------------

class _PGCursorWrapper:
    def __init__(self, cursor):
        self._cursor = cursor
        self.lastrowid = None
        self.rowcount = getattr(cursor, "rowcount", -1)

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

    def rollback(self):
        self._conn.rollback()

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
    _add_column_if_missing(conn, "messages", "read_by_artisan", "INTEGER DEFAULT 1")
    _add_column_if_missing(conn, "work_posts", "status", "TEXT DEFAULT 'approved'")
    _add_column_if_missing(conn, "work_posts", "submitted_by", "INTEGER")
    _add_column_if_missing(conn, "work_posts", "category", "TEXT DEFAULT ''")
    _add_column_if_missing(conn, "work_posts", "reject_reason", "TEXT DEFAULT ''")
    _add_column_if_missing(conn, "users", "has_seen_guide", "INTEGER DEFAULT 0")
    _add_column_if_missing(conn, "users", "reset_token", "TEXT DEFAULT ''")
    _add_column_if_missing(conn, "users", "reset_token_expires", "TEXT DEFAULT ''")
    _add_column_if_missing(conn, "users", "avatar_filename", "TEXT DEFAULT ''")
    _add_column_if_missing(conn, "users", "bio", "TEXT DEFAULT ''")
    conn.execute(f"""
        CREATE TABLE IF NOT EXISTS push_subscriptions (
            id {id_column},
            user_id INTEGER NOT NULL,
            endpoint TEXT NOT NULL,
            p256dh TEXT NOT NULL,
            auth TEXT NOT NULL,
            created_at TEXT DEFAULT CURRENT_TIMESTAMP
        )
    """)
    conn.execute("CREATE TABLE IF NOT EXISTS app_kv (k TEXT PRIMARY KEY, v TEXT)")
    conn.execute("CREATE TABLE IF NOT EXISTS paystack_refs (reference TEXT PRIMARY KEY, user_id INTEGER, created_at TEXT DEFAULT CURRENT_TIMESTAMP)")
    _add_column_if_missing(conn, "jobs", "escrow_held", "INTEGER DEFAULT 0")
    if not conn.execute("SELECT 1 FROM app_kv WHERE k='escrow_backfill'").fetchone():
        # one-time: jobs already in progress were paid through the escrow flow
        conn.execute("UPDATE jobs SET escrow_held = 1 WHERE status = 'in_progress'")
        conn.execute("INSERT INTO app_kv (k, v) VALUES ('escrow_backfill', '1')")
    _add_column_if_missing(conn, "work_photos", "kind", "TEXT DEFAULT 'image'")
    conn.execute("CREATE TABLE IF NOT EXISTS work_likes (work_id INTEGER NOT NULL, user_id INTEGER NOT NULL, PRIMARY KEY (work_id, user_id))")
    conn.execute("CREATE TABLE IF NOT EXISTS review_likes (review_id INTEGER NOT NULL, user_id INTEGER NOT NULL, PRIMARY KEY (review_id, user_id))")
    conn.execute(f"""
        CREATE TABLE IF NOT EXISTS work_reviews (
            id {id_column},
            work_id INTEGER NOT NULL,
            user_id INTEGER NOT NULL,
            rating INTEGER NOT NULL,
            text TEXT DEFAULT '',
            created_at TEXT DEFAULT CURRENT_TIMESTAMP
        )
    """)
    conn.commit()
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

    # Owner credentials come from environment variables so the real production
    # password is never baked into the source code. ADMIN_EMAIL/ADMIN_PASSWORD
    # must be set before going live; the fallback values below are for local
    # testing only and print a loud warning so they're never mistaken for safe
    # production defaults.
    owner_email = os.environ.get("ADMIN_EMAIL", "danny@andy.local")
    owner_password = os.environ.get("ADMIN_PASSWORD")
    using_fallback_password = owner_password is None
    if using_fallback_password:
        owner_password = pysecrets.token_urlsafe(10)   # random, shown once in the server log

    existing_owner_row = conn.execute("SELECT * FROM users WHERE email = ?", (owner_email,)).fetchone()
    if existing_owner_row is None:
        conn.execute(
            "INSERT INTO users (name, email, password_hash, role, wallet, referral_code) "
            "VALUES ('Danny', ?, ?, 'owner', 0, 'ANDY-ADMIN')",
            (owner_email, generate_password_hash(owner_password)),
        )
        conn.commit()
        if using_fallback_password:
            print(f"[ANDY] WARNING: no ADMIN_PASSWORD environment variable set. Seeded the owner "
                  f"login with a RANDOM one-time password -> email: {owner_email}  password: {owner_password}")
            print("[ANDY] Log in, then change it in Settings. Set ADMIN_EMAIL and ADMIN_PASSWORD "
                  "as environment variables for a stable production setup.")
        else:
            print(f"[ANDY] Seeded admin/owner login -> email: {owner_email}")
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



WORKER_SVGS = {'1': '<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 400 300"><defs><linearGradient id="a1-bg" x1="0" y1="0" x2="0" y2="1"><stop offset="0" stop-color="#17294B"/><stop offset="1" stop-color="#0B1630"/></linearGradient><linearGradient id="a1-glass" x1="0" y1="0" x2="1" y2="1"><stop offset="0" stop-color="#A8EAFF"/><stop offset=".55" stop-color="#43A6DD"/><stop offset="1" stop-color="#1A5E96"/></linearGradient><linearGradient id="a1-alu" x1="0" y1="0" x2="0" y2="1"><stop offset="0" stop-color="#F4F7FB"/><stop offset=".5" stop-color="#BFCAD6"/><stop offset="1" stop-color="#8793A1"/></linearGradient></defs><rect width="400" height="300" fill="url(#a1-bg)"/><rect y="196" width="400" height="104" fill="#1B2438"/><rect y="194" width="400" height="4" fill="#2C3A58"/><line x1="30" y1="40" x2="30" y2="170" stroke="#7B8896" stroke-width="8" stroke-linecap="round"/><line x1="30" y1="38.4" x2="30" y2="168.4" stroke="#E6EDF4" stroke-width="3.6" stroke-linecap="round"/><line x1="52" y1="40" x2="52" y2="170" stroke="#7B8896" stroke-width="8" stroke-linecap="round"/><line x1="52" y1="38.4" x2="52" y2="168.4" stroke="#E6EDF4" stroke-width="3.6" stroke-linecap="round"/><line x1="74" y1="40" x2="74" y2="170" stroke="#7B8896" stroke-width="8" stroke-linecap="round"/><line x1="74" y1="38.4" x2="74" y2="168.4" stroke="#E6EDF4" stroke-width="3.6" stroke-linecap="round"/><line x1="96" y1="40" x2="96" y2="170" stroke="#7B8896" stroke-width="8" stroke-linecap="round"/><line x1="96" y1="38.4" x2="96" y2="168.4" stroke="#E6EDF4" stroke-width="3.6" stroke-linecap="round"/><line x1="118" y1="40" x2="118" y2="170" stroke="#7B8896" stroke-width="8" stroke-linecap="round"/><line x1="118" y1="38.4" x2="118" y2="168.4" stroke="#E6EDF4" stroke-width="3.6" stroke-linecap="round"/><line x1="140" y1="40" x2="140" y2="170" stroke="#7B8896" stroke-width="8" stroke-linecap="round"/><line x1="140" y1="38.4" x2="140" y2="168.4" stroke="#E6EDF4" stroke-width="3.6" stroke-linecap="round"/><rect x="18" y="100" width="150" height="5" fill="#3A4A6B"/><rect x="18" y="150" width="150" height="5" fill="#3A4A6B"/><rect x="250" y="40" width="110" height="82" rx="3" fill="none" stroke="url(#a1-alu)" stroke-width="9"/><rect x="259" y="49" width="92" height="64" fill="url(#a1-glass)" opacity=".7"/><line x1="305" y1="49" x2="305" y2="113" stroke="#C9D3DE" stroke-width="5"/><rect x="60" y="188" width="300" height="14" rx="3" fill="#8A6A4A"/><rect x="72" y="202" width="10" height="70" fill="#6B523A"/><rect x="338" y="202" width="10" height="70" fill="#6B523A"/><rect x="262" y="176" width="64" height="12" rx="2" fill="#35425F"/><circle cx="292" cy="170" r="17" fill="#C9D3DE" stroke="#7B8896" stroke-width="2"/><circle cx="292" cy="170" r="4" fill="#4A5568"/><rect x="288" y="140" width="8" height="26" fill="#EF4444"/><line x1="96" y1="181" x2="252" y2="181" stroke="#7B8896" stroke-width="8" stroke-linecap="round"/><line x1="96" y1="179.4" x2="252" y2="179.4" stroke="#E6EDF4" stroke-width="3.6" stroke-linecap="round"/><rect x="126" y="170" width="16" height="11" rx="2" fill="#F5C518"/><path d="M171.1,226.1 L166.6,263.9" stroke="#27324D" stroke-width="12.2" stroke-linecap="round"/><path d="M184.6,226.1 L186.8,263.9" stroke="#27324D" stroke-width="12.2" stroke-linecap="round"/><rect x="157.1" y="261.2" width="18.9" height="10.8" rx="4.1" fill="#3B2F2F"/><rect x="177.3" y="261.2" width="20.2" height="10.8" rx="4.1" fill="#3B2F2F"/><rect x="164.4" y="172.1" width="35.1" height="54.0" rx="9.5" fill="#1F2A44"/><path d="M165.8,177.5 L176.6,226.1 L165.8,226.1 Z M198.2,177.5 L187.4,226.1 L198.2,226.1 Z" fill="#22C55E"/><rect x="165.8" y="207.2" width="32.4" height="5.4" fill="#E8FFF1" opacity=".85"/><path d="M167.2,182.9 L177.8,158.1 L196.0,178.0" stroke="#1F2A44" stroke-width="9" stroke-linecap="round" stroke-linejoin="round" fill="none"/><circle cx="196.0" cy="178.0" r="5" fill="#D9A47A" stroke="#8B5A3A" stroke-width=".8"/><path d="M196.8,182.9 L172.9,195.3 L150.0,181.0" stroke="#1F2A44" stroke-width="9" stroke-linecap="round" stroke-linejoin="round" fill="none"/><circle cx="150.0" cy="181.0" r="5" fill="#D9A47A" stroke="#8B5A3A" stroke-width=".8"/><rect x="179.1" y="166.7" width="8.1" height="10.8" fill="#D9A47A"/><circle cx="183.2" cy="154.6" r="16.2" fill="#D9A47A" stroke="#8B5A3A" stroke-width=".8"/><rect x="171.0" y="151.9" width="24.3" height="8.1" rx="4.1" fill="#9FD8F2" stroke="#2A4A6A" stroke-width="1"/><path d="M164.3,149.2 A18.9,17.6 0 0 1 202.1,149.2 Z" fill="#F5C518" stroke="#B8920F" stroke-width="1"/><rect x="160.2" y="147.8" width="45.9" height="5.4" rx="2.7" fill="#F5C518" stroke="#B8920F" stroke-width="1"/><circle cx="270" cy="164" r="1.6" fill="#FFD166"/><circle cx="262" cy="158" r="1.6" fill="#FFD166"/><circle cx="276" cy="156" r="1.6" fill="#FFD166"/><rect y="272" width="400" height="28" fill="#111B30"/></svg>', '2': '<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 400 300"><defs><linearGradient id="a2-bg" x1="0" y1="0" x2="0" y2="1"><stop offset="0" stop-color="#17294B"/><stop offset="1" stop-color="#0B1630"/></linearGradient><linearGradient id="a2-glass" x1="0" y1="0" x2="1" y2="1"><stop offset="0" stop-color="#A8EAFF"/><stop offset=".55" stop-color="#43A6DD"/><stop offset="1" stop-color="#1A5E96"/></linearGradient><linearGradient id="a2-alu" x1="0" y1="0" x2="0" y2="1"><stop offset="0" stop-color="#F4F7FB"/><stop offset=".5" stop-color="#BFCAD6"/><stop offset="1" stop-color="#8793A1"/></linearGradient></defs><rect width="400" height="300" fill="url(#a2-bg)"/><rect x="70" y="30" width="260" height="240" fill="#C9C2B6"/><line x1="70" y1="30" x2="330" y2="30" stroke="#A9A194" stroke-width="1.4"/><line x1="70" y1="30" x2="70" y2="50" stroke="#A9A194" stroke-width="1.4"/><line x1="110" y1="30" x2="110" y2="50" stroke="#A9A194" stroke-width="1.4"/><line x1="150" y1="30" x2="150" y2="50" stroke="#A9A194" stroke-width="1.4"/><line x1="190" y1="30" x2="190" y2="50" stroke="#A9A194" stroke-width="1.4"/><line x1="230" y1="30" x2="230" y2="50" stroke="#A9A194" stroke-width="1.4"/><line x1="270" y1="30" x2="270" y2="50" stroke="#A9A194" stroke-width="1.4"/><line x1="310" y1="30" x2="310" y2="50" stroke="#A9A194" stroke-width="1.4"/><line x1="70" y1="50" x2="330" y2="50" stroke="#A9A194" stroke-width="1.4"/><line x1="90" y1="50" x2="90" y2="70" stroke="#A9A194" stroke-width="1.4"/><line x1="130" y1="50" x2="130" y2="70" stroke="#A9A194" stroke-width="1.4"/><line x1="170" y1="50" x2="170" y2="70" stroke="#A9A194" stroke-width="1.4"/><line x1="210" y1="50" x2="210" y2="70" stroke="#A9A194" stroke-width="1.4"/><line x1="250" y1="50" x2="250" y2="70" stroke="#A9A194" stroke-width="1.4"/><line x1="290" y1="50" x2="290" y2="70" stroke="#A9A194" stroke-width="1.4"/><line x1="70" y1="50" x2="70" y2="70" stroke="#A9A194" stroke-width="1.4"/><line x1="70" y1="70" x2="330" y2="70" stroke="#A9A194" stroke-width="1.4"/><line x1="70" y1="70" x2="70" y2="90" stroke="#A9A194" stroke-width="1.4"/><line x1="110" y1="70" x2="110" y2="90" stroke="#A9A194" stroke-width="1.4"/><line x1="150" y1="70" x2="150" y2="90" stroke="#A9A194" stroke-width="1.4"/><line x1="190" y1="70" x2="190" y2="90" stroke="#A9A194" stroke-width="1.4"/><line x1="230" y1="70" x2="230" y2="90" stroke="#A9A194" stroke-width="1.4"/><line x1="270" y1="70" x2="270" y2="90" stroke="#A9A194" stroke-width="1.4"/><line x1="310" y1="70" x2="310" y2="90" stroke="#A9A194" stroke-width="1.4"/><line x1="70" y1="90" x2="330" y2="90" stroke="#A9A194" stroke-width="1.4"/><line x1="90" y1="90" x2="90" y2="110" stroke="#A9A194" stroke-width="1.4"/><line x1="130" y1="90" x2="130" y2="110" stroke="#A9A194" stroke-width="1.4"/><line x1="170" y1="90" x2="170" y2="110" stroke="#A9A194" stroke-width="1.4"/><line x1="210" y1="90" x2="210" y2="110" stroke="#A9A194" stroke-width="1.4"/><line x1="250" y1="90" x2="250" y2="110" stroke="#A9A194" stroke-width="1.4"/><line x1="290" y1="90" x2="290" y2="110" stroke="#A9A194" stroke-width="1.4"/><line x1="70" y1="90" x2="70" y2="110" stroke="#A9A194" stroke-width="1.4"/><line x1="70" y1="110" x2="330" y2="110" stroke="#A9A194" stroke-width="1.4"/><line x1="70" y1="110" x2="70" y2="130" stroke="#A9A194" stroke-width="1.4"/><line x1="110" y1="110" x2="110" y2="130" stroke="#A9A194" stroke-width="1.4"/><line x1="150" y1="110" x2="150" y2="130" stroke="#A9A194" stroke-width="1.4"/><line x1="190" y1="110" x2="190" y2="130" stroke="#A9A194" stroke-width="1.4"/><line x1="230" y1="110" x2="230" y2="130" stroke="#A9A194" stroke-width="1.4"/><line x1="270" y1="110" x2="270" y2="130" stroke="#A9A194" stroke-width="1.4"/><line x1="310" y1="110" x2="310" y2="130" stroke="#A9A194" stroke-width="1.4"/><line x1="70" y1="130" x2="330" y2="130" stroke="#A9A194" stroke-width="1.4"/><line x1="90" y1="130" x2="90" y2="150" stroke="#A9A194" stroke-width="1.4"/><line x1="130" y1="130" x2="130" y2="150" stroke="#A9A194" stroke-width="1.4"/><line x1="170" y1="130" x2="170" y2="150" stroke="#A9A194" stroke-width="1.4"/><line x1="210" y1="130" x2="210" y2="150" stroke="#A9A194" stroke-width="1.4"/><line x1="250" y1="130" x2="250" y2="150" stroke="#A9A194" stroke-width="1.4"/><line x1="290" y1="130" x2="290" y2="150" stroke="#A9A194" stroke-width="1.4"/><line x1="70" y1="130" x2="70" y2="150" stroke="#A9A194" stroke-width="1.4"/><line x1="70" y1="150" x2="330" y2="150" stroke="#A9A194" stroke-width="1.4"/><line x1="70" y1="150" x2="70" y2="170" stroke="#A9A194" stroke-width="1.4"/><line x1="110" y1="150" x2="110" y2="170" stroke="#A9A194" stroke-width="1.4"/><line x1="150" y1="150" x2="150" y2="170" stroke="#A9A194" stroke-width="1.4"/><line x1="190" y1="150" x2="190" y2="170" stroke="#A9A194" stroke-width="1.4"/><line x1="230" y1="150" x2="230" y2="170" stroke="#A9A194" stroke-width="1.4"/><line x1="270" y1="150" x2="270" y2="170" stroke="#A9A194" stroke-width="1.4"/><line x1="310" y1="150" x2="310" y2="170" stroke="#A9A194" stroke-width="1.4"/><line x1="70" y1="170" x2="330" y2="170" stroke="#A9A194" stroke-width="1.4"/><line x1="90" y1="170" x2="90" y2="190" stroke="#A9A194" stroke-width="1.4"/><line x1="130" y1="170" x2="130" y2="190" stroke="#A9A194" stroke-width="1.4"/><line x1="170" y1="170" x2="170" y2="190" stroke="#A9A194" stroke-width="1.4"/><line x1="210" y1="170" x2="210" y2="190" stroke="#A9A194" stroke-width="1.4"/><line x1="250" y1="170" x2="250" y2="190" stroke="#A9A194" stroke-width="1.4"/><line x1="290" y1="170" x2="290" y2="190" stroke="#A9A194" stroke-width="1.4"/><line x1="70" y1="170" x2="70" y2="190" stroke="#A9A194" stroke-width="1.4"/><line x1="70" y1="190" x2="330" y2="190" stroke="#A9A194" stroke-width="1.4"/><line x1="70" y1="190" x2="70" y2="210" stroke="#A9A194" stroke-width="1.4"/><line x1="110" y1="190" x2="110" y2="210" stroke="#A9A194" stroke-width="1.4"/><line x1="150" y1="190" x2="150" y2="210" stroke="#A9A194" stroke-width="1.4"/><line x1="190" y1="190" x2="190" y2="210" stroke="#A9A194" stroke-width="1.4"/><line x1="230" y1="190" x2="230" y2="210" stroke="#A9A194" stroke-width="1.4"/><line x1="270" y1="190" x2="270" y2="210" stroke="#A9A194" stroke-width="1.4"/><line x1="310" y1="190" x2="310" y2="210" stroke="#A9A194" stroke-width="1.4"/><line x1="70" y1="210" x2="330" y2="210" stroke="#A9A194" stroke-width="1.4"/><line x1="90" y1="210" x2="90" y2="230" stroke="#A9A194" stroke-width="1.4"/><line x1="130" y1="210" x2="130" y2="230" stroke="#A9A194" stroke-width="1.4"/><line x1="170" y1="210" x2="170" y2="230" stroke="#A9A194" stroke-width="1.4"/><line x1="210" y1="210" x2="210" y2="230" stroke="#A9A194" stroke-width="1.4"/><line x1="250" y1="210" x2="250" y2="230" stroke="#A9A194" stroke-width="1.4"/><line x1="290" y1="210" x2="290" y2="230" stroke="#A9A194" stroke-width="1.4"/><line x1="70" y1="210" x2="70" y2="230" stroke="#A9A194" stroke-width="1.4"/><line x1="70" y1="230" x2="330" y2="230" stroke="#A9A194" stroke-width="1.4"/><line x1="70" y1="230" x2="70" y2="250" stroke="#A9A194" stroke-width="1.4"/><line x1="110" y1="230" x2="110" y2="250" stroke="#A9A194" stroke-width="1.4"/><line x1="150" y1="230" x2="150" y2="250" stroke="#A9A194" stroke-width="1.4"/><line x1="190" y1="230" x2="190" y2="250" stroke="#A9A194" stroke-width="1.4"/><line x1="230" y1="230" x2="230" y2="250" stroke="#A9A194" stroke-width="1.4"/><line x1="270" y1="230" x2="270" y2="250" stroke="#A9A194" stroke-width="1.4"/><line x1="310" y1="230" x2="310" y2="250" stroke="#A9A194" stroke-width="1.4"/><line x1="70" y1="250" x2="330" y2="250" stroke="#A9A194" stroke-width="1.4"/><line x1="90" y1="250" x2="90" y2="270" stroke="#A9A194" stroke-width="1.4"/><line x1="130" y1="250" x2="130" y2="270" stroke="#A9A194" stroke-width="1.4"/><line x1="170" y1="250" x2="170" y2="270" stroke="#A9A194" stroke-width="1.4"/><line x1="210" y1="250" x2="210" y2="270" stroke="#A9A194" stroke-width="1.4"/><line x1="250" y1="250" x2="250" y2="270" stroke="#A9A194" stroke-width="1.4"/><line x1="290" y1="250" x2="290" y2="270" stroke="#A9A194" stroke-width="1.4"/><line x1="70" y1="250" x2="70" y2="270" stroke="#A9A194" stroke-width="1.4"/><rect x="130" y="80" width="140" height="110" fill="#0B1630"/><rect x="136" y="86" width="128" height="98" rx="2" fill="url(#a2-glass)" stroke="url(#a2-alu)" stroke-width="9"/><line x1="200" y1="86" x2="200" y2="184" stroke="#DCE5EE" stroke-width="6"/><path d="M146 96 L172 96 L152 160 L146 160 Z" fill="#fff" opacity=".35"/><rect x="195" y="130" width="3" height="22" rx="1.5" fill="#44505F"/><rect x="150" y="70" width="100" height="9" rx="2" fill="#F5C518" stroke="#B8920F"/><rect x="192" y="72" width="16" height="5" rx="2" fill="#B9F6CA"/><circle cx="200" cy="74.5" r="2" fill="#16A34A"/><rect y="270" width="400" height="30" fill="#111B30"/><rect x="60" y="266" width="280" height="6" fill="#6B6559"/><path d="M92.2,226.1 L86.5,263.9" stroke="#27324D" stroke-width="12.2" stroke-linecap="round"/><path d="M105.8,226.1 L106.8,263.9" stroke="#27324D" stroke-width="12.2" stroke-linecap="round"/><rect x="77.1" y="261.2" width="18.9" height="10.8" rx="4.1" fill="#3B2F2F"/><rect x="97.3" y="261.2" width="20.2" height="10.8" rx="4.1" fill="#3B2F2F"/><rect x="88.5" y="172.1" width="35.1" height="54.0" rx="9.5" fill="#1F2A44"/><path d="M89.8,177.5 L100.6,226.1 L89.8,226.1 Z M122.2,177.5 L111.4,226.1 L122.2,226.1 Z" fill="#22C55E"/><rect x="89.8" y="207.2" width="32.4" height="5.4" fill="#E8FFF1" opacity=".85"/><path d="M91.2,182.9 L109.4,148.4 L136.0,120.0" stroke="#1F2A44" stroke-width="9" stroke-linecap="round" stroke-linejoin="round" fill="none"/><circle cx="136.0" cy="120.0" r="5" fill="#D9A47A" stroke="#8B5A3A" stroke-width=".8"/><path d="M120.8,182.9 L134.5,142.5 L138.0,100.0" stroke="#1F2A44" stroke-width="9" stroke-linecap="round" stroke-linejoin="round" fill="none"/><circle cx="138.0" cy="100.0" r="5" fill="#D9A47A" stroke="#8B5A3A" stroke-width=".8"/><rect x="104.0" y="166.7" width="8.1" height="10.8" fill="#D9A47A"/><circle cx="108.0" cy="154.6" r="16.2" fill="#D9A47A" stroke="#8B5A3A" stroke-width=".8"/><rect x="95.8" y="151.9" width="24.3" height="8.1" rx="4.1" fill="#9FD8F2" stroke="#2A4A6A" stroke-width="1"/><path d="M89.1,149.2 A18.9,17.6 0 0 1 126.9,149.2 Z" fill="#F5C518" stroke="#B8920F" stroke-width="1"/><rect x="85.0" y="147.8" width="45.9" height="5.4" rx="2.7" fill="#F5C518" stroke="#B8920F" stroke-width="1"/><path d="M294.2,226.1 L294.6,263.9" stroke="#27324D" stroke-width="12.2" stroke-linecap="round"/><path d="M307.8,226.1 L314.8,263.9" stroke="#27324D" stroke-width="12.2" stroke-linecap="round"/><rect x="285.1" y="261.2" width="18.9" height="10.8" rx="4.1" fill="#3B2F2F"/><rect x="305.4" y="261.2" width="20.2" height="10.8" rx="4.1" fill="#3B2F2F"/><rect x="276.4" y="172.1" width="35.1" height="54.0" rx="9.5" fill="#1F2A44"/><path d="M277.8,177.5 L288.6,226.1 L277.8,226.1 Z M310.2,177.5 L299.4,226.1 L310.2,226.1 Z" fill="#22C55E"/><rect x="277.8" y="207.2" width="32.4" height="5.4" fill="#E8FFF1" opacity=".85"/><path d="M279.1,182.9 L276.6,149.3 L264.0,118.0" stroke="#1F2A44" stroke-width="9" stroke-linecap="round" stroke-linejoin="round" fill="none"/><circle cx="264.0" cy="118.0" r="5" fill="#D9A47A" stroke="#8B5A3A" stroke-width=".8"/><path d="M308.9,182.9 L282.5,170.7 L262.0,150.0" stroke="#1F2A44" stroke-width="9" stroke-linecap="round" stroke-linejoin="round" fill="none"/><circle cx="262.0" cy="150.0" r="5" fill="#D9A47A" stroke="#8B5A3A" stroke-width=".8"/><rect x="287.9" y="166.7" width="8.1" height="10.8" fill="#D9A47A"/><circle cx="292.0" cy="154.6" r="16.2" fill="#D9A47A" stroke="#8B5A3A" stroke-width=".8"/><rect x="279.9" y="151.9" width="24.3" height="8.1" rx="4.1" fill="#9FD8F2" stroke="#2A4A6A" stroke-width="1"/><path d="M273.1,149.2 A18.9,17.6 0 0 1 310.9,149.2 Z" fill="#FFFFFF" stroke="#B8920F" stroke-width="1"/><rect x="269.1" y="147.8" width="45.9" height="5.4" rx="2.7" fill="#FFFFFF" stroke="#B8920F" stroke-width="1"/><rect x="318" y="214" width="26" height="12" rx="3" fill="#22C55E"/><rect x="342" y="217" width="12" height="5" fill="#44505F"/></svg>', '3': '<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 400 300"><defs><linearGradient id="a3-bg" x1="0" y1="0" x2="0" y2="1"><stop offset="0" stop-color="#17294B"/><stop offset="1" stop-color="#0B1630"/></linearGradient><linearGradient id="a3-glass" x1="0" y1="0" x2="1" y2="1"><stop offset="0" stop-color="#A8EAFF"/><stop offset=".55" stop-color="#43A6DD"/><stop offset="1" stop-color="#1A5E96"/></linearGradient><linearGradient id="a3-alu" x1="0" y1="0" x2="0" y2="1"><stop offset="0" stop-color="#F4F7FB"/><stop offset=".5" stop-color="#BFCAD6"/><stop offset="1" stop-color="#8793A1"/></linearGradient></defs><rect width="400" height="300" fill="url(#a3-bg)"/><rect y="270" width="400" height="30" fill="#111B30"/><rect y="268" width="400" height="4" fill="#2C3A58"/><rect x="200" y="46" width="112" height="224" rx="3" fill="url(#a3-alu)" stroke="#7B8896" stroke-width="2"/><rect x="214" y="62" width="84" height="120" rx="2" fill="url(#a3-glass)" stroke="#5A6878"/><path d="M222 70 L246 70 L224 150 L222 150 Z" fill="#fff" opacity=".35"/><rect x="214" y="196" width="84" height="58" rx="2" fill="url(#a3-alu)" stroke="#7B8896"/><rect x="288" y="118" width="7" height="60" rx="3.5" fill="#3F4A58"/><rect x="289.5" y="120" width="2" height="56" fill="#B8C6D6"/><polygon points="40,262 48,60 128,52 130,262" fill="#9BE6FF" opacity=".35" stroke="#CDEBFA" stroke-width="3"/><path d="M58 70 L92 66 L64 200 L56 200 Z" fill="#fff" opacity=".35"/><rect x="136" y="244" width="48" height="26" rx="3" fill="#B91C1C"/><rect x="136" y="244" width="48" height="6" rx="2" fill="#7F1D1D"/><rect x="154" y="238" width="12" height="8" rx="2" fill="none" stroke="#7F1D1D" stroke-width="3"/><path d="M173.4,226.1 L166.6,263.9" stroke="#27324D" stroke-width="12.2" stroke-linecap="round"/><path d="M186.9,226.1 L186.8,263.9" stroke="#27324D" stroke-width="12.2" stroke-linecap="round"/><rect x="157.1" y="261.2" width="18.9" height="10.8" rx="4.1" fill="#3B2F2F"/><rect x="177.3" y="261.2" width="20.2" height="10.8" rx="4.1" fill="#3B2F2F"/><rect x="172.4" y="172.1" width="35.1" height="54.0" rx="9.5" fill="#1F2A44"/><path d="M173.8,177.5 L184.6,226.1 L173.8,226.1 Z M206.2,177.5 L195.4,226.1 L206.2,226.1 Z" fill="#22C55E"/><rect x="173.8" y="207.2" width="32.4" height="5.4" fill="#E8FFF1" opacity=".85"/><path d="M175.2,182.9 L200.0,151.7 L232.0,128.0" stroke="#1F2A44" stroke-width="9" stroke-linecap="round" stroke-linejoin="round" fill="none"/><circle cx="232.0" cy="128.0" r="5" fill="#D9A47A" stroke="#8B5A3A" stroke-width=".8"/><path d="M204.8,182.9 L247.8,166.0 L286.0,140.0" stroke="#1F2A44" stroke-width="9" stroke-linecap="round" stroke-linejoin="round" fill="none"/><circle cx="286.0" cy="140.0" r="5" fill="#D9A47A" stroke="#8B5A3A" stroke-width=".8"/><rect x="188.8" y="166.7" width="8.1" height="10.8" fill="#D9A47A"/><circle cx="192.8" cy="154.6" r="16.2" fill="#D9A47A" stroke="#8B5A3A" stroke-width=".8"/><rect x="180.7" y="151.9" width="24.3" height="8.1" rx="4.1" fill="#9FD8F2" stroke="#2A4A6A" stroke-width="1"/><path d="M173.9,149.2 A18.9,17.6 0 0 1 211.7,149.2 Z" fill="#F5C518" stroke="#B8920F" stroke-width="1"/><rect x="169.9" y="147.8" width="45.9" height="5.4" rx="2.7" fill="#F5C518" stroke="#B8920F" stroke-width="1"/><rect x="286" y="132" width="22" height="12" rx="3" fill="#22C55E"/><rect x="306" y="136" width="10" height="4" fill="#44505F"/><rect x="290" y="143" width="8" height="14" rx="2" fill="#16A34A"/></svg>'}

ABOUT_ART = [
    ("Illustration: an Andy fabricator cutting an aluminum window profile in the workshop", "Fabrication in the workshop"),
    ("Illustration: two Andy artisans fitting an aluminum sliding window into a wall", "Installing a sliding window"),
    ("Illustration: an Andy artisan fitting the handle on an aluminum and glass door", "Finishing an aluminum door"),
]


@app.route("/about-art/<int:n>.svg")
def about_art(n):
    svg = WORKER_SVGS.get(str(n))
    if not svg:
        return Response("", status=404)
    resp = Response(svg, mimetype="image/svg+xml")
    resp.headers["Cache-Control"] = "public, max-age=86400"
    return resp


def get_about_slides(limit=6):
    """Genuine photos first (approved Our Work, one per job). Illustrations only fill the gaps."""
    conn = get_db()
    rows = conn.execute(
        "SELECT work_posts.id AS wid, work_posts.title AS title, work_photos.filename AS filename "
        "FROM work_posts JOIN work_photos ON work_photos.work_id = work_posts.id "
        "WHERE COALESCE(work_posts.status, 'approved') = 'approved' AND COALESCE(work_photos.kind, 'image') = 'image' "
        "ORDER BY work_posts.id DESC, work_photos.id ASC").fetchall()
    conn.close()
    seen, slides = set(), []
    for r in rows:
        if r["wid"] in seen:
            continue
        seen.add(r["wid"])
        slides.append({"src": photo_url_filter(r["filename"], "works"), "alt": r["title"], "caption": r["title"], "illustration": False})
        if len(slides) >= limit:
            break
    i = 0
    while len(slides) < 3 and i < len(ABOUT_ART):
        alt, cap = ABOUT_ART[i]
        slides.append({"src": url_for("about_art", n=i + 1), "alt": alt, "caption": cap, "illustration": True})
        i += 1
    return slides


def get_featured_products(limit=8):
    conn = get_db()
    rows = conn.execute("SELECT * FROM products ORDER BY id DESC LIMIT ?", (limit,)).fetchall()
    conn.close()
    return [_product_dict(r) for r in rows]


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
        <rect width="200" height="130" fill="#0A1426"/>
        <rect x="45" y="18" width="110" height="94" rx="3" fill="none" stroke="#22C55E" stroke-width="4"/>
        <line x1="100" y1="18" x2="100" y2="112" stroke="#22C55E" stroke-width="3"/>
        <line x1="45" y1="65" x2="155" y2="65" stroke="#22C55E" stroke-width="3"/>
        <rect x="50" y="23" width="45" height="37" fill="#14294A" opacity="0.7"/>
        <rect x="105" y="23" width="45" height="37" fill="#14294A" opacity="0.5"/>
        <rect x="50" y="70" width="45" height="37" fill="#14294A" opacity="0.5"/>
        <rect x="105" y="70" width="45" height="37" fill="#14294A" opacity="0.7"/>
    </svg>''',
    "Doors": '''<svg viewBox="0 0 200 130" xmlns="http://www.w3.org/2000/svg">
        <rect width="200" height="130" fill="#0A1426"/>
        <rect x="70" y="14" width="60" height="108" rx="2" fill="#14294A" opacity="0.6" stroke="#22C55E" stroke-width="4"/>
        <line x1="100" y1="14" x2="100" y2="122" stroke="#22C55E" stroke-width="2" opacity="0.5"/>
        <circle cx="118" cy="70" r="3.5" fill="#22C55E"/>
    </svg>''',
    "Partitions": '''<svg viewBox="0 0 200 130" xmlns="http://www.w3.org/2000/svg">
        <rect width="200" height="130" fill="#0A1426"/>
        <rect x="35" y="16" width="32" height="100" fill="#14294A" opacity="0.5" stroke="#22C55E" stroke-width="3"/>
        <rect x="75" y="16" width="32" height="100" fill="#14294A" opacity="0.7" stroke="#22C55E" stroke-width="3"/>
        <rect x="115" y="16" width="32" height="100" fill="#14294A" opacity="0.5" stroke="#22C55E" stroke-width="3"/>
        <rect x="155" y="16" width="20" height="100" fill="#14294A" opacity="0.3" stroke="#22C55E" stroke-width="2"/>
    </svg>''',
    "Custom Solutions": '''<svg viewBox="0 0 200 130" xmlns="http://www.w3.org/2000/svg">
        <rect width="200" height="130" fill="#0A1426"/>
        <circle cx="100" cy="65" r="34" fill="none" stroke="#22C55E" stroke-width="4"/>
        <circle cx="100" cy="65" r="10" fill="#14294A" stroke="#22C55E" stroke-width="3"/>
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
<meta name="viewport" content="width=device-width, initial-scale=1.0, viewport-fit=cover">
<title>{% block title %}ANDY | Aluminum made simple{% endblock %}</title>
<link rel="preconnect" href="https://fonts.googleapis.com">
<link href="https://fonts.googleapis.com/css2?family=Poppins:wght@500;600;700;800&family=DM+Sans:wght@400;500;600;700&family=IBM+Plex+Mono:wght@500&display=swap" rel="stylesheet">
<link rel="stylesheet" href="{{ url_for('static', filename='style.css') }}">
<script>document.documentElement.classList.add('js');try{if(sessionStorage.getItem('andySplashSeen'))document.documentElement.classList.add('no-splash')}catch(e){}</script>
</head>
{% set _m = request.cookies.get('andy_mode') %}{% set dark = (_m == 'dark') or (not _m and ((user and user.dark_mode) or default_mode == 'dark')) %}
<body class="theme-{{ user.theme if user else 'green' }} {{ 'dark-mode' if dark }} {{ 'guest-site' if not user }}">

{% if request.endpoint == 'home' %}
<div id="splash" aria-label="ANDY">
  <div class="splash-glow"></div>
  <div class="splash-center">
    <div class="splash-float">
      <div class="splash-logo"><span class="logo-mark"></span><span class="splash-word">ANDY<span>.</span></span></div>
    </div>
    <div class="splash-shadow"></div>
    <div class="splash-caption">The all-in-one service provider for you <span class="splash-smile">😊</span></div>
  </div>
  <div class="splash-bar"><i></i></div>
  <div class="splash-tap">Tap to continue</div>
</div>
{% endif %}

<div class="mobile-topbar">
  <span class="logo-mark"></span>
  <span class="mobile-topbar-title">ANDY.</span>
  {% set sm = true %}<button type="button" class="mode-switch{{ ' sm' if sm }}" role="switch" aria-checked="{{ 'true' if dark else 'false' }}" aria-label="Dark mode" onclick="toggleMode()"><span class="ms-ico ms-sun">☀️</span><span class="ms-ico ms-moon">🌙</span><span class="ms-knob"></span></button>
  <a href="{{ url_for('contact_support') if (user and user.role in ('customer', 'artisan')) else url_for('help_page') }}" class="help-icon-btn" title="Help / Customer Care" aria-label="Help and customer care">💬</a>
  <button onclick="toggleMenu()" class="hamburger-btn{% if user %} dup-tab{% endif %}" aria-label="Open menu" aria-expanded="false">☰</button>
</div>

<div id="lb" class="lb" aria-hidden="true">
  <div class="lb-top"><span class="lb-count"></span><button type="button" class="lb-close" aria-label="Close">✕</button></div>
  <div class="lb-stage"><img class="lb-img" alt=""></div>
  <button type="button" class="lb-nav lb-prev" aria-label="Previous">‹</button>
  <button type="button" class="lb-nav lb-next" aria-label="Next">›</button>
  <div class="lb-bottom"><span class="lb-cap"></span><button type="button" class="lb-rate" style="display:none;">⭐ Reviews</button></div>
</div>
<div class="menu-overlay" onclick="toggleMenu()"></div>

<div class="app-shell">
  <div class="sidebar" id="sidebar" role="navigation" aria-label="Main menu">
    <button type="button" class="menu-close" onclick="toggleMenu()" aria-label="Close menu">✕</button>
    <div class="logo"><span class="logo-mark"></span><span class="nav-word">ANDY<span>.</span></span></div>

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


    <nav>
      <a href="{{ url_for('home') }}" class="dup-tab {{ 'active' if active_page == 'home' }}"><span class="icon">🏠</span><span>Home</span></a>

      {% if not user or user.role == 'customer' %}
        <div class="nav-section-label">Browse</div>
        <a href="{{ url_for('services') }}" class="dup-tab {{ 'active' if active_page == 'services' }}"><span class="icon">🪟</span><span>Services</span></a>
        <a href="{{ url_for('catalog') }}" class="dup-tab {{ 'active' if active_page == 'catalog' }}"><span class="icon">🛒</span><span>Catalog</span></a>
        <a href="{{ url_for('works') }}" class="{{ 'active' if active_page == 'works' }}"><span class="icon">📸</span><span>Our Work</span></a>
      {% endif %}

      {% if user %}
        <div class="nav-section-label">My Account</div>
        {% if user.role == 'customer' %}
          <a href="{{ url_for('notifications_page') }}" class="{{ 'active' if active_page == 'notifications' }}"><span class="icon">🔔</span><span>Notifications</span><span class="unread-badge js-unread" {% if not customer_unread_count %}style="display:none"{% endif %}>{{ customer_unread_count }}</span></a>
          <a href="{{ url_for('request_service') }}" class="{{ 'active' if active_page == 'request_service' }}"><span class="icon">🛠️</span><span>Request a Service</span></a>
          <a href="{{ url_for('measure_tool') }}" class="{{ 'active' if active_page == 'measure' }}"><span class="icon">📐</span><span>Measure a Window</span></a>
          <a href="{{ url_for('measurement_history') }}" class="{{ 'active' if active_page == 'measure_history' }}"><span class="icon">📏</span><span>Saved Measurements</span></a>
          <a href="{{ url_for('cart') }}" class="{{ 'active' if active_page == 'cart' }}"><span class="icon">🧺</span><span>My Cart</span></a>
        {% elif user.role == 'artisan' %}
          <a href="{{ url_for('notifications_page') }}" class="{{ 'active' if active_page == 'notifications' }}"><span class="icon">🔔</span><span>Notifications</span><span class="unread-badge js-unread" {% if not customer_unread_count %}style="display:none"{% endif %}>{{ customer_unread_count }}</span></a>
          <a href="{{ url_for('artisan_jobs') }}" class="dup-tab {{ 'active' if active_page == 'artisan_jobs' }}"><span class="icon">📋</span><span>My Assigned Jobs</span></a>
          <a href="{{ url_for('artisan_work') }}" class="dup-tab {{ 'active' if active_page == 'artisan_work' }}"><span class="icon">📸</span><span>My Completed Work</span></a>
          <a href="{{ url_for('measure_tool') }}" class="{{ 'active' if active_page == 'measure' }}"><span class="icon">📐</span><span>Measure a Window</span></a>
          <a href="{{ url_for('measurement_history') }}" class="{{ 'active' if active_page == 'measure_history' }}"><span class="icon">📏</span><span>Saved Measurements</span></a>
          <a href="{{ url_for('dashboard') }}" class="{{ 'active' if active_page == 'dashboard' }}"><span class="icon">📊</span><span>Dashboard</span></a>
        {% elif user.role == 'owner' %}
          <a href="{{ url_for('admin_dashboard') }}" class="{{ 'active' if active_page == 'admin_dashboard' }}"><span class="icon">📊</span><span>Admin Overview</span></a>
          <a href="{{ url_for('admin_works') }}" class="{{ 'active' if active_page == 'admin_works' }}"><span class="icon">📸</span><span>Upload Our Work</span><span class="unread-badge" {% if not pending_work_count %}style="display:none"{% endif %}>{{ pending_work_count }}</span></a>
          <a href="{{ url_for('admin_chats') }}" class="dup-tab {{ 'active' if active_page == 'admin_chats' }}"><span class="icon">💬</span><span>Chats</span><span class="unread-badge js-unread" {% if not admin_unread_count %}style="display:none"{% endif %}>{{ admin_unread_count }}</span></a>
          <a href="{{ url_for('admin_artisans') }}" class="dup-tab {{ 'active' if active_page == 'admin_artisans' }}"><span class="icon">🧑‍🔧</span><span>Artisans</span></a>
          <a href="{{ url_for('admin_jobs') }}" class="dup-tab {{ 'active' if active_page == 'admin_jobs' }}"><span class="icon">📋</span><span>All Jobs</span></a>
          <a href="{{ url_for('dashboard_catalog') }}" class="{{ 'active' if active_page == 'dashboard_catalog' }}"><span class="icon">🛒</span><span>Manage Catalog</span></a>
          <a href="{{ url_for('admin_site') }}" class="{{ 'active' if active_page == 'admin_site' }}"><span class="icon">🖼️</span><span>Site Content</span></a>
          <a href="{{ url_for('admin_controls') }}" class="{{ 'active' if active_page == 'admin_controls' }}"><span class="icon">🎛️</span><span>Site Controls</span></a>
          <a href="{{ url_for('admin_learning') }}" class="{{ 'active' if active_page == 'admin_learning' }}"><span class="icon">📚</span><span>Upload Tips Videos</span></a>
        {% endif %}
      {% endif %}
    </nav>

    <div class="bottom-links">
      <div class="mode-row"><span>🌗 Dark mode</span><button type="button" class="mode-switch sm" role="switch" aria-checked="{{ 'true' if dark else 'false' }}" aria-label="Dark mode" onclick="toggleMode()"><span class="ms-ico ms-sun">☀️</span><span class="ms-ico ms-moon">🌙</span><span class="ms-knob"></span></button></div>
      <a href="{{ url_for('about') }}" class="{{ 'active' if active_page == 'about' }}"><span class="icon">ℹ️</span><span>About Andy</span></a>
      {% if user and user.role in ('customer', 'artisan') %}
        <a href="{{ url_for('contact_support') }}" class="dup-tab"><span class="icon">💬</span><span>Contact Andy</span></a>
        <a href="{{ url_for('support_feedback') }}"><span class="icon">📝</span><span>Feedback</span></a>
        <a href="{{ url_for('support_bug') }}"><span class="icon">🐞</span><span>Report a Bug</span></a>
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
    {% if not user %}
    <header class="site-nav" id="siteNav">
      <a class="site-nav-logo" href="{{ url_for('home') }}"><span class="logo-mark"></span><span class="nav-word">ANDY<span>.</span></span></a>
      <nav class="site-nav-links">
        <a href="{{ url_for('home') }}" class="{{ 'active' if active_page == 'home' }}">Home</a>
        <a href="{{ url_for('services') }}" class="{{ 'active' if active_page == 'services' }}">Services</a>
        <a href="{{ url_for('home') }}#how-it-works">How it works</a>
        <a href="{{ url_for('home') }}#about">About</a>
        <a href="{{ url_for('works') }}" class="{{ 'active' if active_page == 'works' }}">Our Work</a>
        <a href="{{ url_for('catalog') }}" class="{{ 'active' if active_page == 'catalog' }}">Catalogue</a>
        <a href="{{ url_for('home') }}#contact">Contact</a>
      </nav>
      <div class="site-nav-cta">
        <button type="button" class="mode-switch" role="switch" aria-checked="{{ 'true' if dark else 'false' }}" aria-label="Dark mode" onclick="toggleMode()"><span class="ms-ico ms-sun">☀️</span><span class="ms-ico ms-moon">🌙</span><span class="ms-knob"></span></button>
        <button class="btn btn-outline" onclick="document.getElementById('authModal').classList.add('open');showStep('loginForm')">Login</button>
        <button class="btn btn-purple" onclick="document.getElementById('authModal').classList.add('open')">Get Started</button>
      </div>
    </header>
    {% endif %}
    {% if user %}
    <div id="pushBar" class="push-bar" style="display:none;">
      <span>🔔 Get notified when someone sends you a message</span>
      <span class="push-actions"><button type="button" id="pushOn">Turn on</button><button type="button" id="pushLater" class="push-later">Not now</button></span>
    </div>
    {% endif %}
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
    {% if not user %}
    <footer class="site-footer">
      <div class="footer-grid">
        <div class="footer-brand">
          <div class="footer-logo"><span class="logo-mark"></span><span class="nav-word">ANDY<span>.</span></span></div>
          <p class="footer-motto">Aluminum made simple.</p>
          <p>Andy is starting with its own team of aluminum (alloy) fabricators. Every job runs through Andy, and you pay Andy.</p>
        </div>
        <div class="footer-col">
          <h4>Explore</h4>
          <a href="{{ url_for('home') }}">Home</a>
          <a href="{{ url_for('services') }}" class="{{ 'active' if active_page == 'services' }}">Services</a>
          <a href="{{ url_for('home') }}#how-it-works">How it works</a>
          <a href="{{ url_for('home') }}#about">About</a>
          <a href="{{ url_for('works') }}">Our Work</a>
          <a href="{{ url_for('catalog') }}">Catalogue</a>
        </div>
        <div class="footer-col">
          <h4>Account</h4>
          <a href="#" onclick="document.getElementById('authModal').classList.add('open');return false;">Sign up</a>
          <a href="#" onclick="document.getElementById('authModal').classList.add('open');showStep('loginForm');return false;">Login</a>
          <a href="{{ url_for('help_page') }}">Help</a>
        </div>
        <div class="footer-col">
          <h4>Contact</h4>
          {% if contact.phone %}<a href="tel:{{ contact.phone }}">📞 {{ contact.phone }}</a>{% endif %}
          {% if contact.whatsapp %}<a href="https://wa.me/{{ contact.whatsapp }}" target="_blank" rel="noopener">💬 WhatsApp</a>{% endif %}
          {% if contact.email %}<a href="mailto:{{ contact.email }}">✉️ {{ contact.email }}</a>{% endif %}
          {% if contact.address %}<span>📍 {{ contact.address }}</span>{% endif %}
          {% if not (contact.phone or contact.whatsapp or contact.email or contact.address) %}<span>Sign up to chat with Andy directly.</span>{% endif %}
        </div>
      </div>
      <div class="footer-bottom">© {{ current_year }} ANDY. All rights reserved. <span class="footer-legal"><a href="{{ url_for('terms') }}">Terms &amp; Conditions</a><a href="{{ url_for('privacy') }}">Privacy Policy</a></span></div>
    </footer>
    {% else %}
    <div class="app-footer">© {{ current_year }} ANDY · <a href="{{ url_for('terms') }}">Terms</a> · <a href="{{ url_for('privacy') }}">Privacy</a></div>
    {% endif %}
  </div>
</div>

<nav class="bottom-tabs">
  {% if user and user.role == 'artisan' %}
    <a href="{{ url_for('home') }}" class="{{ 'active' if active_page == 'home' }}"><span>🏠</span>Home</a>
    <a href="{{ url_for('artisan_jobs') }}" class="{{ 'active' if active_page == 'artisan_jobs' }}"><span>📋</span>Jobs</a>
    <a href="{{ url_for('artisan_work') }}" class="{{ 'active' if active_page == 'artisan_work' }}"><span>📸</span>My Work</a>
    <button onclick="toggleMenu()"><span>⚙️</span>More</button>
  {% elif user and user.role == 'owner' %}
    <a href="{{ url_for('home') }}" class="{{ 'active' if active_page == 'home' }}"><span>🏠</span>Home</a>
    <a href="{{ url_for('admin_chats') }}" class="{{ 'active' if active_page == 'admin_chats' }}"><span>💬</span>Chats<span class="unread-badge js-unread" style="position:absolute;margin-left:2px;{% if not admin_unread_count %}display:none;{% endif %}">{{ admin_unread_count }}</span></a>
    <a href="{{ url_for('admin_jobs') }}" class="{{ 'active' if active_page == 'admin_jobs' }}"><span>📋</span>Jobs</a>
    <a href="{{ url_for('admin_artisans') }}" class="{{ 'active' if active_page == 'admin_artisans' }}"><span>🧑‍🔧</span>Techs</a>
    <button onclick="toggleMenu()"><span>⚙️</span>More</button>
  {% else %}
    <a href="{{ url_for('home') }}" class="{{ 'active' if active_page == 'home' }}"><span>🏠</span>Home</a>
    <a href="{{ url_for('services') }}" class="{{ 'active' if active_page == 'services' }}"><span>🪟</span>Services</a>
    <a href="{{ url_for('catalog') }}" class="{{ 'active' if active_page == 'catalog' }}"><span>🛒</span>Catalogue</a>
    {% if user %}
      <button onclick="toggleMenu()"><span>⚙️</span>More</button>
    {% else %}
      <button onclick="toggleMenu()"><span>🔑</span>Login</button>
    {% endif %}
  {% endif %}
</nav>

{% include "_auth_modal.html" %}



<script>
window.toggleMode = function() {
  var dark = !document.body.classList.contains('dark-mode');
  document.body.classList.toggle('dark-mode', dark);
  document.cookie = 'andy_mode=' + (dark ? 'dark' : 'light') + '; path=/; max-age=31536000; SameSite=Lax';
  [].forEach.call(document.querySelectorAll('.mode-switch'), function(b) { b.setAttribute('aria-checked', dark ? 'true' : 'false'); });
  {% if user %}
  var fd = new FormData(); fd.append('csrf_token', '{{ csrf_token() }}'); fd.append('dark', dark ? '1' : '0');
  fetch('{{ url_for("set_mode") }}', { method: 'POST', body: fd, credentials: 'same-origin' }).catch(function() {});
  {% endif %}
};
</script>
<script>
(function() {
  var CSRF = '{{ csrf_token() }}';
  var LOGGED_IN = {{ 'true' if user else 'false' }};
  document.addEventListener('click', function(e) {
    var b = e.target.closest ? e.target.closest('.like-btn') : null;
    if (!b) return;
    e.preventDefault();
    if (!LOGGED_IN) { var m = document.getElementById('authModal'); if (m) m.classList.add('open'); return; }
    if (b.dataset.busy) return;
    b.dataset.busy = '1';
    var fd = new FormData(); fd.append('csrf_token', CSRF);
    fetch(b.dataset.url, { method: 'POST', body: fd, credentials: 'same-origin' })
      .then(function(r) { return r.ok ? r.json() : null; })
      .then(function(d) {
        if (!d) return;
        b.classList.toggle('liked', d.liked);
        b.querySelector('.like-icon').textContent = d.liked ? '♥' : '♡';
        b.querySelector('.like-count').textContent = d.count;
        if (d.liked) { b.classList.remove('pop'); void b.offsetWidth; b.classList.add('pop'); }
      }).catch(function() {}).then(function() { delete b.dataset.busy; });
  });
  document.addEventListener('change', function(e) {
    var inp = e.target;
    if (!inp.matches || !inp.matches('input[type=file][data-maxmb]')) return;
    var max = parseFloat(inp.dataset.maxmb) * 1024 * 1024, bad = [];
    [].forEach.call(inp.files, function(f) { if (f.size > max) bad.push(f.name); });
    if (bad.length) { alert('These files are too big (limit ' + inp.dataset.maxmb + ' MB): ' + bad.join(', ') + '. Trim the video or lower its quality and try again.'); inp.value = ''; }
  });
})();
</script>
<script>
(function() {
  var lb = document.getElementById('lb');
  if (!lb) return;
  var stage = lb.querySelector('.lb-stage'), img = lb.querySelector('.lb-img');
  var cap = lb.querySelector('.lb-cap'), count = lb.querySelector('.lb-count');
  var prev = lb.querySelector('.lb-prev'), next = lb.querySelector('.lb-next'), rate = lb.querySelector('.lb-rate');
  var items = [], idx = 0, S = 1, X = 0, Y = 0, pointers = {}, startDist = 0, startS = 1, lastTap = 0, moved = false, startX = 0, startY = 0;

  function apply() {
    img.style.transform = 'translate(' + X + 'px,' + Y + 'px) scale(' + S + ')';
    stage.classList.toggle('zoomed', S > 1);
  }
  function reset() { S = 1; X = 0; Y = 0; apply(); }
  function show(i) {
    idx = (i + items.length) % items.length;
    img.src = items[idx].src;
    cap.textContent = items[idx].cap;
    count.textContent = items.length > 1 ? (idx + 1) + ' / ' + items.length : '';
    prev.style.display = next.style.display = items.length > 1 ? '' : 'none';
    rate.style.display = items[idx].rev ? '' : 'none';
    reset();
  }
  function open(group, i) {
    var els = [].slice.call(document.querySelectorAll('[data-lightbox="' + group + '"]'));
    items = els.map(function(e) { return { src: e.getAttribute('data-full') || e.src, cap: e.getAttribute('data-caption') || '', rev: e.getAttribute('data-reviews') || '' }; });
    lb.classList.add('open'); lb.setAttribute('aria-hidden', 'false');
    document.body.style.overflow = 'hidden';
    show(i);
  }
  function close() {
    lb.classList.remove('open'); lb.setAttribute('aria-hidden', 'true');
    document.body.style.overflow = ''; img.removeAttribute('src');
  }
  function zoomAt(cx, cy, ns) {
    var r = stage.getBoundingClientRect();
    var px = cx - (r.left + r.width / 2), py = cy - (r.top + r.height / 2);
    X = px - (px - X) * (ns / S); Y = py - (py - Y) * (ns / S); S = ns;
    if (S <= 1.01) { S = 1; X = 0; Y = 0; }
    apply();
  }

  document.addEventListener('click', function(e) {
    var t = e.target.closest ? e.target.closest('[data-lightbox]') : null;
    if (!t) return;
    e.preventDefault();
    var g = t.getAttribute('data-lightbox');
    open(g, [].slice.call(document.querySelectorAll('[data-lightbox="' + g + '"]')).indexOf(t));
  });
  lb.querySelector('.lb-close').onclick = close;
  prev.onclick = function(e) { e.stopPropagation(); show(idx - 1); };
  next.onclick = function(e) { e.stopPropagation(); show(idx + 1); };
  rate.onclick = function() {
    var id = items[idx].rev; close();
    if (window.toggleReviews) window.toggleReviews(id, true);
    var el = document.getElementById(id); if (el) el.scrollIntoView({ behavior: 'smooth', block: 'center' });
  };
  document.addEventListener('keydown', function(e) {
    if (!lb.classList.contains('open')) return;
    if (e.key === 'Escape') close();
    else if (e.key === 'ArrowLeft') show(idx - 1);
    else if (e.key === 'ArrowRight') show(idx + 1);
  });
  stage.addEventListener('wheel', function(e) {
    e.preventDefault();
    zoomAt(e.clientX, e.clientY, Math.max(1, Math.min(5, S * (e.deltaY < 0 ? 1.2 : 0.83))));
  }, { passive: false });

  function dist() { var k = Object.keys(pointers); var a = pointers[k[0]], b = pointers[k[1]]; return Math.hypot(a.x - b.x, a.y - b.y); }
  stage.addEventListener('pointerdown', function(e) {
    stage.setPointerCapture(e.pointerId);
    pointers[e.pointerId] = { x: e.clientX, y: e.clientY };
    moved = false; startX = e.clientX; startY = e.clientY;
    if (Object.keys(pointers).length === 2) { startDist = dist(); startS = S; }
  });
  stage.addEventListener('pointermove', function(e) {
    var p = pointers[e.pointerId]; if (!p) return;
    var n = Object.keys(pointers).length;
    if (n === 2) {
      p.x = e.clientX; p.y = e.clientY;
      var k = Object.keys(pointers), a = pointers[k[0]], b = pointers[k[1]];
      zoomAt((a.x + b.x) / 2, (a.y + b.y) / 2, Math.max(1, Math.min(5, startS * dist() / startDist)));
      moved = true; return;
    }
    var dx = e.clientX - p.x, dy = e.clientY - p.y;
    p.x = e.clientX; p.y = e.clientY;
    if (Math.abs(e.clientX - startX) > 6 || Math.abs(e.clientY - startY) > 6) moved = true;
    if (S > 1) { X += dx; Y += dy; apply(); }
  });
  function end(e) {
    var p = pointers[e.pointerId]; if (!p) return;
    var n = Object.keys(pointers).length;
    delete pointers[e.pointerId];
    if (n !== 1) return;
    var dx = e.clientX - startX, dy = e.clientY - startY;
    if (S === 1 && moved && Math.abs(dx) > 60 && Math.abs(dy) < 90 && items.length > 1) { show(dx < 0 ? idx + 1 : idx - 1); return; }
    if (S === 1 && moved && dy > 110 && Math.abs(dx) < 90) { close(); return; }
    if (!moved) {
      var now = Date.now();
      if (now - lastTap < 320) { lastTap = 0; zoomAt(e.clientX, e.clientY, S > 1 ? 1 : 2.5); return; }
      lastTap = now;
      setTimeout(function() { if (lastTap && Date.now() - lastTap >= 300 && S === 1 && e.target === stage) close(); }, 320);
    }
  }
  stage.addEventListener('pointerup', end);
  stage.addEventListener('pointercancel', function(e) { delete pointers[e.pointerId]; });
})();

window.toggleReviews = function(id, forceOpen) {
  var box = document.getElementById(id); if (!box) return;
  var panel = box.querySelector('.rev-panel');
  panel.hidden = forceOpen ? false : !panel.hidden;
  box.classList.toggle('open', !panel.hidden);
};
if (location.hash.indexOf('#reviews-') === 0) {
  window.toggleReviews(location.hash.slice(1), true);
  var _r = document.getElementById(location.hash.slice(1)); if (_r) setTimeout(function() { _r.scrollIntoView({ block: 'center' }); }, 300);
}
</script>

<script>
(function() {
  function init(c) {
    var track = c.querySelector('.carousel-track');
    if (!track) return;
    var prev = c.querySelector('.prev'), next = c.querySelector('.next'), dotsBox = c.querySelector('.carousel-dots');
    var slides = [].slice.call(track.children);
    function step() {
      var f = slides[0]; if (!f) return track.clientWidth;
      var cs = getComputedStyle(track); var gap = parseFloat(cs.columnGap || cs.gap || 0) || 0;
      return f.getBoundingClientRect().width + gap;
    }
    var dots = [];
    if (dotsBox && slides.length > 1) {
      slides.forEach(function(_, i) {
        var b = document.createElement('button'); b.type = 'button'; b.setAttribute('aria-label', 'Go to item ' + (i + 1));
        b.addEventListener('click', function() { track.scrollTo({ left: i * step(), behavior: 'smooth' }); });
        dotsBox.appendChild(b); dots.push(b);
      });
    }
    function update() {
      var max = track.scrollWidth - track.clientWidth;
      c.classList.toggle('no-scroll', max <= 3);
      if (prev) prev.disabled = track.scrollLeft <= 3;
      if (next) next.disabled = track.scrollLeft >= max - 3;
      var idx = Math.round(track.scrollLeft / (step() || 1));
      dots.forEach(function(d, i) { d.classList.toggle('on', i === idx); });
    }
    var tick = null;
    track.addEventListener('scroll', function() { if (tick) return; tick = requestAnimationFrame(function() { tick = null; update(); }); }, { passive: true });
    if (prev) prev.addEventListener('click', function() { track.scrollBy({ left: -step(), behavior: 'smooth' }); });
    if (next) next.addEventListener('click', function() { track.scrollBy({ left: step(), behavior: 'smooth' }); });
    track.addEventListener('keydown', function(e) {
      if (e.key === 'ArrowRight') { e.preventDefault(); track.scrollBy({ left: step(), behavior: 'smooth' }); }
      if (e.key === 'ArrowLeft') { e.preventDefault(); track.scrollBy({ left: -step(), behavior: 'smooth' }); }
    });
    window.addEventListener('resize', update);
    window.addEventListener('load', update);
    update();
  }
  [].forEach.call(document.querySelectorAll('[data-carousel]'), init);
})();
</script>
<script>
  (function() {
    var els = document.querySelectorAll('.reveal');
    if (!('IntersectionObserver' in window)) { els.forEach(function(e) { e.classList.add('in'); }); }
    else {
      var io = new IntersectionObserver(function(entries) {
        entries.forEach(function(en) { if (en.isIntersecting) { en.target.classList.add('in'); io.unobserve(en.target); } });
      }, { threshold: 0.12, rootMargin: '0px 0px -40px 0px' });
      els.forEach(function(e) { io.observe(e); });
    }
    var nav = document.getElementById('siteNav');
    if (nav) window.addEventListener('scroll', function() { nav.classList.toggle('scrolled', window.scrollY > 10); }, { passive: true });
  })();
  window.updateUnreadBadges = function(n) {
    n = parseInt(n, 10) || 0;
    document.querySelectorAll('.js-unread').forEach(function(b) {
      b.textContent = n; b.style.display = n ? '' : 'none';
    });
    document.title = (n ? '(' + n + ') ' : '') + document.title.replace(/^\\(\\d+\\)\\s*/, '');
  };
  {% if user and user.role in ('customer', 'owner', 'artisan') %}
  setInterval(function() {
    if (document.hidden) return;
    fetch('{{ url_for("api_unread") }}', {credentials: 'same-origin'})
      .then(function(r) { return r.ok ? r.json() : null; })
      .then(function(d) { if (d) window.updateUnreadBadges(d.unread); })
      .catch(function() {});
  }, 5000);
  {% endif %}
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
    var open = document.body.classList.toggle('menu-open');
    [].forEach.call(document.querySelectorAll('.hamburger-btn, .bottom-tabs button'), function(b) { b.setAttribute('aria-expanded', open ? 'true' : 'false'); });
  }
  document.addEventListener('keydown', function(e) {
    if (e.key === 'Escape' && document.body.classList.contains('menu-open')) toggleMenu();
  });
  document.addEventListener('DOMContentLoaded', function() {
    document.querySelectorAll('.sidebar a, .sidebar button').forEach(function(el) {
      el.addEventListener('click', function() { document.body.classList.remove('menu-open'); });
    });
  });
  {% if auto_open_auth %}
    openAuth();
  {% endif %}
</script>


{% if user and user.role == 'customer' and not user.has_seen_guide and request.endpoint == 'home' %}
<script>
window.startAndyTour = function() {
  var defs = [
    {sel: '.hero-name', title: 'Welcome to ANDY 😊', text: "Let me show you around. It takes about 20 seconds."},
    {sel: 'a[href$="/catalog"]', title: 'Catalogue 🛒', text: 'Browse windows, doors and more, with prices and sizes, ready to order.'},
    {sel: '.sidebar a[href$="/request-service"]', title: 'Request a Service 🛠️', text: 'Need something fixed or built? Start a request here and Andy takes it from there.'},
    {sel: '.sidebar a[href$="/notifications"]', title: 'Notifications 🔔', text: 'A green number shows up here whenever Andy or your artisan replies.'},
    {sel: '.help-icon-btn, .sidebar a[href$="/contact-support"]', title: 'Talk to Andy 💬', text: 'Tap here any time to chat directly, with photos and files.'},
    {sel: '.bottom-tabs button', title: 'More ⚙️', text: 'Your cart, measurements, notifications, settings and everything else live in this menu.'},
    {sel: '.sidebar a[href$="/settings"]', title: 'Settings ⚙️', text: 'Change your profile, theme and dark mode here.'}
  ];

  function visible(sel) {
    var list = document.querySelectorAll(sel);
    for (var i = 0; i < list.length; i++) {
      var r = list[i].getBoundingClientRect();
      if (r.width > 0 && r.height > 0 && r.right > 0 && r.left < window.innerWidth && r.bottom > 0 && r.top < window.innerHeight + 2000) return list[i];
    }
    return null;
  }

  var steps = [];
  defs.forEach(function(d) { var el = visible(d.sel); if (el) steps.push({el: el, title: d.title, text: d.text}); });
  steps.push({el: null, title: "You're all set 🎉", text: 'Welcome to the family. Go ahead and explore ANDY.'});

  var block = document.createElement('div'); block.className = 'tour-block';
  var spot = document.createElement('div'); spot.className = 'tour-spot';
  var card = document.createElement('div'); card.className = 'tour-card';
  document.body.appendChild(block); document.body.appendChild(spot); document.body.appendChild(card);

  var i = 0;
  function finish() {
    [block, spot, card].forEach(function(n) { n.remove(); });
    window.removeEventListener('resize', place);
    var fd = new FormData();
    fd.append('csrf_token', '{{ csrf_token() }}');
    fetch('{{ url_for("dismiss_guide") }}', {method: 'POST', body: fd, credentials: 'same-origin', redirect: 'manual'}).catch(function() {});
  }
  function place() {
    var s = steps[i];
    var vw = window.innerWidth, vh = window.innerHeight;
    var w = Math.min(320, vw - 24);
    card.style.width = w + 'px';
    var h = card.offsetHeight;
    var r = s.el ? s.el.getBoundingClientRect() : null;
    // the target must really be on screen; otherwise show a plain centred card (never off-screen)
    var onScreen = r && r.width > 0 && r.bottom > 0 && r.top < vh && r.right > 0 && r.left < vw;
    if (onScreen) {
      var pad = 6;
      spot.style.cssText = 'left:' + (r.left - pad) + 'px;top:' + (r.top - pad) + 'px;width:' + (r.width + pad * 2) + 'px;height:' + (r.height + pad * 2) + 'px;';
      var left = Math.max(12, Math.min(r.left + r.width / 2 - w / 2, vw - w - 12));
      var top = (r.bottom + 16 + h < vh) ? r.bottom + 14 : r.top - h - 14;
      top = Math.max(12, Math.min(top, vh - h - 12));
      card.style.left = left + 'px'; card.style.top = top + 'px';
    } else {
      spot.style.cssText = 'left:' + (vw / 2) + 'px;top:' + (vh / 2) + 'px;width:0;height:0;';
      card.style.left = Math.max(12, (vw - w) / 2) + 'px'; card.style.top = Math.max(12, (vh - h) / 2) + 'px';
    }
    card.style.transform = 'none';
  }
  function show() {
    var s = steps[i], last = i === steps.length - 1;
    if (s.el && s.el.scrollIntoView) s.el.scrollIntoView({block: 'center', inline: 'nearest'});
    var dots = '';
    for (var k = 0; k < steps.length; k++) dots += '<i class="' + (k === i ? 'on' : '') + '"></i>';
    card.innerHTML = '<button class="tour-x" type="button" aria-label="Close tour">✕</button><div class="tour-title">' + s.title + '</div><div class="tour-text">' + s.text + '</div>' +
      '<div class="tour-foot"><div class="tour-dots">' + dots + '</div><div>' +
      (last ? '' : '<button class="tour-skip" type="button">Skip</button>') +
      '<button class="tour-next" type="button">' + (last ? 'Okay' : 'Next') + '</button></div></div>';
    card.querySelector('.tour-next').onclick = function() { if (last) finish(); else { i++; show(); } };
    var sk = card.querySelector('.tour-skip'); if (sk) sk.onclick = finish;
    card.querySelector('.tour-x').onclick = finish;
    var nb = card.querySelector('.tour-next'); if (nb && nb.focus) nb.focus({ preventScroll: true });
    setTimeout(place, 60);
  }
  window.addEventListener('resize', place);
  document.addEventListener('keydown', function esc(e) { if (e.key === 'Escape' && document.querySelector('.tour-card')) { document.removeEventListener('keydown', esc); finish(); } });
  show();
};
</script>
{% endif %}
<script>
(function() {
  var sp = document.getElementById('splash');
  function after() { if (window.startAndyTour) window.startAndyTour(); }
  if (!sp || document.documentElement.classList.contains('no-splash')) { if (sp) sp.remove(); after(); return; }
  document.body.style.overflow = 'hidden';
  function close() {
    if (sp.classList.contains('hide')) return;
    sp.classList.add('hide');
    try { sessionStorage.setItem('andySplashSeen', '1'); } catch (e) {}
    document.body.style.overflow = '';
    setTimeout(function() { sp.remove(); after(); }, 750);
  }
  sp.addEventListener('click', close);
  setTimeout(close, 3800);
})();
</script>

<script>
(function() {
  var bar = document.getElementById('pushBar');
  if (!bar || !('serviceWorker' in navigator) || !('PushManager' in window) || !('Notification' in window) || !window.isSecureContext) return;
  var csrf = '{{ csrf_token() }}';
  function toKey(b) {
    var pad = '='.repeat((4 - b.length % 4) % 4);
    var raw = atob((b + pad).replace(/-/g, '+').replace(/_/g, '/'));
    var out = new Uint8Array(raw.length);
    for (var i = 0; i < raw.length; i++) out[i] = raw.charCodeAt(i);
    return out;
  }
  function save(sub) {
    var fd = new FormData();
    fd.append('csrf_token', csrf);
    fd.append('subscription', JSON.stringify(sub));
    return fetch('/push/subscribe', { method: 'POST', body: fd, credentials: 'same-origin' });
  }
  function subscribe(key) {
    return navigator.serviceWorker.register('/sw.js').then(function() { return navigator.serviceWorker.ready; })
      .then(function(reg) {
        return reg.pushManager.getSubscription().then(function(s) {
          return s || reg.pushManager.subscribe({ userVisibleOnly: true, applicationServerKey: toKey(key) });
        });
      }).then(save);
  }
  function dismissedRecently() {
    try { var t = parseInt(localStorage.getItem('andyPushDismissed') || '0', 10); return t && Date.now() - t < 7 * 86400000; } catch (e) { return false; }
  }
  fetch('/push/key', { credentials: 'same-origin' }).then(function(r) { return r.json(); }).then(function(cfg) {
    if (!cfg.enabled) return;
    if (Notification.permission === 'granted') { subscribe(cfg.key).catch(function() {}); return; }
    if (Notification.permission === 'denied' || dismissedRecently()) return;
    bar.style.display = 'flex';
    document.getElementById('pushOn').onclick = function() {
      Notification.requestPermission().then(function(p) {
        if (p !== 'granted') { bar.style.display = 'none'; return; }
        subscribe(cfg.key).then(function() {
          bar.innerHTML = '<span>✅ Notifications are on</span>';
          setTimeout(function() { bar.style.display = 'none'; }, 2500);
        }).catch(function() { bar.style.display = 'none'; });
      });
    };
    document.getElementById('pushLater').onclick = function() {
      try { localStorage.setItem('andyPushDismissed', String(Date.now())); } catch (e) {}
      bar.style.display = 'none';
    };
  }).catch(function() {});

  // On logout, stop sending this device the previous user's notifications.
  document.addEventListener('click', function(e) {
    var a = e.target.closest ? e.target.closest('a[href$="/logout"]') : null;
    if (!a) return;
    e.preventDefault();
    var go = function() { window.location.href = a.href; };
    var timer = setTimeout(go, 1200);
    navigator.serviceWorker.getRegistration().then(function(reg) { return reg ? reg.pushManager.getSubscription() : null; })
      .then(function(sub) {
        if (!sub) return;
        var fd = new FormData(); fd.append('csrf_token', csrf); fd.append('endpoint', sub.endpoint);
        return fetch('/push/unsubscribe', { method: 'POST', body: fd, credentials: 'same-origin' });
      }).catch(function() {}).then(function() { clearTimeout(timer); go(); });
  });
})();
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
        <p class="terms-note">Terms and conditions apply. By continuing you agree to our <a href="{{ url_for('terms') }}">Terms &amp; Conditions</a> and <a href="{{ url_for('privacy') }}">Privacy Policy</a>.</p>
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
        <p class="terms-note">Terms and conditions apply. By continuing you agree to our <a href="{{ url_for('terms') }}">Terms &amp; Conditions</a> and <a href="{{ url_for('privacy') }}">Privacy Policy</a>.</p>
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

{% set hero_bg = (hero_photos[0].filename|photo_url("hero")) if hero_photos else "" %}
<div class="hero" style="{% if hero_bg %}background-image:url('{{ hero_bg }}');{% endif %}">
  {% if not hero_photos %}
  <div class="hero-default-bg">
    <svg width="100%" height="100%" viewBox="0 0 800 400" xmlns="http://www.w3.org/2000/svg" preserveAspectRatio="xMidYMax slice">
      <defs>
        <linearGradient id="skyG" x1="0" y1="0" x2="0" y2="1">
          <stop offset="0%" stop-color="#0A1426"/>
          <stop offset="100%" stop-color="#10203A"/>
        </linearGradient>
        <linearGradient id="glassG" x1="0" y1="0" x2="0" y2="1">
          <stop offset="0%" stop-color="#14294A"/>
          <stop offset="100%" stop-color="#0C1A30"/>
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
    <div class="hero-kicker">Aluminum made simple</div>
    <h1 class="hero-name hero-headline">Find the Right Professional for the Job.</h1>
    {% set old_tag = "Connecting you with trusted artisans when you need them." %}
    <p class="hero-title">{% if site.tagline and site.tagline != old_tag %}{{ site.tagline }}{% else %}From home repairs to installations, Andy helps you connect with professionals for the work you need done.{% endif %}</p>
    {% if not user or user.role == 'customer' %}
    <div class="hero-actions">
      {% if user %}<a href="{{ url_for('request_service') }}" class="btn btn-purple">Request a Service</a>
      {% else %}<a href="#" onclick="document.getElementById('authModal').classList.add('open');return false;" class="btn btn-purple">Request a Service</a>{% endif %}
      <a href="{{ url_for('services') }}" class="btn btn-outline-light">Explore Services</a>
    </div>
    {% endif %}
  </div>
</div>

<section class="lp-section" id="services">
  <div class="lp-head reveal">
    <span class="lp-eyebrow">Services</span>
    <h2 class="lp-title">What Andy offers</h2>
    <p class="lp-lead">{% if site.what_offers %}{{ site.what_offers }}{% else %}Aluminum (alloy) windows, doors, partitions, curtain walls and maintenance, made and fitted by our own artisans.{% endif %}</p>
  </div>
  {% set req_href = url_for('request_service') if (user and user.role == 'customer') else ('#' if not user else url_for('catalog')) %}
  <div class="carousel carousel-cards" data-carousel role="region" aria-roledescription="carousel" aria-label="Andy services">
    <div class="carousel-track" tabindex="0">
      <a class="svc-card" href="{{ url_for("services") }}#windows">
        <div class="svc-art svc-art-1"><svg viewBox="0 0 400 300" class="svc-svg" role="img" aria-label="3D aluminum sliding window"><defs>
<linearGradient id="w-alu" x1="0" y1="0" x2="0" y2="1"><stop offset="0" stop-color="#F6F9FC"/><stop offset=".45" stop-color="#C9D3DE"/><stop offset="1" stop-color="#8E9AA8"/></linearGradient>
<linearGradient id="w-alu-h" x1="0" y1="0" x2="1" y2="0"><stop offset="0" stop-color="#E9EEF4"/><stop offset=".5" stop-color="#BCC7D3"/><stop offset="1" stop-color="#8794A3"/></linearGradient>
<linearGradient id="w-side" x1="0" y1="0" x2="1" y2="0"><stop offset="0" stop-color="#8F9BAA"/><stop offset="1" stop-color="#586474"/></linearGradient>
<linearGradient id="w-top" x1="0" y1="1" x2="0" y2="0"><stop offset="0" stop-color="#CBD5E0"/><stop offset="1" stop-color="#F3F7FB"/></linearGradient>
<linearGradient id="w-glass" x1="0" y1="0" x2="1" y2="1"><stop offset="0" stop-color="#A8EAFF"/><stop offset=".5" stop-color="#43A6DD"/><stop offset="1" stop-color="#1A5E96"/></linearGradient>
<linearGradient id="w-glass2" x1="0" y1="0" x2="0" y2="1"><stop offset="0" stop-color="#9BE6FF" stop-opacity=".9"/><stop offset="1" stop-color="#2A78B4" stop-opacity=".85"/></linearGradient>
<filter id="w-blur" x="-20%" y="-50%" width="140%" height="200%"><feGaussianBlur stdDeviation="7"/></filter>
</defs><ellipse cx="195" cy="268" rx="135" ry="11" fill="#000" opacity=".5" filter="url(#w-blur)"/><g stroke="#5EE9A0" stroke-width="1.2" stroke-dasharray="4 4" opacity=".75" fill="none"><path d="M80 38 H280"/><path d="M80 32 V44 M280 32 V44"/><path d="M52 70 V230"/><path d="M46 70 H58 M46 230 H58"/></g><g fill="#5EE9A0" font-family="DM Sans, sans-serif" font-size="11" opacity=".9"><text x="158" y="31">150 cm</text><text x="8" y="154" transform="rotate(-90 20 150)">120 cm</text></g><polygon points="280.0,70.0 306.0,50.0 306.0,210.0 280.0,230.0" fill="url(#w-side)"/><polygon points="80.0,70.0 106.0,50.0 306.0,50.0 280.0,70.0" fill="url(#w-top)"/><polygon points="280.0,70.0 306.0,50.0 306.0,210.0 280.0,230.0" fill="none" stroke="#475262" stroke-width="1"/><rect x="80" y="70" width="200" height="160" rx="3" fill="url(#w-alu)" stroke="#7F8C9B" stroke-width="1.5"/><rect x="96" y="86" width="168" height="128" fill="#16456E"/><rect x="96" y="86" width="88" height="128" fill="url(#w-alu-h)" stroke="#7F8C9B"/><rect x="104" y="94" width="72" height="112" fill="url(#w-glass)" stroke="#5A6878" stroke-width="1"/><clipPath id="w-cl"><rect x="104" y="94" width="72" height="112" rx="2"/></clipPath>
<g clip-path="url(#w-cl)"><g class="svc-shine" ><polygon points="94.0,206.0 129.2,94.0 143.6,94.0 118.4,206.0" fill="#fff" opacity=".38"/><polygon points="136.4,206.0 161.6,94.0 167.4,94.0 142.2,206.0" fill="#fff" opacity=".2"/></g></g><rect x="178" y="86" width="86" height="128" fill="url(#w-alu-h)" stroke="#6C7988" stroke-width="1.3"/><rect x="186" y="94" width="70" height="112" fill="url(#w-glass)" stroke="#5A6878" stroke-width="1"/><clipPath id="w-cr"><rect x="186" y="94" width="70" height="112" rx="2"/></clipPath>
<g clip-path="url(#w-cr)"><g class="svc-shine" style="animation-delay:.6s"><polygon points="176.0,206.0 210.5,94.0 224.5,94.0 200.0,206.0" fill="#fff" opacity=".38"/><polygon points="217.5,206.0 242.0,94.0 247.6,94.0 223.1,206.0" fill="#fff" opacity=".2"/></g></g><rect x="180" y="138" width="5" height="30" rx="2.5" fill="#44505F"/><rect x="180.8" y="139" width="1.6" height="28" rx=".8" fill="#9FB0C2"/><path d="M82 72 H278" stroke="#fff" stroke-width="1.6" opacity=".8"/><path d="M82 72 V228" stroke="#fff" stroke-width="1.2" opacity=".6"/><polygon points="72.0,230.0 98.0,214.0 314.0,214.0 288.0,230.0" fill="url(#w-top)" stroke="#8794A3" stroke-width=".8"/><rect x="72" y="230" width="216" height="12" fill="url(#w-alu)" stroke="#7F8C9B"/><polygon points="288.0,230.0 314.0,214.0 314.0,226.0 288.0,242.0" fill="url(#w-side)"/></svg></div>
        <h3>Windows</h3>
        <p>Sliding and fixed aluminum windows, made to size.</p>
        <span class="svc-go">See windows →</span>
      </a>
      <a class="svc-card" href="{{ url_for("services") }}#doors">
        <div class="svc-art svc-art-2"><svg viewBox="0 0 400 300" class="svc-svg" role="img" aria-label="3D aluminum and glass door"><defs>
<linearGradient id="d-alu" x1="0" y1="0" x2="0" y2="1"><stop offset="0" stop-color="#F6F9FC"/><stop offset=".45" stop-color="#C9D3DE"/><stop offset="1" stop-color="#8E9AA8"/></linearGradient>
<linearGradient id="d-alu-h" x1="0" y1="0" x2="1" y2="0"><stop offset="0" stop-color="#E9EEF4"/><stop offset=".5" stop-color="#BCC7D3"/><stop offset="1" stop-color="#8794A3"/></linearGradient>
<linearGradient id="d-side" x1="0" y1="0" x2="1" y2="0"><stop offset="0" stop-color="#8F9BAA"/><stop offset="1" stop-color="#586474"/></linearGradient>
<linearGradient id="d-top" x1="0" y1="1" x2="0" y2="0"><stop offset="0" stop-color="#CBD5E0"/><stop offset="1" stop-color="#F3F7FB"/></linearGradient>
<linearGradient id="d-glass" x1="0" y1="0" x2="1" y2="1"><stop offset="0" stop-color="#A8EAFF"/><stop offset=".5" stop-color="#43A6DD"/><stop offset="1" stop-color="#1A5E96"/></linearGradient>
<linearGradient id="d-glass2" x1="0" y1="0" x2="0" y2="1"><stop offset="0" stop-color="#9BE6FF" stop-opacity=".9"/><stop offset="1" stop-color="#2A78B4" stop-opacity=".85"/></linearGradient>
<filter id="d-blur" x="-20%" y="-50%" width="140%" height="200%"><feGaussianBlur stdDeviation="7"/></filter>
</defs><ellipse cx="205" cy="272" rx="120" ry="11" fill="#000" opacity=".5" filter="url(#d-blur)"/><g stroke="#5EE9A0" stroke-width="1.2" stroke-dasharray="4 4" opacity=".75" fill="none"><path d="M96 36 V250"/><path d="M90 36 H102 M90 250 H102"/><path d="M130 22 H250"/><path d="M130 16 V28 M250 16 V28"/></g><g fill="#5EE9A0" font-family="DM Sans, sans-serif" font-size="11" opacity=".9"><text x="170" y="15">90 cm</text><text x="62" y="148" transform="rotate(-90 70 142)">210 cm</text></g><polygon points="250.0,40.0 274.0,26.0 274.0,242.0 250.0,256.0" fill="url(#d-side)"/><polygon points="130.0,40.0 154.0,26.0 274.0,26.0 250.0,40.0" fill="url(#d-top)"/><rect x="130" y="40" width="120" height="216" rx="3" fill="url(#d-alu)" stroke="#7F8C9B" stroke-width="1.5"/><rect x="142" y="52" width="96" height="198" fill="#14405F"/><rect x="142" y="52" width="96" height="198" fill="url(#d-alu-h)" stroke="#6C7988" stroke-width="1.3"/><rect x="154" y="64" width="72" height="112" rx="2" fill="url(#d-glass)" stroke="#546273"/><clipPath id="d-c"><rect x="154" y="64" width="72" height="112" rx="2"/></clipPath>
<g clip-path="url(#d-c)"><g class="svc-shine" ><polygon points="144.0,176.0 179.2,64.0 193.6,64.0 168.4,176.0" fill="#fff" opacity=".38"/><polygon points="186.4,176.0 211.6,64.0 217.4,64.0 192.2,176.0" fill="#fff" opacity=".2"/></g></g><rect x="154" y="190" width="72" height="48" rx="2" fill="url(#d-alu)" stroke="#7F8C9B"/><rect x="158" y="194" width="64" height="40" rx="1.5" fill="none" stroke="#fff" stroke-opacity=".7"/><rect x="158" y="194" width="64" height="40" rx="1.5" fill="none" stroke="#8794A3" stroke-opacity=".6" transform="translate(1 1)"/><rect x="224" y="118" width="7" height="74" rx="3.5" fill="#3F4A58"/><rect x="225.3" y="120" width="2" height="70" rx="1" fill="#B8C6D6"/><circle cx="227.5" cy="124" r="3" fill="#6E7B8B"/><circle cx="227.5" cy="186" r="3" fill="#6E7B8B"/><rect x="139" y="84" width="5" height="16" rx="1.5" fill="#4C5766"/><rect x="139" y="150" width="5" height="16" rx="1.5" fill="#4C5766"/><rect x="139" y="216" width="5" height="16" rx="1.5" fill="#4C5766"/><path d="M132 42 H248" stroke="#fff" stroke-width="1.6" opacity=".8"/><rect x="122" y="256" width="136" height="9" rx="2" fill="#5B6877"/><polygon points="258.0,256.0 280.0,243.0 280.0,252.0 258.0,265.0" fill="#46515F"/></svg></div>
        <h3>Doors</h3>
        <p>Strong, smooth-running aluminum and glass doors.</p>
        <span class="svc-go">See doors →</span>
      </a>
      <a class="svc-card" href="{{ url_for("services") }}#partitioning">
        <div class="svc-art svc-art-3"><svg viewBox="0 0 400 300" class="svc-svg" role="img" aria-label="3D glass partition wall"><defs>
<linearGradient id="p-alu" x1="0" y1="0" x2="0" y2="1"><stop offset="0" stop-color="#F6F9FC"/><stop offset=".45" stop-color="#C9D3DE"/><stop offset="1" stop-color="#8E9AA8"/></linearGradient>
<linearGradient id="p-alu-h" x1="0" y1="0" x2="1" y2="0"><stop offset="0" stop-color="#E9EEF4"/><stop offset=".5" stop-color="#BCC7D3"/><stop offset="1" stop-color="#8794A3"/></linearGradient>
<linearGradient id="p-side" x1="0" y1="0" x2="1" y2="0"><stop offset="0" stop-color="#8F9BAA"/><stop offset="1" stop-color="#586474"/></linearGradient>
<linearGradient id="p-top" x1="0" y1="1" x2="0" y2="0"><stop offset="0" stop-color="#CBD5E0"/><stop offset="1" stop-color="#F3F7FB"/></linearGradient>
<linearGradient id="p-glass" x1="0" y1="0" x2="1" y2="1"><stop offset="0" stop-color="#A8EAFF"/><stop offset=".5" stop-color="#43A6DD"/><stop offset="1" stop-color="#1A5E96"/></linearGradient>
<linearGradient id="p-glass2" x1="0" y1="0" x2="0" y2="1"><stop offset="0" stop-color="#9BE6FF" stop-opacity=".9"/><stop offset="1" stop-color="#2A78B4" stop-opacity=".85"/></linearGradient>
<filter id="p-blur" x="-20%" y="-50%" width="140%" height="200%"><feGaussianBlur stdDeviation="7"/></filter>
<linearGradient id="p-floor" x1="0" y1="0" x2="0" y2="1"><stop offset="0" stop-color="#9BE6FF" stop-opacity=".25"/><stop offset="1" stop-color="#9BE6FF" stop-opacity="0"/></linearGradient></defs><polygon points="44.0,252.0 352.0,214.0 366.0,238.0 34.0,286.0" fill="url(#p-floor)"/><ellipse cx="200" cy="262" rx="165" ry="10" fill="#000" opacity=".35" filter="url(#p-blur)"/><polygon points="48.0,50.0 133.4,68.0 133.4,230.6 48.0,242.0" fill="url(#p-glass2)" stroke="#4E6F8E" stroke-width="1"/><polygon points="48.0,130.6 133.4,136.3 133.4,162.3 48.0,161.4" fill="#fff" opacity=".3"/><polygon points="57.9,52.0 82.8,55.4 82.8,236.6 53.2,240.0" fill="#fff" opacity=".22"/><polygon points="140.4,68.0 210.4,83.0 210.4,221.1 140.4,230.6" fill="url(#p-glass2)" stroke="#4E6F8E" stroke-width="1"/><polygon points="140.4,136.3 210.4,141.0 210.4,163.1 140.4,162.3" fill="#fff" opacity=".3"/><polygon points="147.9,70.0 168.7,72.5 168.7,225.8 144.1,228.6" fill="#fff" opacity=".22"/><polygon points="217.4,83.0 278.2,96.2 278.2,212.7 217.4,221.1" fill="url(#p-glass2)" stroke="#4E6F8E" stroke-width="1"/><polygon points="217.4,141.0 278.2,145.1 278.2,163.8 217.4,163.1" fill="#fff" opacity=".3"/><polygon points="223.6,85.0 241.9,87.0 241.9,216.6 220.2,219.1" fill="#fff" opacity=".22"/><polygon points="285.2,96.2 349.0,110.0 349.0,204.0 285.2,212.7" fill="url(#p-glass2)" stroke="#4E6F8E" stroke-width="1"/><polygon points="285.2,145.1 349.0,149.5 349.0,164.5 285.2,163.8" fill="#fff" opacity=".3"/><polygon points="291.8,98.2 310.9,100.3 310.9,208.1 288.2,210.7" fill="#fff" opacity=".22"/><rect x="264.3" y="147.9" width="4.5" height="22.2" rx="2" fill="#3F4A58"/><polygon points="40.5,46.0 47.5,46.0 47.5,246.0 40.5,246.0" fill="url(#p-alu-h)" stroke="#7F8C9B" stroke-width=".8"/><polygon points="133.3,64.0 139.4,64.0 139.4,234.6 133.3,234.6" fill="url(#p-alu-h)" stroke="#7F8C9B" stroke-width=".8"/><polygon points="210.8,79.0 216.0,79.0 216.0,225.1 210.8,225.1" fill="url(#p-alu-h)" stroke="#7F8C9B" stroke-width=".8"/><polygon points="279.0,92.2 283.3,92.2 283.3,216.7 279.0,216.7" fill="url(#p-alu-h)" stroke="#7F8C9B" stroke-width=".8"/><polygon points="350.3,106.0 353.7,106.0 353.7,208.0 350.3,208.0" fill="url(#p-alu-h)" stroke="#7F8C9B" stroke-width=".8"/><polygon points="40.0,36.0 355.0,96.0 355.0,110.0 40.0,50.0" fill="url(#p-alu)" stroke="#7F8C9B" stroke-width="1"/><polygon points="40.0,36.0 52.0,28.0 362.0,88.0 355.0,96.0" fill="url(#p-top)" stroke="#8794A3" stroke-width=".8"/><polygon points="40.0,242.0 355.0,204.0 355.0,218.0 40.0,256.0" fill="url(#p-alu)" stroke="#7F8C9B" stroke-width="1"/><polygon points="355.0,96.0 362.0,88.0 362.0,210.0 355.0,218.0" fill="url(#p-side)"/></svg></div>
        <h3>Partitioning</h3>
        <p>Glass and aluminum partitions for offices and homes.</p>
        <span class="svc-go">See partitioning →</span>
      </a>
      <a class="svc-card" href="{{ url_for('services') }}#curtain-walls">
        <div class="svc-art svc-art-4"><svg viewBox="0 0 400 300" class="svc-svg" role="img" aria-label="3D glass curtain wall building"><defs>
<linearGradient id="c-alu" x1="0" y1="0" x2="0" y2="1"><stop offset="0" stop-color="#F6F9FC"/><stop offset=".45" stop-color="#C9D3DE"/><stop offset="1" stop-color="#8E9AA8"/></linearGradient>
<linearGradient id="c-alu-h" x1="0" y1="0" x2="1" y2="0"><stop offset="0" stop-color="#E9EEF4"/><stop offset=".5" stop-color="#BCC7D3"/><stop offset="1" stop-color="#8794A3"/></linearGradient>
<linearGradient id="c-side" x1="0" y1="0" x2="1" y2="0"><stop offset="0" stop-color="#8F9BAA"/><stop offset="1" stop-color="#586474"/></linearGradient>
<linearGradient id="c-top" x1="0" y1="1" x2="0" y2="0"><stop offset="0" stop-color="#CBD5E0"/><stop offset="1" stop-color="#F3F7FB"/></linearGradient>
<linearGradient id="c-glass" x1="0" y1="0" x2="1" y2="1"><stop offset="0" stop-color="#A8EAFF"/><stop offset=".5" stop-color="#43A6DD"/><stop offset="1" stop-color="#1A5E96"/></linearGradient>
<linearGradient id="c-glass2" x1="0" y1="0" x2="0" y2="1"><stop offset="0" stop-color="#9BE6FF" stop-opacity=".9"/><stop offset="1" stop-color="#2A78B4" stop-opacity=".85"/></linearGradient>
<filter id="c-blur" x="-20%" y="-50%" width="140%" height="200%"><feGaussianBlur stdDeviation="7"/></filter>
<linearGradient id="c-sky" x1="0" y1="0" x2="1" y2="1"><stop offset="0" stop-color="#BDF0FF"/><stop offset=".5" stop-color="#58B4E8"/><stop offset="1" stop-color="#1E67A3"/></linearGradient><linearGradient id="c-sky2" x1="0" y1="0" x2="1" y2="1"><stop offset="0" stop-color="#4C9CD3"/><stop offset=".6" stop-color="#1E5C93"/><stop offset="1" stop-color="#103B66"/></linearGradient></defs><ellipse cx="205" cy="270" rx="150" ry="10" fill="#000" opacity=".45" filter="url(#c-blur)"/><polygon points="40.0,78.0 208.0,34.0 208.0,258.0 40.0,226.0" fill="url(#c-sky)" stroke="#2F5F8C" stroke-width="1.2"/><polygon points="40.0,78.0 73.6,69.2 73.6,92.5 40.0,99.1" fill="#fff" opacity="0.10"/><polygon points="40.0,162.6 73.6,162.5 73.6,185.8 40.0,183.7" fill="#fff" opacity="0.10"/><polygon points="40.0,183.7 73.6,185.8 73.6,209.1 40.0,204.9" fill="#fff" opacity="0.10"/><polygon points="73.6,69.2 107.2,60.4 107.2,85.9 73.6,92.5" fill="#fff" opacity="0.10"/><polygon points="73.6,92.5 107.2,85.9 107.2,111.4 73.6,115.8" fill="#fff" opacity="0.10"/><polygon points="73.6,185.8 107.2,187.8 107.2,213.3 73.6,209.1" fill="#fff" opacity="0.10"/><polygon points="73.6,209.1 107.2,213.3 107.2,238.8 73.6,232.4" fill="#fff" opacity="0.10"/><polygon points="107.2,85.9 140.8,79.3 140.8,106.9 107.2,111.4" fill="#fff" opacity="0.10"/><polygon points="107.2,111.4 140.8,106.9 140.8,134.6 107.2,136.9" fill="#fff" opacity="0.10"/><polygon points="107.2,213.3 140.8,217.5 140.8,245.2 107.2,238.8" fill="#fff" opacity="0.10"/><polygon points="140.8,106.9 174.4,102.5 174.4,132.3 140.8,134.6" fill="#fff" opacity="0.10"/><polygon points="140.8,134.6 174.4,132.3 174.4,162.1 140.8,162.2" fill="#fff" opacity="0.10"/><polygon points="174.4,132.3 208.0,130.0 208.0,162.0 174.4,162.1" fill="#fff" opacity="0.10"/><polygon points="174.4,162.1 208.0,162.0 208.0,194.0 174.4,191.9" fill="#fff" opacity="0.10"/><line x1="40.0" y1="99.1" x2="208.0" y2="66.0" stroke="#DCE5EE" stroke-width="2.2"/><line x1="40.0" y1="100.7" x2="208.0" y2="67.6" stroke="#5C6B7C" stroke-width="1"/><line x1="40.0" y1="120.3" x2="208.0" y2="98.0" stroke="#DCE5EE" stroke-width="2.2"/><line x1="40.0" y1="121.9" x2="208.0" y2="99.6" stroke="#5C6B7C" stroke-width="1"/><line x1="40.0" y1="141.4" x2="208.0" y2="130.0" stroke="#DCE5EE" stroke-width="2.2"/><line x1="40.0" y1="143.0" x2="208.0" y2="131.6" stroke="#5C6B7C" stroke-width="1"/><line x1="40.0" y1="162.6" x2="208.0" y2="162.0" stroke="#DCE5EE" stroke-width="2.2"/><line x1="40.0" y1="164.2" x2="208.0" y2="163.6" stroke="#5C6B7C" stroke-width="1"/><line x1="40.0" y1="183.7" x2="208.0" y2="194.0" stroke="#DCE5EE" stroke-width="2.2"/><line x1="40.0" y1="185.3" x2="208.0" y2="195.6" stroke="#5C6B7C" stroke-width="1"/><line x1="40.0" y1="204.9" x2="208.0" y2="226.0" stroke="#DCE5EE" stroke-width="2.2"/><line x1="40.0" y1="206.5" x2="208.0" y2="227.6" stroke="#5C6B7C" stroke-width="1"/><line x1="73.6" y1="69.2" x2="73.6" y2="232.4" stroke="#DCE5EE" stroke-width="2.2"/><line x1="107.2" y1="60.4" x2="107.2" y2="238.8" stroke="#DCE5EE" stroke-width="2.2"/><line x1="140.8" y1="51.6" x2="140.8" y2="245.2" stroke="#DCE5EE" stroke-width="2.2"/><line x1="174.4" y1="42.8" x2="174.4" y2="251.6" stroke="#DCE5EE" stroke-width="2.2"/><polygon points="368.0,92.0 208.0,34.0 208.0,258.0 368.0,214.0" fill="url(#c-sky2)" stroke="#2F5F8C" stroke-width="1.2"/><polygon points="368.0,92.0 314.7,72.7 314.7,95.0 368.0,109.4" fill="#fff" opacity="0.16"/><polygon points="368.0,161.7 314.7,161.8 314.7,184.1 368.0,179.1" fill="#fff" opacity="0.16"/><polygon points="368.0,179.1 314.7,184.1 314.7,206.4 368.0,196.6" fill="#fff" opacity="0.16"/><polygon points="314.7,72.7 261.3,53.3 261.3,80.5 314.7,95.0" fill="#fff" opacity="0.16"/><polygon points="314.7,95.0 261.3,80.5 261.3,107.6 314.7,117.2" fill="#fff" opacity="0.16"/><polygon points="314.7,184.1 261.3,189.0 261.3,216.2 314.7,206.4" fill="#fff" opacity="0.16"/><polygon points="314.7,206.4 261.3,216.2 261.3,243.3 314.7,228.7" fill="#fff" opacity="0.16"/><polygon points="261.3,80.5 208.0,66.0 208.0,98.0 261.3,107.6" fill="#fff" opacity="0.16"/><polygon points="261.3,107.6 208.0,98.0 208.0,130.0 261.3,134.8" fill="#fff" opacity="0.16"/><polygon points="261.3,216.2 208.0,226.0 208.0,258.0 261.3,243.3" fill="#fff" opacity="0.16"/><line x1="368.0" y1="109.4" x2="208.0" y2="66.0" stroke="#DCE5EE" stroke-width="2.2"/><line x1="368.0" y1="111.0" x2="208.0" y2="67.6" stroke="#5C6B7C" stroke-width="1"/><line x1="368.0" y1="126.9" x2="208.0" y2="98.0" stroke="#DCE5EE" stroke-width="2.2"/><line x1="368.0" y1="128.5" x2="208.0" y2="99.6" stroke="#5C6B7C" stroke-width="1"/><line x1="368.0" y1="144.3" x2="208.0" y2="130.0" stroke="#DCE5EE" stroke-width="2.2"/><line x1="368.0" y1="145.9" x2="208.0" y2="131.6" stroke="#5C6B7C" stroke-width="1"/><line x1="368.0" y1="161.7" x2="208.0" y2="162.0" stroke="#DCE5EE" stroke-width="2.2"/><line x1="368.0" y1="163.3" x2="208.0" y2="163.6" stroke="#5C6B7C" stroke-width="1"/><line x1="368.0" y1="179.1" x2="208.0" y2="194.0" stroke="#DCE5EE" stroke-width="2.2"/><line x1="368.0" y1="180.7" x2="208.0" y2="195.6" stroke="#5C6B7C" stroke-width="1"/><line x1="368.0" y1="196.6" x2="208.0" y2="226.0" stroke="#DCE5EE" stroke-width="2.2"/><line x1="368.0" y1="198.2" x2="208.0" y2="227.6" stroke="#5C6B7C" stroke-width="1"/><line x1="314.7" y1="72.7" x2="314.7" y2="228.7" stroke="#DCE5EE" stroke-width="2.2"/><line x1="261.3" y1="53.3" x2="261.3" y2="243.3" stroke="#DCE5EE" stroke-width="2.2"/><polygon points="204.5,34.0 211.5,34.0 211.5,258.0 204.5,258.0" fill="url(#c-alu-h)" stroke="#7F8C9B" stroke-width=".8"/><polygon points="37.0,72.0 208.0,26.0 371.0,86.0 371.0,93.0 208.0,35.0 37.0,79.0" fill="url(#c-alu)" stroke="#7F8C9B" stroke-width="1"/><polygon points="37.0,72.0 208.0,26.0 371.0,86.0 208.0,18.0" fill="url(#c-top)" stroke="#8794A3" stroke-width=".8"/><polygon points="37.0,226.0 208.0,258.0 371.0,214.0 371.0,221.0 208.0,266.0 37.0,233.0" fill="url(#c-side)"/><g class="svc-twinkle"><path d="M300 120 L304 130 L314 134 L304 138 L300 148 L296 138 L286 134 L296 130 Z" fill="#fff" opacity=".9"/></g></svg></div>
        <h3>Curtain Walls</h3>
        <p>Sleek glass facades for modern buildings.</p>
        <span class="svc-go">See examples →</span>
      </a>
      <a class="svc-card" href="{{ url_for('services') }}#maintenance">
        <div class="svc-art svc-art-5"><svg viewBox="0 0 400 300" class="svc-svg" role="img" aria-label="3D wrench and gear for maintenance"><defs><radialGradient id="m-gear" cx=".35" cy=".3" r=".9"><stop offset="0" stop-color="#F8FBFE"/><stop offset=".5" stop-color="#B9C5D2"/><stop offset="1" stop-color="#6D7A8A"/></radialGradient><linearGradient id="m-steel" x1="0" y1="0" x2="0" y2="1"><stop offset="0" stop-color="#F4F8FC"/><stop offset=".45" stop-color="#BAC6D3"/><stop offset="1" stop-color="#6F7D8D"/></linearGradient><linearGradient id="m-green" x1="0" y1="0" x2="1" y2="1"><stop offset="0" stop-color="#6EF0A6"/><stop offset="1" stop-color="#14934A"/></linearGradient><filter id="m-blur" x="-20%" y="-50%" width="140%" height="200%"><feGaussianBlur stdDeviation="7"/></filter><mask id="m-jaw" maskUnits="userSpaceOnUse" x="-140" y="-140" width="360" height="360"><rect x="-140" y="-140" width="360" height="360" fill="#fff"/><rect x="-13" y="-72" width="26" height="54" rx="3" fill="#000"/></mask></defs><ellipse cx="200" cy="270" rx="150" ry="11" fill="#000" opacity=".5" filter="url(#m-blur)"/><path d="M201.8,155.3 L217.8,165.3 L212.5,188.8 L193.8,190.9 L192.8,192.6 L199.8,210.0 L181.7,225.9 L165.3,216.6 L163.5,217.4 L159.0,235.6 L135.0,237.8 L127.2,220.7 L125.3,220.2 L110.9,232.4 L90.2,220.0 L94.0,201.6 L92.7,200.1 L73.9,201.5 L64.4,179.3 L78.4,166.6 L78.2,164.7 L62.2,154.7 L67.5,131.2 L86.2,129.1 L87.2,127.4 L80.2,110.0 L98.3,94.1 L114.7,103.4 L116.5,102.6 L121.0,84.4 L145.0,82.2 L152.8,99.3 L154.7,99.8 L169.1,87.6 L189.8,100.0 L186.0,118.4 L187.3,119.9 L206.1,118.5 L215.6,140.7 L201.6,153.4 Z M166,160 A26,26 0 1,0 114,160 A26,26 0 1,0 166,160 Z" transform="translate(9.0 11.0)" fill="#4A5666" fill-rule="evenodd"/><path d="M201.8,155.3 L217.8,165.3 L212.5,188.8 L193.8,190.9 L192.8,192.6 L199.8,210.0 L181.7,225.9 L165.3,216.6 L163.5,217.4 L159.0,235.6 L135.0,237.8 L127.2,220.7 L125.3,220.2 L110.9,232.4 L90.2,220.0 L94.0,201.6 L92.7,200.1 L73.9,201.5 L64.4,179.3 L78.4,166.6 L78.2,164.7 L62.2,154.7 L67.5,131.2 L86.2,129.1 L87.2,127.4 L80.2,110.0 L98.3,94.1 L114.7,103.4 L116.5,102.6 L121.0,84.4 L145.0,82.2 L152.8,99.3 L154.7,99.8 L169.1,87.6 L189.8,100.0 L186.0,118.4 L187.3,119.9 L206.1,118.5 L215.6,140.7 L201.6,153.4 Z M166,160 A26,26 0 1,0 114,160 A26,26 0 1,0 166,160 Z" transform="translate(8.1 9.9)" fill="#4A5666" fill-rule="evenodd"/><path d="M201.8,155.3 L217.8,165.3 L212.5,188.8 L193.8,190.9 L192.8,192.6 L199.8,210.0 L181.7,225.9 L165.3,216.6 L163.5,217.4 L159.0,235.6 L135.0,237.8 L127.2,220.7 L125.3,220.2 L110.9,232.4 L90.2,220.0 L94.0,201.6 L92.7,200.1 L73.9,201.5 L64.4,179.3 L78.4,166.6 L78.2,164.7 L62.2,154.7 L67.5,131.2 L86.2,129.1 L87.2,127.4 L80.2,110.0 L98.3,94.1 L114.7,103.4 L116.5,102.6 L121.0,84.4 L145.0,82.2 L152.8,99.3 L154.7,99.8 L169.1,87.6 L189.8,100.0 L186.0,118.4 L187.3,119.9 L206.1,118.5 L215.6,140.7 L201.6,153.4 Z M166,160 A26,26 0 1,0 114,160 A26,26 0 1,0 166,160 Z" transform="translate(7.2 8.8)" fill="#4A5666" fill-rule="evenodd"/><path d="M201.8,155.3 L217.8,165.3 L212.5,188.8 L193.8,190.9 L192.8,192.6 L199.8,210.0 L181.7,225.9 L165.3,216.6 L163.5,217.4 L159.0,235.6 L135.0,237.8 L127.2,220.7 L125.3,220.2 L110.9,232.4 L90.2,220.0 L94.0,201.6 L92.7,200.1 L73.9,201.5 L64.4,179.3 L78.4,166.6 L78.2,164.7 L62.2,154.7 L67.5,131.2 L86.2,129.1 L87.2,127.4 L80.2,110.0 L98.3,94.1 L114.7,103.4 L116.5,102.6 L121.0,84.4 L145.0,82.2 L152.8,99.3 L154.7,99.8 L169.1,87.6 L189.8,100.0 L186.0,118.4 L187.3,119.9 L206.1,118.5 L215.6,140.7 L201.6,153.4 Z M166,160 A26,26 0 1,0 114,160 A26,26 0 1,0 166,160 Z" transform="translate(6.3 7.7)" fill="#4A5666" fill-rule="evenodd"/><path d="M201.8,155.3 L217.8,165.3 L212.5,188.8 L193.8,190.9 L192.8,192.6 L199.8,210.0 L181.7,225.9 L165.3,216.6 L163.5,217.4 L159.0,235.6 L135.0,237.8 L127.2,220.7 L125.3,220.2 L110.9,232.4 L90.2,220.0 L94.0,201.6 L92.7,200.1 L73.9,201.5 L64.4,179.3 L78.4,166.6 L78.2,164.7 L62.2,154.7 L67.5,131.2 L86.2,129.1 L87.2,127.4 L80.2,110.0 L98.3,94.1 L114.7,103.4 L116.5,102.6 L121.0,84.4 L145.0,82.2 L152.8,99.3 L154.7,99.8 L169.1,87.6 L189.8,100.0 L186.0,118.4 L187.3,119.9 L206.1,118.5 L215.6,140.7 L201.6,153.4 Z M166,160 A26,26 0 1,0 114,160 A26,26 0 1,0 166,160 Z" transform="translate(5.4 6.6)" fill="#4A5666" fill-rule="evenodd"/><path d="M201.8,155.3 L217.8,165.3 L212.5,188.8 L193.8,190.9 L192.8,192.6 L199.8,210.0 L181.7,225.9 L165.3,216.6 L163.5,217.4 L159.0,235.6 L135.0,237.8 L127.2,220.7 L125.3,220.2 L110.9,232.4 L90.2,220.0 L94.0,201.6 L92.7,200.1 L73.9,201.5 L64.4,179.3 L78.4,166.6 L78.2,164.7 L62.2,154.7 L67.5,131.2 L86.2,129.1 L87.2,127.4 L80.2,110.0 L98.3,94.1 L114.7,103.4 L116.5,102.6 L121.0,84.4 L145.0,82.2 L152.8,99.3 L154.7,99.8 L169.1,87.6 L189.8,100.0 L186.0,118.4 L187.3,119.9 L206.1,118.5 L215.6,140.7 L201.6,153.4 Z M166,160 A26,26 0 1,0 114,160 A26,26 0 1,0 166,160 Z" transform="translate(4.5 5.5)" fill="#4A5666" fill-rule="evenodd"/><path d="M201.8,155.3 L217.8,165.3 L212.5,188.8 L193.8,190.9 L192.8,192.6 L199.8,210.0 L181.7,225.9 L165.3,216.6 L163.5,217.4 L159.0,235.6 L135.0,237.8 L127.2,220.7 L125.3,220.2 L110.9,232.4 L90.2,220.0 L94.0,201.6 L92.7,200.1 L73.9,201.5 L64.4,179.3 L78.4,166.6 L78.2,164.7 L62.2,154.7 L67.5,131.2 L86.2,129.1 L87.2,127.4 L80.2,110.0 L98.3,94.1 L114.7,103.4 L116.5,102.6 L121.0,84.4 L145.0,82.2 L152.8,99.3 L154.7,99.8 L169.1,87.6 L189.8,100.0 L186.0,118.4 L187.3,119.9 L206.1,118.5 L215.6,140.7 L201.6,153.4 Z M166,160 A26,26 0 1,0 114,160 A26,26 0 1,0 166,160 Z" transform="translate(3.6 4.4)" fill="#4A5666" fill-rule="evenodd"/><path d="M201.8,155.3 L217.8,165.3 L212.5,188.8 L193.8,190.9 L192.8,192.6 L199.8,210.0 L181.7,225.9 L165.3,216.6 L163.5,217.4 L159.0,235.6 L135.0,237.8 L127.2,220.7 L125.3,220.2 L110.9,232.4 L90.2,220.0 L94.0,201.6 L92.7,200.1 L73.9,201.5 L64.4,179.3 L78.4,166.6 L78.2,164.7 L62.2,154.7 L67.5,131.2 L86.2,129.1 L87.2,127.4 L80.2,110.0 L98.3,94.1 L114.7,103.4 L116.5,102.6 L121.0,84.4 L145.0,82.2 L152.8,99.3 L154.7,99.8 L169.1,87.6 L189.8,100.0 L186.0,118.4 L187.3,119.9 L206.1,118.5 L215.6,140.7 L201.6,153.4 Z M166,160 A26,26 0 1,0 114,160 A26,26 0 1,0 166,160 Z" transform="translate(2.7 3.3)" fill="#4A5666" fill-rule="evenodd"/><path d="M201.8,155.3 L217.8,165.3 L212.5,188.8 L193.8,190.9 L192.8,192.6 L199.8,210.0 L181.7,225.9 L165.3,216.6 L163.5,217.4 L159.0,235.6 L135.0,237.8 L127.2,220.7 L125.3,220.2 L110.9,232.4 L90.2,220.0 L94.0,201.6 L92.7,200.1 L73.9,201.5 L64.4,179.3 L78.4,166.6 L78.2,164.7 L62.2,154.7 L67.5,131.2 L86.2,129.1 L87.2,127.4 L80.2,110.0 L98.3,94.1 L114.7,103.4 L116.5,102.6 L121.0,84.4 L145.0,82.2 L152.8,99.3 L154.7,99.8 L169.1,87.6 L189.8,100.0 L186.0,118.4 L187.3,119.9 L206.1,118.5 L215.6,140.7 L201.6,153.4 Z M166,160 A26,26 0 1,0 114,160 A26,26 0 1,0 166,160 Z" transform="translate(1.8 2.2)" fill="#4A5666" fill-rule="evenodd"/><path d="M201.8,155.3 L217.8,165.3 L212.5,188.8 L193.8,190.9 L192.8,192.6 L199.8,210.0 L181.7,225.9 L165.3,216.6 L163.5,217.4 L159.0,235.6 L135.0,237.8 L127.2,220.7 L125.3,220.2 L110.9,232.4 L90.2,220.0 L94.0,201.6 L92.7,200.1 L73.9,201.5 L64.4,179.3 L78.4,166.6 L78.2,164.7 L62.2,154.7 L67.5,131.2 L86.2,129.1 L87.2,127.4 L80.2,110.0 L98.3,94.1 L114.7,103.4 L116.5,102.6 L121.0,84.4 L145.0,82.2 L152.8,99.3 L154.7,99.8 L169.1,87.6 L189.8,100.0 L186.0,118.4 L187.3,119.9 L206.1,118.5 L215.6,140.7 L201.6,153.4 Z M166,160 A26,26 0 1,0 114,160 A26,26 0 1,0 166,160 Z" transform="translate(0.9 1.1)" fill="#4A5666" fill-rule="evenodd"/><path d="M201.8,155.3 L217.8,165.3 L212.5,188.8 L193.8,190.9 L192.8,192.6 L199.8,210.0 L181.7,225.9 L165.3,216.6 L163.5,217.4 L159.0,235.6 L135.0,237.8 L127.2,220.7 L125.3,220.2 L110.9,232.4 L90.2,220.0 L94.0,201.6 L92.7,200.1 L73.9,201.5 L64.4,179.3 L78.4,166.6 L78.2,164.7 L62.2,154.7 L67.5,131.2 L86.2,129.1 L87.2,127.4 L80.2,110.0 L98.3,94.1 L114.7,103.4 L116.5,102.6 L121.0,84.4 L145.0,82.2 L152.8,99.3 L154.7,99.8 L169.1,87.6 L189.8,100.0 L186.0,118.4 L187.3,119.9 L206.1,118.5 L215.6,140.7 L201.6,153.4 Z M166,160 A26,26 0 1,0 114,160 A26,26 0 1,0 166,160 Z" fill="url(#m-gear)" fill-rule="evenodd" stroke="#5B6879" stroke-width="1.2"/><circle cx="140" cy="160" r="46" fill="none" stroke="#fff" stroke-opacity=".5" stroke-width="2"/><circle cx="140" cy="160" r="26" fill="#1E2733"/><circle cx="140" cy="160" r="26" fill="none" stroke="#9AA8B8" stroke-width="2"/><path d="M96 132 A52 52 0 0 1 150 108" stroke="#fff" stroke-opacity=".7" stroke-width="3" fill="none" stroke-linecap="round"/><g transform="translate(262 150) rotate(-42)"><g fill="#3E4958" mask="url(#m-jaw)"><g transform="translate(7.2 9.0)"><circle cx="0" cy="-8" r="40"/></g><g transform="translate(6.4 8.0)"><circle cx="0" cy="-8" r="40"/></g><g transform="translate(5.6 7.0)"><circle cx="0" cy="-8" r="40"/></g><g transform="translate(4.8 6.0)"><circle cx="0" cy="-8" r="40"/></g><g transform="translate(4.0 5.0)"><circle cx="0" cy="-8" r="40"/></g><g transform="translate(3.2 4.0)"><circle cx="0" cy="-8" r="40"/></g><g transform="translate(2.4 3.0)"><circle cx="0" cy="-8" r="40"/></g><g transform="translate(1.6 2.0)"><circle cx="0" cy="-8" r="40"/></g><g transform="translate(0.8 1.0)"><circle cx="0" cy="-8" r="40"/></g></g><g fill="#3E4958"><g transform="translate(7.2 9.0)"><rect x="-14" y="10" width="28" height="170" rx="14"/></g><g transform="translate(6.4 8.0)"><rect x="-14" y="10" width="28" height="170" rx="14"/></g><g transform="translate(5.6 7.0)"><rect x="-14" y="10" width="28" height="170" rx="14"/></g><g transform="translate(4.8 6.0)"><rect x="-14" y="10" width="28" height="170" rx="14"/></g><g transform="translate(4.0 5.0)"><rect x="-14" y="10" width="28" height="170" rx="14"/></g><g transform="translate(3.2 4.0)"><rect x="-14" y="10" width="28" height="170" rx="14"/></g><g transform="translate(2.4 3.0)"><rect x="-14" y="10" width="28" height="170" rx="14"/></g><g transform="translate(1.6 2.0)"><rect x="-14" y="10" width="28" height="170" rx="14"/></g><g transform="translate(0.8 1.0)"><rect x="-14" y="10" width="28" height="170" rx="14"/></g></g><rect x="-14" y="10" width="28" height="170" rx="14" fill="url(#m-steel)" stroke="#667385" stroke-width="1.2"/><g mask="url(#m-jaw)"><circle cx="0" cy="-8" r="40" fill="url(#m-steel)" stroke="#667385" stroke-width="1.2"/></g><rect x="-14" y="-52" width="28" height="42" rx="3" fill="#10161F" opacity=".0"/><rect x="-6" y="40" width="4" height="120" rx="2" fill="#fff" opacity=".7"/><circle cx="0" cy="164" r="6" fill="#4A5666"/><circle cx="0" cy="164" r="6" fill="none" stroke="#C9D3DE"/></g><polygon points="361.1,87.0 342.0,98.0 322.9,87.0 322.9,65.0 342.0,54.0 361.1,65.0" fill="#3E4958"/><polygon points="357.1,81.0 338.0,92.0 318.9,81.0 318.9,59.0 338.0,48.0 357.1,59.0" fill="url(#m-green)" stroke="#0D6B33" stroke-width="1.2"/><circle cx="338" cy="70" r="9" fill="#12331F"/><circle cx="338" cy="70" r="9" fill="none" stroke="#8BF5B8"/><g class="svc-twinkle" style="animation-delay:0s"><path transform="translate(300 28) scale(0.9)" d="M0 -12 L3 -3 L12 0 L3 3 L0 12 L-3 3 L-12 0 L-3 -3 Z" fill="#7CF5B0"/></g><g class="svc-twinkle" style="animation-delay:0.8s"><path transform="translate(84 62) scale(0.7)" d="M0 -12 L3 -3 L12 0 L3 3 L0 12 L-3 3 L-12 0 L-3 -3 Z" fill="#7CF5B0"/></g><g class="svc-twinkle" style="animation-delay:1.4s"><path transform="translate(372 140) scale(0.6)" d="M0 -12 L3 -3 L12 0 L3 3 L0 12 L-3 3 L-12 0 L-3 -3 Z" fill="#7CF5B0"/></g></svg></div>
        <h3>Maintenance</h3>
        <p>Repairs, servicing and quick fixes.</p>
        <span class="svc-go">See examples →</span>
      </a>
    </div>
    <button class="carousel-btn prev" type="button" aria-label="Previous service">‹</button>
    <button class="carousel-btn next" type="button" aria-label="Next service">›</button>
    <div class="carousel-dots" aria-hidden="true"></div>
  </div>
  <div class="svc-all"><a class="btn btn-purple" href="{{ url_for('services') }}">Explore all services →</a></div>

  {% if featured %}
  <div class="lp-subhead reveal"><h3>From the catalogue</h3><a href="{{ url_for('catalog') }}">View all →</a></div>
  <div class="carousel carousel-mini" data-carousel role="region" aria-roledescription="carousel" aria-label="Featured products">
    <div class="carousel-track" tabindex="0">
      {% for p in featured %}
      <a class="pcard-mini" href="{{ url_for('catalog', cat=p.category) }}">
        {% if p.image_filename %}{% set pu = p.image_filename|photo_url("products") %}
        <div class="pimg" style="--bg:url('{{ pu }}');"><img src="{{ pu }}" alt="{{ p.name }}" loading="lazy"></div>
        {% else %}<div class="pimg pimg-art">{{ category_graphic(p.category)|safe }}</div>{% endif %}
        <div class="pm-name">{{ p.name }}</div>
        <div class="pm-price">{% if p.price > 0 %}₦{{ "{:,}".format(p.price) }}{% else %}Ask for a quote{% endif %}</div>
      </a>
      {% endfor %}
    </div>
    <button class="carousel-btn prev" type="button" aria-label="Previous product">‹</button>
    <button class="carousel-btn next" type="button" aria-label="Next product">›</button>
  </div>
  {% endif %}
</section>

<section class="lp-section" id="how-it-works">
  <div class="lp-head reveal"><span class="lp-eyebrow">How it works</span><h2 class="lp-title">Three simple steps</h2></div>
  <ol class="steps3">
    <li class="step3 reveal" style="--d:0ms"><span class="step3-num">1</span><div><h3>Request a service</h3><p>Tell Andy what you need. Add photos or files if they help.</p></div></li>
    <li class="step3 reveal" style="--d:100ms"><span class="step3-num">2</span><div><h3>Get connected</h3><p>Andy assigns one of its artisans to your job and agrees the details with you in chat.</p></div></li>
    <li class="step3 reveal" style="--d:200ms"><span class="step3-num">3</span><div><h3>Arrange the work</h3><p>Confirm the plan and pay Andy. Your artisan does the job and is paid after it is done.</p></div></li>
  </ol>
  <p class="steps-note reveal">Larger projects can be directed to EAS where appropriate.</p>
</section>

<section class="lp-section" id="why-andy">
  <div class="lp-head reveal"><span class="lp-eyebrow">Why Andy</span><h2 class="lp-title">Why choose Andy</h2></div>
  <div class="why-grid">
    <div class="why-item reveal" style="--d:0ms"><span class="why-ico">🧰</span><div><h3>Our own artisans</h3><p>Aluminum (alloy) fabricators who work as Andy staff.</p></div></div>
    <div class="why-item reveal" style="--d:80ms"><span class="why-ico">💬</span><div><h3>One place for the job</h3><p>Request, chat with Andy and follow the status in the app.</p></div></div>
    <div class="why-item reveal" style="--d:160ms"><span class="why-ico">🔒</span><div><h3>Pay Andy, not the artisan</h3><p>Your artisan is paid after the job is done.</p></div></div>
    <div class="why-item reveal" style="--d:240ms"><span class="why-ico">📸</span><div><h3>See finished work</h3><p>Browse photos and videos of completed jobs, with reviews.</p></div></div>
  </div>
</section>

<section class="lp-section" id="about">
  {% include "_about_section.html" %}
</section>

<section class="lp-section" id="contact">
  <div class="lp-contact reveal">
    <h2 class="lp-title">Ready to get started?</h2>
    <p class="lp-lead">Tell Andy what you need and we will take it from there.</p>
    {% if not user %}
    <div class="lp-cta-row">
      <button class="btn btn-purple" onclick="document.getElementById('authModal').classList.add('open')">Request a Service</button>
      <button class="btn btn-outline" onclick="document.getElementById('authModal').classList.add('open');showStep('loginForm')">Login</button>
    </div>
    <p class="terms-note" style="text-align:center;margin-top:14px;">Terms and conditions apply. <a href="{{ url_for('terms') }}">Terms &amp; Conditions</a> · <a href="{{ url_for('privacy') }}">Privacy Policy</a></p>
    {% elif user.role == 'customer' %}
    <div class="lp-cta-row"><a class="btn btn-purple" href="{{ url_for('request_service') }}">Request a Service</a></div>
    {% endif %}
    {% if contact.phone or contact.whatsapp or contact.email or contact.address %}
    <div class="lp-contact-list">
      {% if contact.phone %}<a href="tel:{{ contact.phone }}">📞 {{ contact.phone }}</a>{% endif %}
      {% if contact.whatsapp %}<a href="https://wa.me/{{ contact.whatsapp }}" target="_blank" rel="noopener">💬 WhatsApp us</a>{% endif %}
      {% if contact.email %}<a href="mailto:{{ contact.email }}">✉️ {{ contact.email }}</a>{% endif %}
      {% if contact.address %}<span>📍 {{ contact.address }}</span>{% endif %}
    </div>
    {% endif %}
  </div>
</section>

{% endblock %}
''',

"_about_section.html": '''<div class="about-grid">
  <div class="about-text">
    <div class="lp-head reveal">
      <span class="lp-eyebrow">About</span>
      <h2 class="lp-title">About Andy</h2>
      <p class="lp-lead">{% if site.about_text %}{{ site.about_text }}{% else %}Andy is an aluminum (alloy) service company. We make it easy to get windows, doors, partitions and curtain walls made, fitted and repaired by our own team of artisans.{% endif %}</p>
    </div>
    <div class="about-points">
      <div class="about-point reveal" style="--d:0ms"><span class="ap-ico">🎯</span><div><h3>Our purpose</h3><p>To make aluminum work simple: one place to ask, agree and follow the job.</p></div></div>
      <div class="about-point reveal" style="--d:80ms"><span class="ap-ico">🧩</span><div><h3>The problem we solve</h3><p>Finding a reliable fabricator, agreeing a clear price and knowing how the job is going can be hard. Andy keeps it all in one chat.</p></div></div>
      <div class="about-point reveal" style="--d:160ms"><span class="ap-ico">✅</span><div><h3>What you get</h3>
        <ul>
          <li>An Andy artisan assigned to your job</li>
          <li>Photo requests and in-app chat</li>
          <li>A phone measuring tool for quick size estimates (always confirm with a tape measure)</li>
          <li>One payment to Andy, with the artisan paid after the job</li>
        </ul></div></div>
    </div>
    <a class="btn btn-outline about-link" href="{{ url_for('works') }}">See our work →</a>
  </div>

  <div class="about-media reveal">
    <div class="carousel carousel-hero" data-carousel role="region" aria-roledescription="carousel" aria-label="Andy at work">
      <div class="carousel-track" tabindex="0">
        {% for sl in about_slides %}
        <figure class="slide" role="group" aria-roledescription="slide" aria-label="{{ loop.index }} of {{ about_slides|length }}">
          <div class="slide-img" style="--bg:url('{{ sl.src }}');"><img src="{{ sl.src }}" alt="{{ sl.alt }}" {{ 'loading="lazy"' if not loop.first }}></div>
          <figcaption>{{ sl.caption }}{% if sl.illustration %}<span class="slide-tag">Illustration</span>{% endif %}</figcaption>
        </figure>
        {% endfor %}
      </div>
      <button class="carousel-btn prev" type="button" aria-label="Previous image">‹</button>
      <button class="carousel-btn next" type="button" aria-label="Next image">›</button>
      <div class="carousel-dots" aria-hidden="true"></div>
    </div>
  </div>
</div>
''',

"about.html": '''{% extends "base.html" %}
{% block content %}
<section class="lp-section" id="about" style="padding-top:8px;">
  {% include "_about_section.html" %}
</section>
{% endblock %}
''',

"request_service.html": '''{% extends "base.html" %}
{% block title %}Request a Service | ANDY{% endblock %}
{% block content %}
<div class="rq-chat" id="rq">
  <div class="rq-head">
    <div class="rq-avatar" aria-hidden="true">A</div>
    <div><div class="rq-name">Andy</div><div class="rq-status"><span class="rq-dot"></span>Service desk</div></div>
  </div>
  <div class="rq-body" id="rqBody" role="log" aria-live="polite" aria-label="Conversation with Andy"></div>
  <div class="rq-quick" id="rqQuick"></div>
  <form class="rq-composer" id="rqComposer" autocomplete="off">
    <button type="button" class="rq-attach" id="rqAttach" aria-label="Attach photos or files" disabled>📎</button>
    <textarea id="rqInput" rows="1" maxlength="3000" placeholder="Choose an option above…" aria-label="Your message" disabled></textarea>
    <button type="submit" class="rq-send" id="rqSend" aria-label="Send message" disabled>➤</button>
  </form>
</div>

<form id="rqForm" method="POST" action="{{ url_for('request_service') }}" enctype="multipart/form-data" hidden>
  <input type="hidden" name="csrf_token" value="{{ csrf_token() }}">
  <input type="hidden" name="title" id="rqTitle"><input type="hidden" name="category" id="rqCategory"><input type="hidden" name="description" id="rqDesc">
  <input type="file" name="attachments" id="rqFiles" multiple>
</form>

<noscript>
  <form method="POST" action="{{ url_for('request_service') }}" enctype="multipart/form-data" class="auth-form post-composer"><input type="hidden" name="csrf_token" value="{{ csrf_token() }}">
    <input type="text" name="title" placeholder="Short title" required>
    <select name="category">{% for c in categories %}<option value="{{ c }}">{{ c }}</option>{% endfor %}</select>
    <textarea name="description" rows="4" placeholder="Describe what you need" required></textarea>
    <input type="file" name="attachments" multiple>
    <button class="btn btn-purple" type="submit">Send request</button>
  </form>
</noscript>

<script>
(function() {
  var CHIPS = {{ chips|tojson }};
  var FIRST = {{ first_name|tojson }};
  var PRE = {{ prefill|tojson }};
  var PRE_LABEL = {{ prefill_label|tojson }};
  var body = document.getElementById('rqBody'), quick = document.getElementById('rqQuick');
  var input = document.getElementById('rqInput'), sendBtn = document.getElementById('rqSend'), attach = document.getElementById('rqAttach');
  var composer = document.getElementById('rqComposer'), files = document.getElementById('rqFiles'), form = document.getElementById('rqForm');
  var st = { step: 'category', category: '', label: '', desc: '' };

  function esc(t) { var d = document.createElement('div'); d.textContent = t; return d.innerHTML; }
  function down() { body.scrollTop = body.scrollHeight; }
  function bubble(who, html) {
    var d = document.createElement('div'); d.className = 'rq-msg ' + who;
    d.innerHTML = (who === 'andy' ? '<span class="rq-av" aria-hidden="true">A</span>' : '') + '<div class="rq-bub">' + html + '</div>';
    body.appendChild(d); down(); return d;
  }
  function typing(cb, ms) {
    var d = document.createElement('div'); d.className = 'rq-msg andy';
    d.innerHTML = '<span class="rq-av" aria-hidden="true">A</span><div class="rq-bub rq-typing"><i></i><i></i><i></i></div>';
    body.appendChild(d); down();
    setTimeout(function() { d.remove(); cb(); }, ms || 600);
  }
  function say(html, cb) { setQuick([]); lock(); typing(function() { bubble('andy', html); if (cb) cb(); }); }
  function setQuick(items) {
    quick.innerHTML = '';
    items.forEach(function(it) {
      var b = document.createElement('button'); b.type = 'button'; b.className = 'rq-chip' + (it.primary ? ' primary' : '');
      b.textContent = it.label; b.onclick = function() { setQuick([]); it.fn(); }; quick.appendChild(b);
    });
    down();
  }
  function lock() { input.disabled = true; sendBtn.disabled = true; attach.disabled = true; input.placeholder = 'Choose an option above…'; }
  function unlock(ph) { input.disabled = false; sendBtn.disabled = false; attach.disabled = false; input.placeholder = ph; input.focus({ preventScroll: true }); }

  function askCategory() {
    st.step = 'category';
    say('Hi ' + esc(FIRST) + ' 👋 I\\'m Andy. What can we help you with today?', function() {
      setQuick(CHIPS.map(function(c) { return { label: c.label, fn: function() { pick(c.value, c.label); } }; }));
    });
  }
  function pick(value, label) {
    st.category = value; st.label = label;
    bubble('user', esc(label));
    askDetails(false);
  }
  function askDetails(again) {
    st.step = 'details';
    var msg = again ? 'No problem. Type your message again and I\\'ll update it.'
      : 'Got it: <b>' + esc(st.label) + '</b>. Tell me what you need. Sizes, location and what\\'s wrong all help.';
    say(msg, function() { unlock('Type your message…'); });
  }
  function onSend(text) {
    text = text.trim();
    if (!text) return;
    bubble('user', esc(text).replace(/\\n/g, '<br>'));
    input.value = ''; grow();
    if (text.length < 10) {
      say('Could you give me a little more detail? A sentence or two is enough.', function() { unlock('Type your message…'); });
      return;
    }
    st.desc = text; askPhotos();
  }
  function askPhotos() {
    st.step = 'photos';
    if (files.files.length) { review(); return; }
    say('Do you have photos or files that would help? You can skip this.', function() {
      lock(); attach.disabled = false;
      setQuick([{ label: '📎 Add photos', primary: true, fn: function() { files.click(); } }, { label: 'Skip', fn: function() { bubble('user', 'Skip'); review(); } }]);
    });
  }
  function review() {
    st.step = 'review';
    var n = files.files.length;
    var sum = '<div class="rq-sum"><div><span>Service</span><b>' + esc(st.label) + '</b></div><div><span>Your message</span><p>' + esc(st.desc).replace(/\\n/g, '<br>') + '</p></div><div><span>Files</span><b>' + (n ? n + ' attached' : 'None') + '</b></div></div>';
    say('Thanks! Here is what I\\'ll send to the team:' + sum, function() {
      lock();
      setQuick([
        { label: 'Send request ✅', primary: true, fn: send },
        { label: 'Change message', fn: function() { askDetails(true); } },
        { label: 'Start over', fn: function() { location.href = '{{ url_for("request_service") }}'; } }
      ]);
    });
  }
  function title() {
    var t = st.desc.split('\\n')[0]; if (t.length > 60) { t = t.slice(0, 60); t = t.slice(0, Math.max(t.lastIndexOf(' '), 30)) + '…'; }
    return (st.label + ': ' + t).slice(0, 120);
  }
  function send() {
    bubble('user', 'Send request');
    say('Sending your request to the team…', function() {
      document.getElementById('rqTitle').value = title();
      document.getElementById('rqCategory').value = st.category;
      document.getElementById('rqDesc').value = st.desc;
      form.submit();
    });
  }

  files.addEventListener('change', function() {
    if (files.files.length > 6) {
      var dt = new DataTransfer(); [].slice.call(files.files, 0, 6).forEach(function(f) { dt.items.add(f); }); files.files = dt.files;
      bubble('andy', 'I can take up to 6 files, so I kept the first 6.');
    }
    var html = '', n = files.files.length;
    [].forEach.call(files.files, function(f) {
      html += (f.type.indexOf('image/') === 0) ? '<img class="rq-thumb" alt="" src="' + URL.createObjectURL(f) + '">' : '<span class="rq-file">📄 ' + esc(f.name.slice(0, 24)) + '</span>';
    });
    if (n) bubble('user', '📎 ' + n + ' file' + (n > 1 ? 's' : '') + '<div class="rq-thumbs">' + html + '</div>');
    if (st.step === 'photos') review();
  });
  attach.addEventListener('click', function() { files.click(); });
  composer.addEventListener('submit', function(e) { e.preventDefault(); if (!input.disabled) onSend(input.value); });
  input.addEventListener('keydown', function(e) { if (e.key === 'Enter' && !e.shiftKey) { e.preventDefault(); if (!input.disabled) onSend(input.value); } });
  function grow() { input.style.height = 'auto'; input.style.height = Math.min(input.scrollHeight, 120) + 'px'; }
  input.addEventListener('input', grow);

  if (PRE) {
    st.category = PRE; st.label = PRE_LABEL;
    say('Hi ' + esc(FIRST) + ' 👋 I\\'m Andy. I see you\\'re interested in <b>' + esc(PRE_LABEL) + '</b>.', function() { askDetails(false); });
  } else { askCategory(); }
})();
</script>
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
    <div class="gal" style="margin-top:10px;">
      {% for a in attachments %}
        {% if a.kind == 'image' %}
          {% set au = a.filename|photo_url("attachments") %}<img src="{{ au }}" alt="Attachment" loading="lazy" data-lightbox="att{{ job.id }}" data-full="{{ au }}" data-caption="{{ job.title }}">
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
      <label style="font-size:12px;color:var(--text-muted);">Status</label>
      <select name="status">
        {% for st in statuses %}<option value="{{ st }}" {{ 'selected' if job.status == st }}>{{ st.replace('_', ' ')|title }}</option>{% endfor %}
      </select>
      <label style="font-size:12px;color:var(--text-muted);">Agreed price (CONNECT)</label>
      <input type="number" name="amount" min="0" value="{{ job.amount }}">
      <button class="btn btn-purple" type="submit">Save</button>
    </form>
  </div>
{% endif %}

{% if is_customer_view and job.status == 'assigned' and job.amount and job.amount > 0 %}
  {% if payments_enabled %}
  <form method="POST" action="{{ url_for('pay_for_job', job_id=job.id) }}" style="margin-bottom:16px;"><input type="hidden" name="csrf_token" value="{{ csrf_token() }}">
    <button class="btn btn-gold" type="submit" style="width:100%;">Pay ₦{{ "{:,}".format(job.amount) }} &amp; Confirm — held in escrow</button>
  </form>
  {% else %}
  <div class="info-card" style="margin-bottom:16px;font-size:14px;">Agreed price: <b>₦{{ "{:,}".format(job.amount) }}</b>. Pay Andy using the details Andy shares in this chat.</div>
  {% endif %}
{% endif %}
{% if job.category not in ('General Support', 'Feedback', 'Bug Report') and job.status in ('submitted', 'assigned', 'in_progress') %}
  {% if is_customer_view %}
  <div class="info-card pay-note">💳 <b>Pay Andy only.</b> Never pay the artisan directly. Your artisan is paid by Andy after the job is done.</div>
  {% elif user.role == 'artisan' %}
  <div class="info-card pay-note">💳 Andy pays you after the job is complete. Do not ask for or accept payment from the customer.</div>
  {% endif %}
{% endif %}
{% if is_customer_view and job.status in ('submitted', 'assigned') and job.category not in ('General Support', 'Feedback', 'Bug Report') %}
  <form method="POST" action="{{ url_for('cancel_job', job_id=job.id) }}" style="margin-bottom:16px;" onsubmit="return confirm('Cancel this request?');"><input type="hidden" name="csrf_token" value="{{ csrf_token() }}">
    <button class="btn btn-outline" type="submit" style="width:100%;">Cancel this request</button>
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
  <div class="chat-messages" id="chatMessages" data-job="{{ job.id }}" data-me="{{ user.id }}" data-poll="{{ url_for('job_messages_json', job_id=job.id) }}">
    {% if not messages %}
      <div class="empty-state" id="chatEmpty">No messages yet.</div>
    {% endif %}
    {% for m in messages %}
      <div class="msg-row {{ 'msg-row-me' if m.sender_id == user.id else 'msg-row-them' }}" data-id="{{ m.id }}">
        {% if m.sender_id != user.id %}
          {% if m.sender_avatar %}
            <div class="profile-avatar msg-avatar" style="background-image:url('{{ m.sender_avatar|photo_url('avatars') }}');"></div>
          {% else %}
            <div class="profile-avatar profile-avatar-placeholder msg-avatar">{{ m.sender_name[0]|upper }}</div>
          {% endif %}
        {% endif %}
        <div class="msg {{ 'me' if m.sender_id == user.id else 'them' }}">
          {% if m.sender_id != user.id %}<div class="msg-sender">{{ m.sender_name }} · {{ m.sender_role|title }}</div>{% endif %}
          {% if m.text %}<span class="msg-text">{{ m.text }}</span>{% endif %}
          {% if m.attachment_filename %}
            {% if m.attachment_kind == 'image' %}
              <div><img src="{{ m.attachment_filename|photo_url('attachments') }}" style="max-width:180px;border-radius:8px;margin-top:6px;"></div>
            {% else %}
              <div><a href="{{ m.attachment_filename|photo_url('attachments') }}" target="_blank" style="color:inherit;text-decoration:underline;">📎 attachment</a></div>
            {% endif %}
          {% endif %}
          <span class="msg-meta">{{ (m.created_at|string)[11:16] }}{% if m.sender_id == user.id %} <span class="ticks {{ 'ticks-read' if m.is_read }}" data-tick="{{ m.id }}">{{ '✓✓' if m.is_read else '✓' }}</span>{% endif %}</span>
        </div>
      </div>
    {% endfor %}
  </div>
  <form class="chat-input telegram-composer" id="chatForm" method="POST" action="{{ url_for('post_job_message', job_id=job.id) }}" enctype="multipart/form-data"><input type="hidden" name="csrf_token" value="{{ csrf_token() }}">
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

<script>
(function() {
  var box = document.getElementById('chatMessages');
  if (!box) return;
  var me = parseInt(box.dataset.me, 10);
  var pollUrl = box.dataset.poll;
  var form = document.getElementById('chatForm');
  var busy = false;

  function lastId() {
    var rows = box.querySelectorAll('.msg-row[data-id]');
    return rows.length ? parseInt(rows[rows.length - 1].dataset.id, 10) : 0;
  }
  function scrollDown() { box.scrollTop = box.scrollHeight; }
  function esc(t) { var d = document.createElement('div'); d.textContent = t == null ? '' : t; return d.innerHTML; }

  function render(m) {
    var mine = m.sender_id === me;
    var row = document.createElement('div');
    row.className = 'msg-row ' + (mine ? 'msg-row-me' : 'msg-row-them');
    row.dataset.id = m.id;
    var h = '';
    if (!mine) {
      h += m.avatar_url
        ? '<div class="profile-avatar msg-avatar" style="background-image:url(&quot;' + esc(m.avatar_url) + '&quot;);"></div>'
        : '<div class="profile-avatar profile-avatar-placeholder msg-avatar">' + esc((m.sender_name || '?')[0].toUpperCase()) + '</div>';
    }
    h += '<div class="msg ' + (mine ? 'me' : 'them') + '">';
    if (!mine) h += '<div class="msg-sender">' + esc(m.sender_name) + ' · ' + esc(m.sender_role_label) + '</div>';
    if (m.text) h += '<span class="msg-text">' + esc(m.text) + '</span>';
    if (m.attachment_url) {
      h += m.attachment_kind === 'image'
        ? '<div><img src="' + esc(m.attachment_url) + '" style="max-width:180px;border-radius:8px;margin-top:6px;"></div>'
        : '<div><a href="' + esc(m.attachment_url) + '" target="_blank" style="color:inherit;text-decoration:underline;">📎 attachment</a></div>';
    }
    h += '<span class="msg-meta">' + esc(m.time);
    if (mine) h += ' <span class="ticks ' + (m.is_read ? 'ticks-read' : '') + '" data-tick="' + m.id + '">' + (m.is_read ? '✓✓' : '✓') + '</span>';
    h += '</span></div>';
    row.innerHTML = h;
    return row;
  }

  function apply(data) {
    if (!data) return;
    var empty = document.getElementById('chatEmpty');
    var added = false;
    (data.messages || []).forEach(function(m) {
      if (box.querySelector('.msg-row[data-id="' + m.id + '"]')) return;
      if (empty) { empty.remove(); empty = null; }
      box.appendChild(render(m));
      added = true;
    });
    (data.read_ids || []).forEach(function(id) {
      var t = box.querySelector('[data-tick="' + id + '"]');
      if (t && !t.classList.contains('ticks-read')) { t.classList.add('ticks-read'); t.textContent = '✓✓'; }
    });
    if (added) scrollDown();
    if (window.updateUnreadBadges) window.updateUnreadBadges(data.unread);
  }

  function poll() {
    if (busy || document.hidden) return;
    busy = true;
    fetch(pollUrl + '?after=' + lastId(), {credentials: 'same-origin', headers: {'X-Requested-With': 'fetch'}})
      .then(function(r) { return r.ok ? r.json() : null; })
      .then(apply)
      .catch(function() {})
      .then(function() { busy = false; });
  }
  setInterval(poll, 2500);
  document.addEventListener('visibilitychange', function() { if (!document.hidden) poll(); });
  scrollDown();

  if (form) {
    form.addEventListener('submit', function(e) {
      e.preventDefault();
      var input = form.querySelector('.chat-text-input');
      var fileIn = form.querySelector('input[type=file]');
      if (!input.value.trim() && !(fileIn.files && fileIn.files.length)) return;
      var fd = new FormData(form);
      var ids = box.querySelectorAll('.msg-row[data-id]');
      fd.append('after', ids.length ? ids[ids.length - 1].dataset.id : 0);
      var btn = form.querySelector('.send-btn');
      btn.disabled = true;
      fetch(form.action, {method: 'POST', body: fd, credentials: 'same-origin', headers: {'X-Requested-With': 'fetch'}})
        .then(function(r) { return r.json(); })
        .then(function(d) {
          input.value = ''; fileIn.value = '';
          var lbl = document.querySelector('[id^="chat-file-label-"]'); if (lbl) lbl.textContent = '';
          apply(d);
        })
        .catch(function() { form.submit(); })
        .then(function() { btn.disabled = false; input.focus(); });
    });
  }
})();
</script>

{% endblock %}
''',
}

MORE_TEMPLATES_2 = {

"admin_dashboard.html": '''{% extends "base.html" %}
{% block content %}

<div class="section-title">📊 Admin Overview</div>
{% for w in warnings %}<div class="info-card" style="border-color:#ef4444;background:rgba(239,68,68,.08);margin-bottom:10px;font-size:14px;">⚠️ {{ w }}</div>{% endfor %}
{% if resets %}
<div class="info-card" style="margin-bottom:14px;">
  <b>🔑 Password reset requests</b>
  <p style="font-size:12px;color:var(--text-muted);margin:4px 0 8px;">Only you can see these links. Send one to the customer (for example in chat). Each works for 1 hour.</p>
  {% for r in resets %}<div style="font-size:13px;margin-bottom:8px;word-break:break-all;"><b>{{ r.name }}</b> ({{ r.email }})<br><a href="{{ r.link }}" style="color:var(--accent);">{{ r.link }}</a></div>{% endfor %}
</div>
{% endif %}
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

<div class="cat-head">
  <div>
    <div class="section-title" style="margin-bottom:4px;">🛒 Product Catalogue</div>
    <p class="cat-sub">Standard aluminum windows, doors and partitions. Pick a size and add to your cart.</p>
  </div>
  {% if user and user.role == 'customer' %}<a class="cat-cart" href="{{ url_for('cart') }}">🧺 My cart</a>{% endif %}
</div>

<div class="cat-filter-row" role="navigation" aria-label="Product categories">
  <a href="{{ url_for('catalog') }}" class="cat-filter {{ 'active' if not active_cat }}">All <span>{{ total_products }}</span></a>
  {% for c in categories %}
    <a href="{{ url_for('catalog', cat=c) }}" class="cat-filter {{ 'active' if active_cat == c }}">{{ c }} <span>{{ counts.get(c, 0) }}</span></a>
  {% endfor %}
</div>

<div class="product-grid">
  {% for p in products %}
    <article class="pcard">
      {% if p.image_filename %}
        {% set pu = p.image_filename|photo_url("products") %}
        <div class="pimg" style="--bg:url('{{ pu }}');"><img src="{{ pu }}" alt="{{ p.name }}" loading="lazy"></div>
      {% else %}
        <div class="pimg pimg-art">{{ category_graphic(p.category)|safe }}</div>
      {% endif %}
      {% if p.video_url %}
        <video class="pvideo" controls muted preload="metadata" src="{{ p.video_url|photo_url('products') }}"></video>
      {% endif %}
      <div class="pbody">
        <div class="pcat">{{ p.category }}</div>
        <h3 class="pname">{{ p.name }}</h3>
        {% if p.description %}<p class="pdesc">{{ p.description }}</p>{% endif %}
        {% if p.price > 0 %}<div class="pprice">₦{{ "{:,}".format(p.price) }} <span>per unit</span></div>{% else %}<div class="pprice pquote">Ask for a quote</div>{% endif %}
        {% if p.price <= 0 %}
          {% if user and user.role == 'customer' %}<a class="btn btn-purple pform-login" style="text-align:center;" href="{{ url_for('request_service', category=p.category) }}">Request a quote</a>
          {% elif not user %}<button class="btn btn-outline pform-login" type="button" onclick="document.getElementById('authModal').classList.add('open')">Log in to ask</button>{% endif %}
        {% elif user and user.role == 'customer' %}
          <form method="POST" action="{{ url_for('add_to_cart', product_id=p.id) }}" class="pform"><input type="hidden" name="csrf_token" value="{{ csrf_token() }}">
            {% if p.sizes %}
              <select name="size" required aria-label="Size">{% for sz in p.sizes %}<option value="{{ sz }}">{{ sz }}</option>{% endfor %}</select>
            {% endif %}
            <input type="number" name="quantity" value="1" min="1" aria-label="Quantity">
            <button class="btn btn-purple" type="submit">Add to cart</button>
          </form>
        {% elif not user %}
          <button class="btn btn-outline pform-login" type="button" onclick="document.getElementById('authModal').classList.add('open')">Log in to order</button>
        {% endif %}
      </div>
    </article>
  {% endfor %}
</div>

{% if not products %}
  <div class="empty-state">No products here yet.{% if active_cat %} <a href="{{ url_for('catalog') }}" style="color:var(--accent);font-weight:600;">See all products</a>.{% endif %}</div>
{% endif %}

<div class="cat-help">Can't find what you need? Andy also makes custom aluminum work.
  {% if user and user.role == 'customer' %}<a href="{{ url_for('request_service') }}">Request a service →</a>
  {% elif not user %}<a href="#" onclick="document.getElementById('authModal').classList.add('open');return false;">Request a service →</a>{% endif %}
</div>

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

"admin_works.html": '''{% extends "base.html" %}
{% block content %}
<div class="section-title">📸 Upload Our Work</div>
<p style="font-size:13px;color:var(--text-muted);margin-bottom:14px;">Show customers the windows and doors you have finished. Everything here appears on the public <b>Our Work</b> page as ANDY's work.</p>

<div class="settings-card">
  <div class="settings-card-title">Upload a finished job</div>
  <form method="POST" action="{{ url_for('works') }}" enctype="multipart/form-data" class="auth-form" style="margin-top:10px;"><input type="hidden" name="csrf_token" value="{{ csrf_token() }}">
    <input type="hidden" name="next" value="{{ url_for('admin_works') }}">
    <input type="text" name="title" placeholder="Project title (e.g. 3-panel sliding window, Lekki)" required maxlength="120">
    <select name="category"><option value="">Category (optional)</option>{% for c in categories %}<option value="{{ c }}">{{ c }}</option>{% endfor %}</select>
    <textarea name="description" placeholder="What was the job? Size, materials, result" rows="3"></textarea>
    <input type="file" name="photos" accept=".jpg,.jpeg,.png,.webp,.mp4,.mov,.webm,.m4v" multiple required data-maxmb="95">
    <p class="media-hint">Photos and videos. Videos keep their sound. Under 95 MB each.</p>
    <button class="btn btn-purple" type="submit">Publish to Our Work</button>
  </form>
</div>

<div class="section-title" style="margin-top:22px;">⏳ Waiting for your review {% if pending %}<span class="unread-badge">{{ pending|length }}</span>{% endif %}</div>
{% for w in pending %}
  <div class="settings-card">
    <div style="font-size:12px;color:var(--text-muted);margin-bottom:8px;">Submitted by <b>{{ w.submitter or 'an artisan' }}</b> · only you can see this name</div>
    {% if w.photos %}<div class="gal {{ 'single' if w.photos|length == 1 }}">{% for ph in w.photos %}{% set pu = ph.filename|photo_url("works") %}{% if ph.kind == 'video' %}<video class="gal-video" src="{{ pu }}#t=0.1" controls playsinline preload="metadata"></video>{% else %}<img src="{{ pu }}" alt="{{ w.title }}" loading="lazy" data-lightbox="aw{{ w.id }}" data-full="{{ pu }}" data-caption="{{ w.title }}">{% endif %}{% endfor %}</div>{% endif %}
    <form method="POST" action="{{ url_for('admin_work_approve', work_id=w.id) }}" class="auth-form" style="margin-top:10px;"><input type="hidden" name="csrf_token" value="{{ csrf_token() }}">
      <input type="text" name="title" value="{{ w.title }}" maxlength="120">
      <select name="category"><option value="">Category</option>{% for c in categories %}<option value="{{ c }}" {{ 'selected' if w.category == c }}>{{ c }}</option>{% endfor %}</select>
      <textarea name="description" rows="2">{{ w.description }}</textarea>
      <button class="btn btn-purple" type="submit">✅ Approve and publish</button>
    </form>
    <form method="POST" action="{{ url_for('admin_work_reject', work_id=w.id) }}" class="auth-form" style="margin-top:8px;display:flex;gap:8px;"><input type="hidden" name="csrf_token" value="{{ csrf_token() }}">
      <input type="text" name="reason" placeholder="Reason (optional, the artisan sees it)" maxlength="200" style="flex:1;">
      <button class="btn btn-outline" type="submit">Reject</button>
    </form>
  </div>
{% endfor %}
{% if not pending %}<div class="empty-state">Nothing waiting. Work your artisans upload shows up here.</div>{% endif %}

<div class="section-title" style="margin-top:22px;">✅ Published</div>
{% for w in published %}
  <div class="feed-post">
    <div class="job-title" style="margin-bottom:6px;">{{ w.title }}{% if w.category %} <span class="work-tag">{{ w.category }}</span>{% endif %}{% if w.submitter %} <span class="work-tag">by {{ w.submitter }}</span>{% endif %}</div>
    {% if w.photos %}<div class="gal {{ 'single' if w.photos|length == 1 }}">{% for ph in w.photos %}{% set pu = ph.filename|photo_url("works") %}{% if ph.kind == 'video' %}<video class="gal-video" src="{{ pu }}#t=0.1" controls playsinline preload="metadata"></video>{% else %}<img src="{{ pu }}" alt="{{ w.title }}" loading="lazy" data-lightbox="pw{{ w.id }}" data-full="{{ pu }}" data-caption="{{ w.title }}">{% endif %}{% endfor %}</div>{% endif %}
    <form method="POST" action="{{ url_for('delete_work', work_id=w.id) }}" style="margin-top:10px;" onsubmit="return confirm('Remove this from Our Work?');"><input type="hidden" name="csrf_token" value="{{ csrf_token() }}">
      <input type="hidden" name="next" value="{{ url_for('admin_works') }}">
      <button class="btn btn-outline" type="submit" style="font-size:11px;padding:6px 10px;">Remove</button>
    </form>
  </div>
{% endfor %}
{% if not published %}<div class="empty-state">No work published yet. Upload your first job above.</div>{% endif %}
{% endblock %}
''',

"artisan_work.html": '''{% extends "base.html" %}
{% block content %}
<div class="section-title">📸 My Completed Work</div>
<p style="font-size:13px;color:var(--text-muted);margin-bottom:14px;">Upload photos of jobs you have finished. Andy checks each one first. Approved work appears on the public Our Work page as ANDY's work.</p>

<div class="settings-card">
  <div class="settings-card-title">Add a finished job</div>
  <form method="POST" enctype="multipart/form-data" class="auth-form" style="margin-top:10px;"><input type="hidden" name="csrf_token" value="{{ csrf_token() }}">
    <input type="text" name="title" placeholder="What did you make? (e.g. Sliding window, 150 x 120 cm)" required maxlength="120">
    <select name="category"><option value="">Category (optional)</option>{% for c in categories %}<option value="{{ c }}">{{ c }}</option>{% endfor %}</select>
    <textarea name="description" placeholder="Materials, size, anything worth noting" rows="3"></textarea>
    <input type="file" name="photos" accept=".jpg,.jpeg,.png,.webp,.mp4,.mov,.webm,.m4v" multiple required data-maxmb="95">
    <p style="font-size:12px;color:var(--text-muted);">Up to 8 photos or videos (videos keep their sound, under 95 MB each). Do not show customer names or phone numbers.</p>
    <button class="btn btn-purple" type="submit">Send to Andy for review</button>
  </form>
</div>

<div class="section-title" style="margin-top:22px;">My submissions</div>
{% for w in mine %}
  <div class="feed-post">
    <div class="job-title" style="margin-bottom:6px;">{{ w.title }}
      <span class="work-status work-status-{{ w.status }}">{{ {'pending':'⏳ Waiting for review','approved':'✅ Live','rejected':'❌ Not approved'}[w.status] }}</span></div>
    {% if w.status == 'rejected' and w.reject_reason %}<div class="feed-post-caption" style="color:#ef4444;">Andy says: {{ w.reject_reason }}</div>{% endif %}
    {% if w.photos %}<div class="gal {{ 'single' if w.photos|length == 1 }}">{% for ph in w.photos %}{% set pu = ph.filename|photo_url("works") %}{% if ph.kind == 'video' %}<video class="gal-video" src="{{ pu }}#t=0.1" controls playsinline preload="metadata"></video>{% else %}<img src="{{ pu }}" alt="{{ w.title }}" loading="lazy" data-lightbox="mw{{ w.id }}" data-full="{{ pu }}" data-caption="{{ w.title }}">{% endif %}{% endfor %}</div>{% endif %}
    {% if w.status != 'approved' %}
      <form method="POST" style="margin-top:10px;" onsubmit="return confirm('Remove this submission?');"><input type="hidden" name="csrf_token" value="{{ csrf_token() }}">
        <input type="hidden" name="action" value="delete"><input type="hidden" name="work_id" value="{{ w.id }}">
        <button class="btn btn-outline" type="submit" style="font-size:11px;padding:6px 10px;">Remove</button>
      </form>
    {% endif %}
  </div>
{% endfor %}
{% if not mine %}<div class="empty-state">You have not uploaded any work yet.</div>{% endif %}
{% endblock %}
''',

"terms.html": '''{% extends "base.html" %}
{% block content %}
<div class="legal">
  <h1>Andy Terms &amp; Conditions</h1>
  <div class="legal-date">Effective date: 24 October 2026</div>

  <p>Welcome to Andy, a platform designed to connect customers with service providers for aluminum fabrication, window and door installation, repairs, and other related services.</p>
  <p>By accessing or using Andy, you agree to these Terms and Conditions. Please read them carefully before using the platform.</p>

  <h2>1. About Andy</h2>
  <p>Andy is an aluminum service platform. Andy is starting with its own team of artisans: aluminum fabricators, also known as alloy artisans, who work as Andy's staff. When you send a service request, Andy assigns one of its artisans to your job and provides in-app chat, job coordination and related tools.</p>
  <p>In future, Andy may also connect customers with other approved service providers. If that happens, these Terms or the relevant job details will say so.</p>

  <h2>2. Eligibility and Account Registration</h2>
  <p>To use Andy, you must be at least 18 years old and you agree to:</p>
  <ul>
    <li>Provide accurate and truthful information when creating an account.</li>
    <li>Keep your login credentials secure.</li>
    <li>Use your account only for lawful purposes.</li>
    <li>Update your information when necessary.</li>
    <li>Notify Andy if you suspect unauthorized access to your account.</li>
  </ul>
  <p>You must not impersonate another person, create accounts using false identities, or use the platform to deceive other users.</p>
  <p>Andy reserves the right to restrict or suspend accounts involved in suspected fraud, abuse, or violations of these Terms, subject to applicable law.</p>

  <h2>3. Customer Responsibilities</h2>
  <p>Customers using Andy agree to:</p>
  <ul>
    <li>Provide accurate descriptions of the services they require.</li>
    <li>Supply correct contact details and relevant job information.</li>
    <li>Provide reasonable access to the work location when necessary.</li>
    <li>Communicate respectfully with service providers.</li>
    <li>Agree on the scope of work, materials, costs, and expected completion time before work begins.</li>
    <li>Make agreed payments according to the terms established for the job.</li>
    <li>Ensure that the work location is reasonably safe for the service provider.</li>
  </ul>
  <p>Customers should inspect completed work and communicate any concerns promptly.</p>
  <p>Customers must not use Andy to request illegal services, harass workers, or engage in fraudulent activities.</p>

  <h2>4. Service Provider Responsibilities</h2>
  <p>Service providers (also called artisans) are Andy's staff and join Andy by invitation. Service providers using Andy agree to:</p>
  <ul>
    <li>Provide accurate information about their identity, qualifications, experience, and services.</li>
    <li>Accept only jobs they are reasonably capable of completing.</li>
    <li>Communicate honestly about prices, materials, timelines, and job requirements.</li>
    <li>Carry out agreed work with reasonable care, skill, and professionalism.</li>
    <li>Use suitable materials and equipment for the agreed job.</li>
    <li>Respect customers, their property, and their privacy.</li>
    <li>Follow applicable safety requirements, building regulations, and other relevant laws.</li>
    <li>Notify customers promptly of delays, unexpected costs, or circumstances that may affect the job.</li>
    <li>Avoid misleading claims, fraudulent conduct, and unauthorized charges.</li>
    <li>Never ask for or accept payment directly from a customer. All payments go to Andy.</li>
  </ul>
  <p>Service providers must not claim qualifications, certifications, or experience they do not possess.</p>

  <h2>5. Service Requests and Agreements</h2>
  <p>Submitting a service request through Andy does not automatically guarantee that a service provider will accept or be assigned to the job. Andy decides which service provider, if any, is assigned to a request. So that the job can be done, Andy may share your request details, photos, files and chat messages with the assigned service provider.</p>
  <p>Before work begins, the customer and Andy should clearly agree on:</p>
  <ul>
    <li>The exact work to be performed.</li>
    <li>The total price or pricing method.</li>
    <li>The materials and components required.</li>
    <li>Who will supply the materials.</li>
    <li>The expected start date and completion time.</li>
    <li>Any additional charges that may arise from changes to the original job.</li>
  </ul>
  <p>Any change to the agreed scope of work should be communicated to Andy and accepted by the customer before the additional work is carried out.</p>
  <p>Andy may introduce additional job confirmation or tracking features as the platform develops.</p>

  <h2>6. Pricing and Payments</h2>
  <p>Customers and Andy must ensure that the price and payment arrangements for a job are clearly understood before work begins.</p>
  <p><b>All payments for jobs arranged through Andy must be made to Andy.</b> Customers must not pay service providers directly, and service providers must not ask for or accept payment directly from customers.</p>
  <p>Andy pays the service provider after the job is completed. Where payment is made in the app, the agreed amount is held by Andy and released to the service provider when the job is marked complete. Where in-app payment is not available, Andy will share payment details in the job chat.</p>
  <p>If Andy cancels a job that has already been paid for, Andy will return the amount to the customer (to their wallet where the payment was made in the app). Phone numbers and similar contact details shared in chat may be hidden by the platform.</p>
  <p>Customers must not knowingly withhold an agreed payment for properly completed work in violation of their agreement.</p>
  <p>Any payment-related procedures introduced by Andy will be communicated to users through the relevant platform features or notices.</p>

  <h2>7. Quality of Work and Workmanship</h2>
  <p>Service providers are expected to perform work with reasonable care and skill consistent with the agreed service.</p>
  <p>For aluminum-related services, customers and service providers should agree in advance on relevant specifications, including measurements, materials, finishes, hardware, installation requirements, and other applicable details.</p>
  <p><b>Measurements from the Andy tools are estimates only.</b> The Measure a Window tool and any photo-based measurement can be wrong. Always confirm the real size with a tape measure before anything is cut or fabricated.</p>
  <p>Andy encourages both parties to document important specifications and approvals before fabrication or installation begins.</p>
  <p>Andy may review complaints about service quality and take appropriate action against users who repeatedly engage in dishonest, unsafe, or unprofessional conduct.</p>
  <p>Unless expressly agreed otherwise in writing, Andy does not automatically provide a separate written warranty beyond what is agreed for the job or required by law. Any warranty offered must be communicated clearly to the customer.</p>

  <h2>8. Andy's Artisans</h2>
  <p>The service providers who carry out jobs on Andy are Andy's own staff. They work on Andy's behalf, and Andy is responsible for the services they deliver as set out in these Terms and in applicable law.</p>
  <p>Andy is starting with its own team of aluminum fabricators (alloy artisans). If Andy later works with independent service providers, it will make that clear on the platform.</p>
  <p>Nothing in these Terms excludes any responsibility that Andy may have under applicable law.</p>

  <h2>9. Safety and Property Protection</h2>
  <p>Customers and service providers must take reasonable precautions to protect people and property during service delivery.</p>
  <p>Service providers must use appropriate tools, equipment, and safety practices for their work. Customers should communicate relevant site hazards before work begins.</p>
  <p>Neither party should request or carry out work in a manner that creates an unreasonable risk of injury or property damage.</p>
  <p>Any incident involving injury, theft, property damage, or serious misconduct should be reported to Andy promptly where relevant.</p>

  <h2>10. Cancellations and Job Changes</h2>
  <p>Customers and service providers should communicate cancellations, rescheduling requests, and changes to agreed job requirements as early as reasonably possible.</p>
  <p>A customer can cancel a request from the job page before it has been paid for. After that, the customer should contact Andy through the job chat. Andy may also cancel a job where necessary.</p>
  <p>Where a cancellation or change affects materials already purchased, work already completed, or other commitments, the parties should address those matters according to their existing agreement and applicable law.</p>
  <p>Andy may establish additional cancellation and scheduling procedures as its services develop.</p>

  <h2>11. Complaints and Dispute Resolution</h2>
  <p>If a disagreement arises between a customer and a service provider, both parties are encouraged to communicate respectfully and attempt to resolve the issue directly.</p>
  <p>Users may contact Andy through the in-app chat (Contact Andy), or through Feedback and Report a Bug, to report:</p>
  <ul>
    <li>Poor service or alleged defective workmanship.</li>
    <li>Misrepresentation or suspected fraud.</li>
    <li>Unprofessional conduct.</li>
    <li>Disagreements concerning job specifications.</li>
    <li>Payment disputes.</li>
    <li>Safety concerns or property damage.</li>
  </ul>
  <p>Andy may review available information, request supporting evidence, and communicate with the parties where appropriate. Depending on the circumstances, Andy may issue warnings, restrict accounts, suspend access, or remove users who violate platform rules.</p>
  <p>Andy does not guarantee that every dispute can be resolved through its internal process. Users retain any rights available to them under applicable law.</p>

  <h2>12. Prohibited Activities</h2>
  <p>Users must not:</p>
  <ul>
    <li>Use Andy for fraudulent, unlawful, or deceptive activities.</li>
    <li>Submit false service requests.</li>
    <li>Provide fake identities, qualifications, or business details.</li>
    <li>Harass, threaten, discriminate against, or abuse other users.</li>
    <li>Manipulate reviews, ratings, likes, or feedback.</li>
    <li>Pay, or ask for or accept payment, for an Andy job outside Andy.</li>
    <li>Damage or attempt to compromise Andy's website, systems, or data.</li>
    <li>Use the platform to distribute malicious software or conduct unauthorized access.</li>
    <li>Publish another person's confidential information without lawful authorization.</li>
    <li>Circumvent platform procedures for fraudulent purposes.</li>
  </ul>
  <p>Andy may take appropriate action when these rules are violated.</p>

  <h2>13. Reviews and Feedback</h2>
  <p>Customers may be permitted to submit ratings, reviews, comments and likes about completed work shown on Andy. Reviews show the reviewer's first name and last initial.</p>
  <p>All reviews must be honest, relevant, and based on genuine experience. Users must not submit fabricated reviews, threaten others with false reviews, or manipulate ratings.</p>
  <p>Andy reserves the right to moderate or remove content that violates platform rules or applicable law.</p>

  <h2>14. Privacy and Personal Information</h2>
  <p>Andy collects and processes personal information necessary to operate the platform, manage accounts, facilitate service requests, provide support, and improve its services. This includes the details you give when you sign up and the requests, messages and photos you send.</p>
  <p>Users agree to provide information lawfully and must not misuse personal information obtained through Andy.</p>
  <p>Andy will handle personal information in accordance with its <a href="{{ url_for('privacy') }}">Privacy Policy</a> and applicable data protection laws. Please read the Privacy Policy to understand what is collected, where it is stored and who can see it.</p>

  <h2>15. Platform Availability and Changes</h2>
  <p>Andy aims to provide a useful and reliable service but does not guarantee uninterrupted access to its website or features.</p>
  <p>Maintenance, technical issues, network failures, or other circumstances may temporarily affect availability.</p>
  <p>Andy may introduce, modify, suspend, or discontinue platform features as its business develops, subject to applicable law and any relevant contractual obligations.</p>

  <h2>16. Intellectual Property and Content</h2>
  <p>The Andy name, logo, website design, original content, and other platform materials may be protected by intellectual property laws. Users may not copy, reproduce, modify, distribute, or commercially exploit protected Andy materials without authorization, except where permitted by law.</p>
  <p>Users retain ownership of content they lawfully own and submit to Andy. By submitting content, users grant Andy permission to use, display, and process that content as reasonably necessary to operate, promote, and improve the platform, subject to applicable law and the Privacy Policy.</p>
  <p>Photos and videos of completed work submitted by Andy's artisans are reviewed by Andy. Once approved, they may be shown publicly on Andy, including on the Our Work page and in Andy's promotion. Artisans confirm they have the right to share what they submit.</p>
  <p>Users must not upload content that infringes another person's intellectual property rights.</p>

  <h2>17. Limitation of Liability</h2>
  <p>To the extent permitted by applicable law, Andy is not responsible for losses arising solely from circumstances outside its reasonable control, including third-party misconduct or inaccurate information supplied by users.</p>
  <p>Andy is responsible for the services its artisans deliver as set out in these Terms and in applicable law. Andy is not responsible for losses caused by a customer's inaccurate information, a customer's failure to give access or follow agreed steps, or measurements the customer supplied.</p>
  <p>Nothing in these Terms excludes or limits liability where such exclusion or limitation is prohibited by law, including any non-excludable consumer rights.</p>

  <h2>18. Account Suspension and Termination</h2>
  <p>Andy may restrict, suspend, or terminate a user's access where there are reasonable grounds to believe that the user:</p>
  <ul>
    <li>Has violated these Terms.</li>
    <li>Has engaged in fraud, harassment, or serious misconduct.</li>
    <li>Has compromised platform security.</li>
    <li>Has repeatedly provided misleading information.</li>
    <li>Has used Andy in a manner that creates a serious safety or legal concern.</li>
  </ul>
  <p>Where appropriate and legally permissible, Andy may notify the affected user of the reason for the action.</p>
  <p>Users may stop using Andy at any time and may request account closure by messaging Andy through the in-app chat. Any obligations or rights that reasonably need to continue after account closure will remain effective to the extent permitted by law.</p>

  <h2>19. Changes to These Terms</h2>
  <p>Andy may update these Terms to reflect changes in its services, business operations, technology, or legal obligations.</p>
  <p>Updated Terms will be published on this page with a revised effective date. Where required by law, Andy will provide notice of significant changes or obtain any necessary consent.</p>
  <p>Continued use of Andy after updated Terms take effect constitutes acceptance only to the extent permitted by applicable law.</p>

  <h2>20. Governing Law</h2>
  <p>These Terms are governed by the laws of the Federal Republic of Nigeria, subject to applicable conflict-of-law rules and mandatory legal protections.</p>
  <p>Any dispute will be handled through the courts or other dispute-resolution mechanisms with appropriate jurisdiction, subject to applicable law.</p>

  <h2>21. Contact and Support</h2>
  <p>For questions, complaints, or concerns about these Terms, contact Andy through the in-app chat (Contact Andy) after logging in{% if contact.email %}, or by email{% endif %}.</p>
  <p>
    <b>Platform:</b> Andy<br>
    <b>Website:</b> {{ request.host_url.rstrip('/') }}
    {% if contact.email %}<br><b>Support email:</b> <a href="mailto:{{ contact.email }}">{{ contact.email }}</a>{% endif %}
    {% if contact.phone %}<br><b>Phone:</b> {{ contact.phone }}{% endif %}
    {% if contact.address %}<br><b>Business address:</b> {{ contact.address }}{% endif %}
  </p>

  <p style="margin-top:28px;"><b>By creating an account or using Andy, you acknowledge that you have read and understood these Terms and agree to comply with them.</b></p>
</div>
{% endblock %}
''',

"privacy.html": '''{% extends "base.html" %}
{% block content %}
<div class="legal">
  <h1>Privacy Policy</h1>
  <div class="legal-date">Last updated: October 2026</div>
  <p>This policy explains what ANDY collects, why, and the choices you have.</p>

  <h2>The details we collect</h2>
  <ul>
    <li><b>When you sign up:</b> your name, your email address and a password. Your password is stored scrambled, so nobody at ANDY can read it. If you sign in with Google, we receive your name and email from Google.</li>
    <li><b>When you use ANDY:</b> the service requests you send (title, description, category, and any photos or files), your chat messages and attachments, window measurements and photos you save, and the reviews and likes you post.</li>
    <li><b>Optional:</b> a profile photo and short bio, and a device address if you turn on browser notifications.</li>
    <li><b>Artisans:</b> a phone number and work category, added by ANDY.</li>
    <li><b>Payments:</b> if payments are switched on, the amounts and references of your wallet top-ups and jobs. We never see or store your card details. The payment provider handles those.</li>
    <li><b>Small files in your browser:</b> a login cookie, and your light or dark mode choice.</li>
  </ul>
  <p>We do <b>not</b> collect your card numbers, your exact location or your ID documents.</p>

  <h2>Where your details go</h2>
  <ul>
    <li><b>Our database:</b> your account and job details are stored in {% if db_supabase %}a database hosted by <b>Supabase</b>{% else %}our secure server database{% endif %}.</li>
    <li><b>Website hosting:</b> the ANDY website runs on Render.</li>
    <li><b>Photos and videos:</b> stored with Cloudinary (when switched on), otherwise on our server.</li>
    <li><b>Emails:</b> alerts and password-reset emails are sent through an email service (Gmail).</li>
    <li><b>Notifications:</b> if you turn them on, they travel through your browser's own push service (for example Google, Apple or Mozilla).</li>
    <li><b>Google sign-in and payments:</b> Google, and Paystack when payments are switched on, only when you choose to use them.</li>
  </ul>

  <h2>Who can see it</h2>
  <ul>
    <li>The ANDY team can see accounts, requests and chats so we can run the service.</li>
    <li>The artisan assigned to your job can see that job, its photos and its chat. Other artisans cannot.</li>
    <li>The public only sees work photos and reviews that ANDY has approved. Reviews show only your first name and last initial.</li>
    <li>We do not sell your personal information.</li>
  </ul>

  <h2>How long we keep it</h2>
  <p>We keep your details while your account is open. To have your account and details deleted, message ANDY from your account.</p>

  <h2>Cookies</h2>
  <p>We use a login cookie so you stay signed in and a small preference cookie for dark mode. We do not use advertising cookies.</p>

  <h2>Keeping it safe</h2>
  <p>Passwords are stored hashed, and the site is served over HTTPS. No system is perfectly secure, so please use a strong, unique password.</p>

  <h2>Your choices</h2>
  <ul>
    <li>You can edit your profile in Settings and turn off browser notifications in your browser.</li>
    <li>To ask for a copy of your data or to have your account deleted, message ANDY from your account.</li>
  </ul>

  <h2>Changes</h2>
  <p>We may update this policy and will show the new date above. See also our <a href="{{ url_for('terms') }}">Terms &amp; Conditions</a>.</p>
</div>
{% endblock %}
''',

"consult_guide.html": '''{% extends "base.html" %}
{% block title %}Guided Consultation | ANDY{% endblock %}
{% block content %}
<div class="cg">
  <a class="cg-back" href="{{ url_for('services') }}#consultation">← Back to services</a>
  <div class="rq-chat" id="rq">
    <div class="rq-head">
      <div class="rq-avatar" aria-hidden="true">A</div>
      <div><div class="rq-name">Andy Alloy Consultation</div><div class="rq-status"><span class="rq-dot"></span>Guidance only · not an inspection or quotation</div></div>
    </div>
    <div class="cg-note"><b>Your safety comes first.</b> This guidance is general. Some projects need professional measurements or an on-site assessment.</div>
    <div class="rq-body" id="rqBody" role="log" aria-live="polite" aria-label="Guided consultation"></div>
    <div class="rq-quick" id="rqQuick"></div>
    <form class="rq-composer" id="rqComposer" autocomplete="off">
      <button type="button" class="rq-attach" id="rqAttach" aria-label="Attach photos" disabled>📎</button>
      <textarea id="rqInput" rows="1" maxlength="1000" placeholder="Choose an option above…" aria-label="Your answer" disabled></textarea>
      <button type="submit" class="rq-send" id="rqSend" aria-label="Send answer" disabled>➤</button>
    </form>
  </div>
  <input type="file" id="rqFiles" accept="image/*,.pdf" multiple hidden>
  <noscript><p class="cons-hint">This guided consultation needs JavaScript. You can still use <a href="{{ url_for('request_service') }}">Request a Service</a>.</p></noscript>
</div>

<script>
(function() {
  var G = {{ guide|tojson }};
  var LOGGED = {{ 'true' if user else 'false' }};
  var CAN = {{ 'true' if (user and user.role == 'customer') else 'false' }};
  var UNAME = {{ (user.name if user else '')|tojson }};
  var UMAIL = {{ (user.email if user else '')|tojson }};
  var CSRF = {{ csrf_token()|tojson }};
  var SUBMIT_URL = {{ url_for('consultation_request')|tojson }};
  var KEY = 'andyConsultState';
  var NL = String.fromCharCode(10);
  var body = document.getElementById('rqBody'), quick = document.getElementById('rqQuick');
  var input = document.getElementById('rqInput'), sendBtn = document.getElementById('rqSend'), attach = document.getElementById('rqAttach');
  var composer = document.getElementById('rqComposer'), files = document.getElementById('rqFiles');
  var st = { cat: null, qs: [], i: 0, ans: {}, danger: {}, sending: false, step: '' };
  var lastItems = [];
  var COST_RE = /(^|[^a-z])(price|prices|pricing|cost|costs|how much|quote|quotation|budget|cheap|expensive|naira|₦)/i;
  var DANGER_RE = /(^|[^a-z])(falling|fall|fell|fallen|collaps|shatter|crack|broken glass|detach|spark|electric|exposed wire|injur|bleed|trapped)/i;

  function esc(t) { var d = document.createElement('div'); d.textContent = t; return d.innerHTML; }
  function down() { body.scrollTop = body.scrollHeight; }
  function bubble(who, html, cls) {
    var d = document.createElement('div'); d.className = 'rq-msg ' + who + (cls ? ' ' + cls : '');
    d.innerHTML = (who === 'andy' ? '<span class="rq-av" aria-hidden="true">A</span>' : '') + '<div class="rq-bub">' + html + '</div>';
    body.appendChild(d); down(); return d;
  }
  function typing(cb) {
    var d = document.createElement('div'); d.className = 'rq-msg andy';
    d.innerHTML = '<span class="rq-av" aria-hidden="true">A</span><div class="rq-bub rq-typing"><i></i><i></i><i></i></div>';
    body.appendChild(d); down();
    setTimeout(function() { d.remove(); cb(); }, 350);
  }
  function setQuick(items) {
    if (items.length) lastItems = items;
    quick.innerHTML = '';
    items.forEach(function(it) {
      var b = document.createElement('button'); b.type = 'button'; b.className = 'rq-chip' + (it.primary ? ' primary' : '');
      b.textContent = it.label; b.onclick = function() { if (st.sending) return; setQuick([]); it.fn(); }; quick.appendChild(b);
    });
    down();
  }
  function lock() { input.disabled = true; sendBtn.disabled = true; attach.disabled = true; input.placeholder = 'Choose an option above…'; }
  function unlock(ph) { input.disabled = false; sendBtn.disabled = false; input.placeholder = ph || 'Type your answer…'; input.focus(); }
  function say(html, cb, cls) { setQuick([]); lock(); typing(function() { bubble('andy', html, cls); if (cb) cb(); }); }
  function sayAll(list, cb) {
    if (!list.length) { if (cb) cb(); return; }
    var first = list[0];
    say(first.html, function() { sayAll(list.slice(1), cb); }, first.cls);
  }
  function again() { setQuick(lastItems); }

  // ---- rules ----
  function matches(rule, a) {
    var w = rule.when || {};
    for (var k in w) {
      var list = w[k], v = a[k];
      var ok = list.indexOf(v) > -1 || (list.indexOf('*') > -1 && v !== undefined && v !== '__none');
      if (!ok) return false;
    }
    return true;
  }
  function collect(kind, firstOnly) {
    var out = [], seen = {};
    var sets = [G.rules.all || [], G.rules[st.cat] || []];
    for (var s = 0; s < sets.length; s++) {
      for (var r = 0; r < sets[s].length; r++) {
        var rule = sets[s][r];
        if (rule.kind !== kind || !matches(rule, st.ans)) continue;
        if (seen[rule.text]) continue;
        seen[rule.text] = 1; out.push(rule.text);
        if (firstOnly) return out;
      }
    }
    return out;
  }
  function recomputeDanger() { var any = false; for (var k in st.danger) { if (st.danger[k]) any = true; } if (any) st.ans.__danger = '1'; else delete st.ans.__danger; }

  // ---- flow ----
  function cat() { for (var i = 0; i < G.cats.length; i++) { if (G.cats[i].id === st.cat) return G.cats[i]; } return null; }
  function showCats() {
    st.step = 'cat';
    say('What would you like help with?', function() {
      var items = G.cats.map(function(c) { return { label: c.icon + ' ' + c.label, fn: function() { choose(c.id, c.icon + ' ' + c.label); } }; });
      items.push({ label: 'What affects the cost?', fn: function() { bubble('user', 'What affects the cost?'); say(esc(G.cost), again); } });
      setQuick(items);
    });
  }
  function choose(id, label) {
    st.cat = id; st.ans = {}; st.danger = {}; st.i = 0;
    st.qs = (G.questions[id] || []).concat(G.questions.common);
    bubble('user', esc(label));
    say(esc(cat().intro), nextQ);
  }
  function skipQ(q) {
    if (!q.ask_if) return false;
    for (var k in q.ask_if) { if (q.ask_if[k].indexOf(st.ans[k]) === -1) return true; }
    return false;
  }
  function nextQ() {
    while (st.i < st.qs.length && skipQ(st.qs[st.i])) st.i++;
    if (st.i >= st.qs.length) { finish(); return; }
    ask(st.qs[st.i]);
  }
  function backItems() {
    var items = [];
    if (st.i > 0) items.push({ label: '↩ Back', fn: goBack });
    items.push({ label: 'Start over', fn: restart });
    return items;
  }
  function goBack() {
    var j = st.i - 1;
    while (j >= 0 && skipQ(st.qs[j])) j--;
    if (j < 0) { restart(); return; }
    delete st.ans[st.qs[j].id]; delete st.danger[st.qs[j].id]; recomputeDanger();
    st.i = j; bubble('user', '↩ Back'); nextQ();
  }
  function restart() { bubble('user', 'Start over'); try { sessionStorage.removeItem(KEY); } catch (e) {} st.cat = null; st.ans = {}; st.danger = {}; showCats(); }
  function ask(q) {
    st.step = q.id;
    if (q.kind === 'photos') { askPhotos(); return; }
    var html = esc(q.text) + (q.hint ? '<br><small class="cg-hint">' + esc(q.hint) + '</small>' : '');
    say(html, function() {
      if (q.kind === 'choice') {
        var items = q.options.map(function(o) { return { label: o.label, fn: function() { answerChoice(q, o); } }; });
        setQuick(items.concat(backItems()));
      } else {
        unlock('Type your answer…');
        var items2 = [];
        if (q.optional) items2.push({ label: 'Skip', fn: function() { bubble('user', 'Skip'); lock(); st.ans[q.id] = '__none'; st.i++; nextQ(); } });
        setQuick(items2.concat(backItems()));
      }
    });
  }
  function answerChoice(q, o) {
    bubble('user', esc(o.label));
    st.ans[q.id] = o.v;
    if (o.danger) st.danger[q.id] = 1; else delete st.danger[q.id];
    recomputeDanger();
    st.i++;
    if (o.danger) say(esc(G.danger), nextQ, 'cg-warn'); else nextQ();
  }
  function onSend(text) {
    text = text.trim();
    if (!text || st.step === '' || st.step === 'cat') return;
    var q = st.qs[st.i];
    if (!q || q.kind !== 'text') return;
    bubble('user', esc(text).split(NL).join('<br>')); input.value = ''; grow();
    if (!q.optional && text.length < 3) { say('Please add a little more detail so we can help.', function() { unlock(); setQuick(backItems()); }); return; }
    st.ans[q.id] = text;
    var notes = [];
    if (DANGER_RE.test(text)) { st.danger[q.id] = 1; notes.push({ html: esc(G.danger), cls: 'cg-warn' }); } else { delete st.danger[q.id]; }
    if (COST_RE.test(text)) notes.push({ html: esc(G.cost) });
    recomputeDanger();
    st.i++; lock();
    sayAll(notes, nextQ);
  }
  function askPhotos() {
    say('Do you have photos of the opening or area? They help a lot, but you can skip this.', function() {
      lock(); attach.disabled = false;
      setQuick([{ label: '📎 Add photos', primary: true, fn: function() { files.click(); } },
                { label: 'Skip', fn: function() { bubble('user', 'Skip'); st.i++; nextQ(); } }].concat(backItems()));
    });
  }
  files.addEventListener('change', function() {
    if (files.files.length > 6) {
      var dt = new DataTransfer(); [].slice.call(files.files, 0, 6).forEach(function(f) { dt.items.add(f); }); files.files = dt.files;
      bubble('andy', 'Up to 6 files can be sent, so the first 6 were kept.');
    }
    var html = '', n = files.files.length;
    [].forEach.call(files.files, function(f) {
      html += (f.type.indexOf('image/') === 0) ? '<img class="rq-thumb" alt="" src="' + URL.createObjectURL(f) + '">' : '<span class="rq-file">📄 ' + esc(f.name.slice(0, 24)) + '</span>';
    });
    if (n) bubble('user', '📎 ' + n + ' file' + (n > 1 ? 's' : '') + '<div class="rq-thumbs">' + html + '</div>');
    if (st.step === 'photos' && n) { st.i++; nextQ(); }
  });
  attach.addEventListener('click', function() { files.click(); });
  composer.addEventListener('submit', function(e) { e.preventDefault(); if (!input.disabled) onSend(input.value); });
  input.addEventListener('keydown', function(e) { if (e.key === 'Enter' && !e.shiftKey) { e.preventDefault(); if (!input.disabled) onSend(input.value); } });
  function grow() { input.style.height = 'auto'; input.style.height = Math.min(input.scrollHeight, 120) + 'px'; }
  input.addEventListener('input', grow);

  // ---- summary ----
  function valueOf(q) {
    var a = st.ans[q.id];
    if (a === undefined || a === '__none') return 'Not yet provided';
    if (q.kind === 'choice') { for (var i = 0; i < q.options.length; i++) { if (q.options[i].v === a) return q.options[i].label; } }
    return a;
  }
  function buildSummary() {
    var c = cat(), req = [], det = [], loc = '', dims = '';
    st.qs.forEach(function(q) {
      if (q.kind === 'photos' || st.ans[q.id] === undefined) return;
      var line = q.short + ': ' + valueOf(q);
      if (q.group === 'req') req.push(line); else det.push(line);
      if (q.loc && st.ans[q.id] !== '__none') loc = st.ans[q.id];
      if (q.dims && st.ans[q.id] !== '__none') dims = st.ans[q.id];
    });
    var opts = collect('option'), safe = collect('safety'), ver = collect('verify'), nxt = collect('next', true);
    if (!opts.length) opts = ['There is not enough information yet to suggest a specific option.'];
    var sections = [
      ['Project type', [c.label + ' (' + c.topic + ')']],
      ['Your requirements', req.length ? req : ['Not yet provided']],
      ['Details you gave', det.length ? det : ['Not yet provided']],
      ['Options to consider', opts],
      ['Safety considerations', safe],
      ['Still to be confirmed', ver],
      ['Recommended next step', nxt]
    ];
    var html = '<div class="cg-sum">', text = [];
    sections.forEach(function(s) {
      html += '<h5>' + esc(s[0]) + '</h5><ul>' + s[1].map(function(x) { return '<li>' + esc(x) + '</li>'; }).join('') + '</ul>';
      text.push(s[0].toUpperCase()); s[1].forEach(function(x) { text.push('- ' + x); }); text.push('');
    });
    html += '<p class="cg-fine">General guidance only. This is not a quotation, an inspection or a confirmed measurement.</p></div>';
    text.push('General guidance only. Not a quotation, an inspection or a confirmed measurement.');
    return { html: html, text: text.join(NL), topic: c.topic, jobCat: c.job_cat, loc: loc, dims: dims };
  }
  function save() { try { sessionStorage.setItem(KEY, JSON.stringify({ cat: st.cat, ans: st.ans, danger: st.danger })); } catch (e) {} }
  function finish() {
    st.step = 'summary'; lock(); save();
    say('Thank you. Based only on what you have told us, here is a summary with some things to consider.', showSummary);
  }
  function showSummary() {
    var sm = buildSummary();
    say(sm.html, function() {
      setQuick([
        { label: 'Request Professional Assistance', primary: true, fn: requestHelp },
        { label: 'What affects the cost?', fn: function() { bubble('user', 'What affects the cost?'); say(esc(G.cost), again); } },
        { label: 'Change my answers', fn: function() { var id = st.cat, l = cat().icon + ' ' + cat().label; bubble('user', 'Change my answers'); choose(id, l); } },
        { label: 'Start over', fn: restart }
      ]);
    }, 'wide');
  }

  // ---- request ----
  function requestHelp() {
    bubble('user', 'Request Professional Assistance'); save();
    if (!CAN) {
      if (!LOGGED) {
        say('To send a request you need to log in or create a customer account. Your answers are kept on this device, so you can come back to this summary afterwards.', function() {
          setQuick([{ label: 'Log in or sign up', primary: true, fn: function() { document.getElementById('authModal').classList.add('open'); again(); } },
                    { label: 'Back to summary', fn: showSummary }]);
        });
      } else {
        say('Requests can only be sent from a customer account. You are logged in with a different type of account.', function() { setQuick([{ label: 'Back to summary', fn: showSummary }]); });
      }
      return;
    }
    review();
  }
  function review() {
    var sm = buildSummary(), n = files.files.length;
    var html = 'Before anything is sent, this is exactly what will be shared with Andy Alloy:' +
      '<div class="cg-share"><b>Your account:</b> ' + esc(UNAME) + ' (' + esc(UMAIL) + ')<br><b>Photos:</b> ' + (n ? n + ' attached' : 'none') + '</div>' +
      sm.html +
      '<label class="cg-consent-row"><input type="checkbox" class="cg-consent"> I agree to share this summary, and my account name and email, with Andy Alloy so they can follow up. I understand nothing is confirmed until Andy Alloy confirms it.</label>';
    say(html, function() { setQuick([{ label: 'Send request', primary: true, fn: sendNow }, { label: 'Back to summary', fn: showSummary }]); }, 'wide');
  }
  function sendNow() {
    var boxes = body.querySelectorAll('.cg-consent'), box = boxes[boxes.length - 1];
    if (!box || !box.checked) {
      say('Please tick the box first, so we know you are happy for this to be shared.', function() { setQuick([{ label: 'Send request', primary: true, fn: sendNow }, { label: 'Back to summary', fn: showSummary }]); });
      return;
    }
    var sm = buildSummary(), fd = new FormData();
    fd.append('csrf_token', CSRF); fd.append('category', sm.jobCat); fd.append('topic', sm.topic); fd.append('summary', sm.text);
    fd.append('location', sm.loc); fd.append('dimensions', sm.dims); fd.append('consent', '1');
    [].forEach.call(files.files, function(f) { fd.append('attachments', f); });
    st.sending = true; setQuick([]); lock();
    var wait = bubble('andy', 'Sending your request…');
    function fail(msg) {
      st.sending = false; wait.remove();
      bubble('andy', esc(msg), 'cg-warn'); down();
      setQuick([{ label: 'Try again', primary: true, fn: sendNow }, { label: 'Back to summary', fn: showSummary }]);
    }
    fetch(SUBMIT_URL, { method: 'POST', headers: { 'X-Requested-With': 'fetch' }, body: fd, credentials: 'same-origin' })
      .then(function(r) { return r.json().then(function(d) { return { ok: r.ok, d: d }; }, function() { return { ok: false, d: null }; }); })
      .then(function(res) {
        if (res.ok && res.d && res.d.ok) {
          st.sending = false; wait.remove();
          try { sessionStorage.removeItem(KEY); } catch (e) {}
          bubble('andy', esc(res.d.message)); down();
          setQuick([{ label: 'Open the conversation', primary: true, fn: function() { location.href = res.d.url; } }]);
        } else if (res.d && res.d.message) { fail(res.d.message + (/nothing/i.test(res.d.message) ? '' : ' Nothing was sent.')); }
        else { fail('Your session may have expired. Please refresh the page and try again. Nothing was sent.'); }
      })
      .catch(function() { fail('We could not reach the server. Nothing was sent. Please check your connection and try again.'); });
  }

  // ---- start ----
  var saved = null;
  try { saved = JSON.parse(sessionStorage.getItem(KEY) || 'null'); } catch (e) { saved = null; }
  if (saved && saved.cat && G.questions[saved.cat]) {
    st.cat = saved.cat; st.ans = saved.ans || {}; st.danger = saved.danger || {};
    st.qs = (G.questions[st.cat] || []).concat(G.questions.common); st.step = 'summary';
    say('Welcome back. Your answers were kept. Here is your summary.', showSummary);
  } else {
    sayAll([
      { html: 'Welcome to the Andy Alloy guided consultation. We will ask a few short questions, then give you practical guidance and what still needs checking. Nothing here is a quotation, an inspection or a confirmed measurement.' },
      { html: '<b>Your safety comes first.</b> Our guidance helps you understand your options and make informed decisions. Some projects require professional measurements, an on-site assessment, or specialist installation. Do not attempt work that could put you or others at risk.', cls: 'cg-safe' }
    ], showCats);
  }
})();
</script>
{% endblock %}
''',

"services.html": '''{% extends "base.html" %}
{% block title %}Explore Services | ANDY{% endblock %}
{% block content %}
{% macro rq_link(cat, label, cls) -%}
{% if user and user.role == 'customer' %}<a class="{{ cls }}" href="{{ url_for('request_service', category=cat) }}">{{ label }}</a>{% elif not user %}<a class="{{ cls }}" href="#" onclick="document.getElementById('authModal').classList.add('open');return false;">{{ label }}</a>{% endif %}
{%- endmacro %}
<div class="svcp-head">
  <span class="lp-eyebrow">Explore services</span>
  <h1 class="lp-title">Aluminium doors, windows, partitions and more</h1>
  <p class="lp-lead">Browse what we make and fix, see what each is suited to, and ask for advice if you are not sure what fits your building. Tap a photo to see it full size.</p>
</div>

{% if user and user.role == 'owner' %}
<details class="svcp-upload" id="add" {{ 'open' if add_cat }}>
  <summary>＋ Add photos to the catalogue</summary>
  <form method="POST" action="{{ url_for('services_add') }}" enctype="multipart/form-data" class="auth-form"><input type="hidden" name="csrf_token" value="{{ csrf_token() }}">
    <select name="category" required aria-label="Category">
      {% for c in product_categories %}<option value="{{ c }}" {{ 'selected' if c == add_cat }}>{{ c }}</option>{% endfor %}
    </select>
    <input type="text" name="name" placeholder="Name (e.g. 3-panel sliding window)" maxlength="120" required>
    <input type="number" name="price" min="0" step="500" placeholder="Price in ₦ (leave empty or 0 to show 'Ask for a quote')">
    <textarea name="description" rows="2" maxlength="600" placeholder="Short description (optional)"></textarea>
    <input type="file" name="images" accept=".jpg,.jpeg,.png,.webp" multiple required>
    <p class="media-hint">You can choose several photos at once. Each one becomes its own item and also appears in the Catalogue.</p>
    <button class="btn btn-purple" type="submit">Upload</button>
  </form>
</details>
{% endif %}

{% for sv in sections %}
<section class="svcp-sec" id="{{ sv.slug }}">
  <div class="svcp-sec-head">
    <div class="svcp-art">{% if sv.art is not none %}{{ service_art[sv.art]|safe }}{% else %}<span class="svcp-emoji">🛠️</span>{% endif %}</div>
    <div class="svcp-sec-text">
      <h2>{{ sv.name }}</h2>
      <p>{{ sv.blurb }}</p>
      <dl class="svcp-info">
        <div><dt>Suited to</dt><dd>{{ sv.good_for }}</dd></div>
        <div><dt>Consider</dt><dd>{{ sv.consider }}</dd></div>
      </dl>
      <div class="svcp-actions">
        {{ rq_link(sv.job_cat, 'Request ' ~ (sv.name|lower), 'btn btn-purple') }}
        {% if sv['items']|selectattr('price', 'gt', 0)|list %}<a class="btn btn-outline" href="{{ url_for('catalog', cat=sv.cat) }}">Order from catalogue</a>{% endif %}
        {% if user and user.role == 'owner' %}<a class="btn btn-outline" href="{{ url_for('services', add=sv.cat) }}#add">＋ Add photos</a>{% endif %}
      </div>
    </div>
  </div>

  {% if sv['items'] %}
  <div class="svcp-grid">
    {% for p in sv['items'] %}
    <figure class="svcp-item">
      {% if p.image_filename %}
        {% set pu = p.image_filename|photo_url("products") %}
        <div class="pimg" style="--bg:url('{{ pu }}');"><img src="{{ pu }}" alt="{{ p.name }}" loading="lazy" data-lightbox="svc-{{ sv.slug }}" data-full="{{ pu }}" data-caption="{{ p.name }}" onerror="this.closest('.pimg').classList.add('pimg-broken')"></div>
      {% elif p.video_url %}
        <video class="pvideo" controls muted preload="metadata" src="{{ p.video_url|photo_url('products') }}#t=0.1"></video>
      {% else %}
        <div class="pimg pimg-art">{{ category_graphic(p.category)|safe }}</div>
      {% endif %}
      <figcaption>
        <b>{{ p.name }}</b>
        <span>{% if p.price > 0 %}₦{{ "{:,}".format(p.price) }}{% else %}Ask for a quote{% endif %}</span>
        <details class="svcp-more">
          <summary>Details</summary>
          <p>{{ p.description or 'Ask us for more details about this one.' }}</p>
          {{ rq_link(sv.job_cat, 'Ask about this →', 'svcp-ask') }}
        </details>
        {% if user and user.role == 'owner' %}
        <form method="POST" action="{{ url_for('delete_product', product_id=p.id) }}" onsubmit="return confirm('Remove this photo?');"><input type="hidden" name="csrf_token" value="{{ csrf_token() }}"><input type="hidden" name="next" value="{{ url_for('services') }}#{{ sv.slug }}"><button class="svcp-del" type="submit">Remove</button></form>
        {% endif %}
      </figcaption>
    </figure>
    {% endfor %}
  </div>
  {% else %}
  <div class="empty-state svcp-empty">Photos of our {{ sv.name|lower }} are coming soon.{% if user and user.role == 'owner' %} <a href="{{ url_for('services', add=sv.cat) }}#add" style="color:var(--accent);font-weight:700;">Add the first photos</a>{% endif %}</div>
  {% endif %}
</section>
{% endfor %}

<section class="cons" id="consultation" aria-labelledby="consTitle">
  <div class="cons-intro">
    <span class="lp-eyebrow">Consultation</span>
    <h2 id="consTitle">Professional Aluminium Consultation</h2>
    <p>Not sure which door, window or partition suits your building? Answer a few guided questions about your project and get practical guidance on your options, what still needs to be checked, and the safe next step.</p>
    <p class="cons-prep-title">Helpful to have ready</p>
    <ul class="cons-prep">
      <li>Where the work is, and what the space is used for</li>
      <li>Photos of the opening from inside and outside</li>
      <li>Rough width and height, only if you can measure safely from the floor</li>
      <li>Any concerns about security, ventilation or weather</li>
    </ul>
  </div>
  <div class="cons-safety" role="note">
    <b>Your safety comes first.</b> Our guidance helps you understand your options and make informed decisions. Some projects require professional measurements, an on-site assessment, or specialist installation. Do not attempt work that could put you or others at risk.
    <span>Never climb, lean out of a window, or remove glass or frames just to take a measurement. Heavy glass and sharp aluminium edges can cause serious injury.</span>
  </div>

  <div class="cons-start">
    <a class="btn btn-purple cons-submit" href="{{ url_for('consult_guide') }}">Start your consultation</a>
    <span class="cons-hint">A few guided questions, one at a time. You only need an account when you send a request.</span>
  </div>
</section>

<div class="svcp-foot">
  <h3>Ready to Discuss Your Project?</h3>
  <p>Tell us what you need and we will take it from there.</p>
  {{ rq_link('', 'Request a Service', 'btn btn-purple') }}
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
    <input type="text" name="name" value="{{ user.name }}" placeholder="Your name" maxlength="60" required>
    <textarea name="bio" placeholder="Add a short bio (optional)" rows="3" maxlength="500">{{ user.bio }}</textarea>
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
<p style="font-size:13px;color:var(--text-muted);margin-bottom:10px;">Messages from Andy or your artisan that need your attention.</p>
{% if user.role == 'customer' %}<a href="{{ url_for('my_jobs') }}" style="display:inline-block;font-size:13px;font-weight:600;color:var(--accent);margin-bottom:14px;">See all my requests and their status →</a>{% endif %}

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
<p style="font-size:13px;color:var(--text-muted);margin-bottom:16px;">A quick estimate for quoting. Always confirm the real opening with a tape measure before cutting anything.</p>

<div id="step-camera" class="measure-step">
  <div class="info-card" style="margin-bottom:14px;">
    <b>For an accurate reading:</b>
    <ol style="margin:8px 0 0 18px;padding:0;font-size:13px;line-height:1.7;">
      <li>Stick or hold a flat <b>A4 sheet</b> on the glass or frame, <b>in the same plane as the window</b>, near the middle.</li>
      <li>Stand <b>2 to 3 metres back</b>, directly in front, so the whole window and the sheet are in the photo.</li>
      <li>Use the normal 1x camera. <b>Not ultra-wide</b> (0.5x), it bends the edges.</li>
      <li>Good light, no blur.</li>
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
      <input type="file" id="uploadFallback" accept="image/*" style="display:none;" onchange="handleUpload(event)">
    </label>
  </div>
  <p id="cameraError" style="font-size:12px;color:var(--gold);margin-top:8px;display:none;">Couldn't access your camera. Use "Upload a photo instead."</p>
</div>

<div id="step-reference" class="measure-step" style="display:none;">
  <div class="info-card" style="margin-bottom:12px;">
    <b>Step 2: Mark your reference</b>
    <select id="referenceSelect" onchange="onReferenceChange()" style="margin-top:8px;width:100%;padding:10px;border:1px solid var(--border);border-radius:8px;">
      {% for r in references %}
        <option value="{{ r.id }}" data-mode="{{ r.mode }}" data-w="{{ r.w or '' }}" data-h="{{ r.h or '' }}">{{ r.label }}</option>
      {% endfor %}
    </select>
    <div id="customRectBox" style="display:none;gap:8px;margin-top:8px;">
      <input type="number" id="customW" step="0.1" placeholder="Width cm" style="flex:1;padding:10px;border:1px solid var(--border);border-radius:8px;">
      <input type="number" id="customH" step="0.1" placeholder="Height cm" style="flex:1;padding:10px;border:1px solid var(--border);border-radius:8px;">
    </div>
    <input type="number" id="customLen" step="0.1" placeholder="Exact length in cm" style="display:none;margin-top:8px;width:100%;padding:10px;border:1px solid var(--border);border-radius:8px;">
    <p id="refInstruction" style="font-size:13px;margin-top:10px;"></p>
  </div>
  <canvas id="photoCanvas"></canvas>
  <div style="display:flex;gap:8px;margin-top:8px;">
    <button type="button" class="btn btn-outline" style="flex:1;" onclick="refEditor.undo()">Undo</button>
    <button type="button" class="btn btn-outline" style="flex:1;" onclick="refEditor.reset()">Start over</button>
  </div>
  <p style="font-size:12px;color:var(--text-muted);margin-top:8px;">Tip: tap to drop a point, then drag it to fine-tune. A magnifier shows while you drag.</p>
  <button type="button" class="btn btn-purple" id="toEdgesBtn" onclick="goToEdges()" disabled style="margin-top:10px;width:100%;">Next: mark the window corners</button>
</div>

<div id="step-edges" class="measure-step" style="display:none;">
  <p id="edgeInstruction" class="info-card" style="margin-bottom:12px;font-size:13px;"></p>
  <canvas id="photoCanvas2"></canvas>
  <div style="display:flex;gap:8px;margin-top:8px;">
    <button type="button" class="btn btn-outline" style="flex:1;" onclick="winEditor.undo()">Undo</button>
    <button type="button" class="btn btn-outline" style="flex:1;" onclick="winEditor.reset()">Start over</button>
  </div>
  <button type="button" class="btn btn-purple" id="calcBtn" onclick="calculateMeasurement()" disabled style="width:100%;margin-top:10px;">Calculate</button>
</div>

<div id="step-result" class="measure-step" style="display:none;">
  <div id="confidenceBanner" class="info-card" style="display:none;background:rgba(217,166,61,0.1);border-color:var(--gold);">
    <b>⚠️ Low-confidence estimate</b>
    <ul id="confidenceReasons" style="font-size:12px;margin:6px 0 0 16px;padding:0;"></ul>
  </div>
  <div class="settings-card">
    <div class="settings-card-title">Estimated Measurement</div>
    <div style="font-size:28px;font-family:'Poppins',sans-serif;font-weight:700;margin:10px 0;">
      <span id="resultWidth">0</span> cm × <span id="resultHeight">0</span> cm
    </div>
    <p id="accuracyLine" style="font-size:13px;margin-bottom:6px;"></p>
    <p style="font-size:12px;color:var(--text-muted);">Width × height. Confirm the actual opening with a tape measure before fabrication.</p>
  </div>

  <div class="settings-card">
    <div class="settings-card-title">Check against a tape (optional)</div>
    <p style="font-size:12px;color:var(--text-muted);margin:4px 0 8px;">Measured the real window? Enter it to see how far off this estimate is.</p>
    <div style="display:flex;gap:8px;">
      <input type="number" id="actualW" step="0.1" placeholder="Real width cm" oninput="checkActual()" style="flex:1;padding:10px;border:1px solid var(--border);border-radius:8px;">
      <input type="number" id="actualH" step="0.1" placeholder="Real height cm" oninput="checkActual()" style="flex:1;padding:10px;border:1px solid var(--border);border-radius:8px;">
    </div>
    <p id="actualResult" style="font-size:13px;margin-top:8px;"></p>
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
    <textarea name="notes" id="formNotes" placeholder="Notes (optional)" rows="2"></textarea>
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
var photoImg = null;
var refEditor = null, winEditor = null;

if (navigator.mediaDevices && navigator.mediaDevices.getUserMedia) {
  navigator.mediaDevices.getUserMedia({ video: { facingMode: 'environment', width: { ideal: 1920 }, height: { ideal: 1080 } } })
    .then(function(s) { stream = s; video.srcObject = s; })
    .catch(function() { document.getElementById('cameraError').style.display = 'block'; });
} else {
  document.getElementById('cameraError').style.display = 'block';
}

function capturePhoto() {
  var canvas = document.createElement('canvas');
  canvas.width = video.videoWidth || 640;
  canvas.height = video.videoHeight || 480;
  canvas.getContext('2d').drawImage(video, 0, 0, canvas.width, canvas.height);
  var url = canvas.toDataURL('image/jpeg', 0.92);
  flashCaptureSuccess();
  if (stream) { stream.getTracks().forEach(function(t){ t.stop(); }); }
  setTimeout(function() { showReferenceStep(url); }, 650);
}

function handleUpload(evt) {
  var file = evt.target.files[0];
  if (!file) return;
  var reader = new FileReader();
  reader.onload = function(e) { showReferenceStep(e.target.result); };
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

// Downscale big phone photos (keeps uploads small) and bake in orientation.
function normalizeImage(dataUrl, cb) {
  var img = new Image();
  img.onload = function() {
    var s = Math.min(1, 1600 / Math.max(img.width, img.height));
    var c = document.createElement('canvas');
    c.width = Math.round(img.width * s);
    c.height = Math.round(img.height * s);
    c.getContext('2d').drawImage(img, 0, 0, c.width, c.height);
    capturedDataUrl = c.toDataURL('image/jpeg', 0.9);
    photoImg = new Image();
    photoImg.onload = cb;
    photoImg.src = capturedDataUrl;
  };
  img.src = dataUrl;
}

// ---------------------------------------------------------------------
// Geometry. A homography maps the photo plane onto the real (cm) plane,
// which removes the error caused by photographing at an angle.
// ---------------------------------------------------------------------
function solveLinear(A, b) {
  var n = b.length, i, j, k;
  for (i = 0; i < n; i++) A[i].push(b[i]);
  for (i = 0; i < n; i++) {
    var p = i;
    for (j = i + 1; j < n; j++) if (Math.abs(A[j][i]) > Math.abs(A[p][i])) p = j;
    if (Math.abs(A[p][i]) < 1e-10) return null;
    var tmp = A[i]; A[i] = A[p]; A[p] = tmp;
    for (j = i + 1; j < n; j++) {
      var f = A[j][i] / A[i][i];
      for (k = i; k <= n; k++) A[j][k] -= f * A[i][k];
    }
  }
  var x = new Array(n);
  for (i = n - 1; i >= 0; i--) {
    var sum = A[i][n];
    for (j = i + 1; j < n; j++) sum -= A[i][j] * x[j];
    x[i] = sum / A[i][i];
  }
  return x;
}
function homography(src, dst) {
  var A = [], b = [], i;
  for (i = 0; i < 4; i++) {
    var x = src[i].x, y = src[i].y, u = dst[i].x, v = dst[i].y;
    A.push([x, y, 1, 0, 0, 0, -u * x, -u * y]); b.push(u);
    A.push([0, 0, 0, x, y, 1, -v * x, -v * y]); b.push(v);
  }
  return solveLinear(A, b);
}
function applyH(h, p) {
  var d = h[6] * p.x + h[7] * p.y + 1;
  return { x: (h[0] * p.x + h[1] * p.y + h[2]) / d, y: (h[3] * p.x + h[4] * p.y + h[5]) / d };
}
function dist(a, b) { return Math.sqrt((a.x - b.x) * (a.x - b.x) + (a.y - b.y) * (a.y - b.y)); }
function cornerAngle(c, a, b) {
  var v1x = a.x - c.x, v1y = a.y - c.y, v2x = b.x - c.x, v2y = b.y - c.y;
  var cos = (v1x * v2x + v1y * v2y) / (Math.sqrt(v1x * v1x + v1y * v1y) * Math.sqrt(v2x * v2x + v2y * v2y));
  return Math.acos(Math.max(-1, Math.min(1, cos))) * 180 / Math.PI;
}

// ---------------------------------------------------------------------
// Point editor: tap to place, drag to adjust, magnifier while dragging.
// ---------------------------------------------------------------------
function PointEditor(canvas, labels, onChange) {
  var self = this;
  self.canvas = canvas; self.labels = labels; self.pts = []; self.active = -1; self.onChange = onChange;
  var w = Math.min(560, window.innerWidth - 44);
  canvas.width = w;
  canvas.height = Math.round(photoImg.height * w / photoImg.width);
  canvas.style.width = w + 'px';
  self.scale = w / photoImg.width;

  function pos(e) {
    var r = canvas.getBoundingClientRect();
    return { x: (e.clientX - r.left) * canvas.width / r.width, y: (e.clientY - r.top) * canvas.height / r.height };
  }
  canvas.onpointerdown = function(e) {
    e.preventDefault();
    var p = pos(e), best = -1, bd = 30, i;
    for (i = 0; i < self.pts.length; i++) { var d = dist(p, self.pts[i]); if (d < bd) { bd = d; best = i; } }
    if (best < 0 && self.pts.length < self.labels.length) { self.pts.push(p); best = self.pts.length - 1; }
    self.active = best;
    try { canvas.setPointerCapture(e.pointerId); } catch (err) {}
    self.draw();
  };
  canvas.onpointermove = function(e) {
    if (self.active < 0) return;
    e.preventDefault();
    var p = pos(e);
    self.pts[self.active] = { x: Math.max(0, Math.min(canvas.width, p.x)), y: Math.max(0, Math.min(canvas.height, p.y)) };
    self.draw();
  };
  canvas.onpointerup = canvas.onpointercancel = function() {
    self.active = -1; self.draw(); self.onChange();
  };
  self.draw();
}
PointEditor.prototype.imgPts = function() {
  var s = this.scale;
  return this.pts.map(function(p) { return { x: p.x / s, y: p.y / s }; });
};
PointEditor.prototype.complete = function() { return this.pts.length === this.labels.length; };
PointEditor.prototype.undo = function() { this.pts.pop(); this.draw(); this.onChange(); };
PointEditor.prototype.reset = function() { this.pts = []; this.draw(); this.onChange(); };
PointEditor.prototype.draw = function() {
  var c = this.canvas, ctx = c.getContext('2d'), pts = this.pts, i;
  ctx.drawImage(photoImg, 0, 0, c.width, c.height);
  ctx.lineWidth = 2; ctx.strokeStyle = '#22C55E'; ctx.fillStyle = '#22C55E';
  if (pts.length > 1) {
    ctx.beginPath(); ctx.moveTo(pts[0].x, pts[0].y);
    for (i = 1; i < pts.length; i++) ctx.lineTo(pts[i].x, pts[i].y);
    if (this.labels.length === 4 && pts.length === 4) ctx.closePath();
    ctx.stroke();
  }
  ctx.font = 'bold 12px sans-serif';
  for (i = 0; i < pts.length; i++) {
    ctx.beginPath(); ctx.arc(pts[i].x, pts[i].y, 6, 0, 7); ctx.fill();
    ctx.fillStyle = '#fff'; ctx.fillText(this.labels[i], pts[i].x + 9, pts[i].y - 8); ctx.fillStyle = '#22C55E';
  }
  if (this.active >= 0) {
    var p = pts[this.active], r = 46, z = 3;
    var lx = p.x < c.width / 2 ? c.width - r - 8 : r + 8;
    var ly = p.y < 130 ? c.height - r - 8 : r + 8;
    ctx.save();
    ctx.beginPath(); ctx.arc(lx, ly, r, 0, 7); ctx.clip();
    var half = (r / z) / this.scale;
    ctx.drawImage(photoImg, p.x / this.scale - half, p.y / this.scale - half, half * 2, half * 2, lx - r, ly - r, r * 2, r * 2);
    ctx.restore();
    ctx.strokeStyle = '#fff'; ctx.lineWidth = 3; ctx.beginPath(); ctx.arc(lx, ly, r, 0, 7); ctx.stroke();
    ctx.strokeStyle = '#22C55E'; ctx.lineWidth = 1;
    ctx.beginPath(); ctx.moveTo(lx - 10, ly); ctx.lineTo(lx + 10, ly); ctx.moveTo(lx, ly - 10); ctx.lineTo(lx, ly + 10); ctx.stroke();
  }
};

// ---------------------------------------------------------------------
// Steps
// ---------------------------------------------------------------------
function refInfo() {
  var sel = document.getElementById('referenceSelect');
  var opt = sel.selectedOptions[0];
  var mode = opt.getAttribute('data-mode');
  var w = parseFloat(opt.getAttribute('data-w')) || 0, h = parseFloat(opt.getAttribute('data-h')) || 0;
  if (sel.value === 'custom_rect') { w = parseFloat(document.getElementById('customW').value) || 0; h = parseFloat(document.getElementById('customH').value) || 0; }
  var len = mode === 'line' ? (parseFloat(document.getElementById('customLen').value) || 0) : 0;
  return { mode: mode, w: w, h: h, len: len, label: opt.textContent };
}

function showReferenceStep(dataUrl) {
  normalizeImage(dataUrl, function() {
    document.getElementById('step-camera').style.display = 'none';
    document.getElementById('step-reference').style.display = 'block';
    onReferenceChange();
  });
}

function onReferenceChange() {
  var sel = document.getElementById('referenceSelect');
  var info = refInfo();
  document.getElementById('customRectBox').style.display = sel.value === 'custom_rect' ? 'flex' : 'none';
  document.getElementById('customLen').style.display = info.mode === 'line' ? 'block' : 'none';
  var labels = info.mode === 'line' ? ['1', '2'] : ['1 TL', '2 TR', '3 BR', '4 BL'];
  document.getElementById('refInstruction').innerHTML = info.mode === 'line'
    ? 'Tap the <b>two ends</b> of your known length. <i>Less accurate: only works well if you photographed straight-on.</i>'
    : 'Tap the <b>4 corners</b> of the reference in order: <b>top-left, top-right, bottom-right, bottom-left</b> (as it looks in the photo).';
  refEditor = new PointEditor(document.getElementById('photoCanvas'), labels, checkReferenceReady);
  checkReferenceReady();
}

function checkReferenceReady() {
  var info = refInfo();
  var dimsOk = info.mode === 'line' ? info.len > 0 : (info.w > 0 && info.h > 0);
  document.getElementById('toEdgesBtn').disabled = !(refEditor && refEditor.complete() && dimsOk);
}
['customW', 'customH', 'customLen'].forEach(function(id) { document.getElementById(id).addEventListener('input', checkReferenceReady); });

function goToEdges() {
  document.getElementById('step-reference').style.display = 'none';
  document.getElementById('step-edges').style.display = 'block';
  document.getElementById('edgeInstruction').innerHTML = 'Tap the <b>4 inside corners of the window opening</b> in order: <b>top-left, top-right, bottom-right, bottom-left</b>. Drag to fine-tune.';
  winEditor = new PointEditor(document.getElementById('photoCanvas2'), ['1 TL', '2 TR', '3 BR', '4 BL'], function() {
    document.getElementById('calcBtn').disabled = !winEditor.complete();
  });
}

var lastResult = null;

function calculateMeasurement() {
  var info = refInfo();
  var rp = refEditor.imgPts(), wp = winEditor.imgPts();
  var widthCm, heightCm, reasons = [], refLen, minRefSide, relErr;

  if (info.mode === 'rect') {
    var top = dist(rp[0], rp[1]), bottom = dist(rp[3], rp[2]), left = dist(rp[0], rp[3]), right = dist(rp[1], rp[2]);
    var longer = Math.max(info.w, info.h), shorter = Math.min(info.w, info.h);
    var rw = ((top + bottom) / 2) >= ((left + right) / 2) ? longer : shorter;
    var rh = rw === longer ? shorter : longer;
    var H = homography(rp, [{ x: 0, y: 0 }, { x: rw, y: 0 }, { x: rw, y: rh }, { x: 0, y: rh }]);
    if (!H) { alert('Those reference corners do not form a valid shape. Please mark them again.'); return; }
    var q = wp.map(function(p) { return applyH(H, p); });
    var tC = dist(q[0], q[1]), bC = dist(q[3], q[2]), lC = dist(q[0], q[3]), rC = dist(q[1], q[2]);
    widthCm = (tC + bC) / 2; heightCm = (lC + rC) / 2;
    minRefSide = Math.min(top, bottom, left, right);
    // A tiny reference makes the angle correction unstable, so fall back to a plain scale.
    var simpleK = (rw / ((top + bottom) / 2) + rh / ((left + right) / 2)) / 2;
    var simpleW = (dist(wp[0], wp[1]) + dist(wp[3], wp[2])) / 2 * simpleK;
    var simpleH = (dist(wp[0], wp[3]) + dist(wp[1], wp[2])) / 2 * simpleK;
    var unstable = !isFinite(widthCm) || !isFinite(heightCm) || minRefSide < 55 ||
      Math.abs(widthCm - simpleW) / simpleW > 0.25 || Math.abs(heightCm - simpleH) / simpleH > 0.25;
    if (unstable) {
      widthCm = simpleW; heightCm = simpleH;
      reasons.push('The reference is too small in the photo to correct for camera angle. Move closer, or use an A4 sheet.');
    }
    var angDev = Math.max(
      Math.abs(cornerAngle(q[0], q[1], q[3]) - 90), Math.abs(cornerAngle(q[1], q[0], q[2]) - 90),
      Math.abs(cornerAngle(q[2], q[1], q[3]) - 90), Math.abs(cornerAngle(q[3], q[0], q[2]) - 90));
    var mism = Math.max(Math.abs(tC - bC) / widthCm, Math.abs(lC - rC) / heightCm);
    if (!unstable && (angDev > 15 || mism > 0.25)) reasons.push('The window corners do not look square once corrected. The reference may not be flat on the window plane, or a corner is misplaced.');
    refLen = rw;
  } else {
    var refPx = dist(rp[0], rp[1]);
    var k = info.len / refPx;
    widthCm = (dist(wp[0], wp[1]) + dist(wp[3], wp[2])) / 2 * k;
    heightCm = (dist(wp[0], wp[3]) + dist(wp[1], wp[2])) / 2 * k;
    minRefSide = refPx;
    refLen = info.len;
    reasons.push('A single known length cannot correct for camera angle. Use an A4 sheet for better accuracy.');
  }

  relErr = 2.5 / Math.max(minRefSide, 1);
  var errCm = Math.max(0.5, Math.round(Math.max(widthCm, heightCm) * relErr * 2) / 2);
  lastResult = { w: widthCm, h: heightCm };

  document.getElementById('resultWidth').textContent = widthCm.toFixed(1);
  document.getElementById('resultHeight').textContent = heightCm.toFixed(1);
  document.getElementById('accuracyLine').textContent = 'Typical accuracy: about ± ' + errCm + ' cm.';
  var banner = document.getElementById('confidenceBanner');
  var list = document.getElementById('confidenceReasons');
  list.innerHTML = '';
  reasons.forEach(function(t) { var li = document.createElement('li'); li.textContent = t; list.appendChild(li); });
  banner.style.display = reasons.length ? 'block' : 'none';

  document.getElementById('formWidth').value = widthCm.toFixed(1);
  document.getElementById('formHeight').value = heightCm.toFixed(1);
  document.getElementById('formRefCm').value = refLen;
  document.getElementById('formRefLabel').value = info.label;
  document.getElementById('formConfidence').value = reasons.length ? 'low' : 'normal';
  document.getElementById('formPhotoData').value = capturedDataUrl;

  document.getElementById('step-edges').style.display = 'none';
  document.getElementById('step-result').style.display = 'block';
}

function checkActual() {
  var aw = parseFloat(document.getElementById('actualW').value), ah = parseFloat(document.getElementById('actualH').value);
  var out = document.getElementById('actualResult'), parts = [];
  if (aw > 0) parts.push('Width off by ' + (lastResult.w - aw).toFixed(1) + ' cm (' + ((lastResult.w - aw) / aw * 100).toFixed(1) + '%)');
  if (ah > 0) parts.push('Height off by ' + (lastResult.h - ah).toFixed(1) + ' cm (' + ((lastResult.h - ah) / ah * 100).toFixed(1) + '%)');
  out.textContent = parts.join(' · ');
  var notes = document.getElementById('formNotes');
  if (parts.length && notes.value.indexOf('[Tape check]') < 0) notes.value = (notes.value ? notes.value + ' ' : '') + '[Tape check: ' + (aw > 0 ? 'W ' + aw : '') + (ah > 0 ? ' H ' + ah : '') + ' cm]';
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
<p class="works-intro">Tap a photo to see it full size, or press play on a video (sound on). Like a job, and logged-in customers can rate it and tell us what they think.</p>

{% if is_owner_view %}
  <div class="post-composer">
    <form method="POST" action="{{ url_for('works') }}" enctype="multipart/form-data" class="auth-form"><input type="hidden" name="csrf_token" value="{{ csrf_token() }}">
      <input type="text" name="title" placeholder="Project title" required>
      <select name="category"><option value="">Category (optional)</option>{% for c in categories %}<option value="{{ c }}">{{ c }}</option>{% endfor %}</select>
      <textarea name="description" placeholder="What was the job?" rows="2"></textarea>
      <input type="file" name="photos" accept=".jpg,.jpeg,.png,.webp,.mp4,.mov,.webm,.m4v" multiple data-maxmb="95">
      <p class="media-hint">Photos and videos. Videos keep their sound. Under 95 MB each, MP4 works best.</p>
      <button class="btn btn-purple" type="submit">Post this work</button>
    </form>
  </div>
  <a href="{{ url_for('admin_works') }}" style="display:block;font-size:13px;color:var(--accent);font-weight:600;margin:8px 0 14px;">Review work from artisans{% if pending_work_count %} ({{ pending_work_count }} waiting){% endif %} →</a>
{% endif %}

{% for w in work_posts %}
  <article class="feed-post work-post" id="work-{{ w.id }}">
    <div class="job-title" style="margin-bottom:6px;">{{ w.title }}{% if w.category %} <span class="work-tag">{{ w.category }}</span>{% endif %}</div>
    {% if w.description %}<div class="feed-post-caption">{{ w.description }}</div>{% endif %}

    {% if w.photos %}
      <div class="gal {{ 'single' if w.photos|length == 1 }}">
        {% for ph in w.photos %}
          {% set pu = ph.filename|photo_url("works") %}
          {% if ph.kind == 'video' %}
            <video class="gal-video" src="{{ pu }}#t=0.1" controls playsinline preload="metadata"></video>
          {% else %}
            <img src="{{ pu }}" alt="{{ w.title }}" loading="lazy" data-lightbox="work{{ w.id }}" data-full="{{ pu }}" data-caption="{{ w.title }}" data-reviews="reviews-{{ w.id }}">
          {% endif %}
        {% endfor %}
      </div>
    {% endif %}

    <div class="work-reviews" id="reviews-{{ w.id }}">
      <div class="work-actions">
        <button type="button" class="like-btn {{ 'liked' if w.liked }}" data-url="{{ url_for('work_like', work_id=w.id) }}" aria-label="Like this job"><span class="like-icon">{{ '♥' if w.liked else '♡' }}</span> <span class="like-count">{{ w.like_count }}</span></button>
      </div>
      <button type="button" class="rev-toggle" onclick="toggleReviews('reviews-{{ w.id }}')">
        {% if w.review_count %}
          {% set full = w.avg_rating|round|int %}<span class="rev-stars">{{ '★' * full }}{{ '☆' * (5 - full) }}</span>
          <b>{{ '%.1f'|format(w.avg_rating) }}</b> · {{ w.review_count }} review{{ '' if w.review_count == 1 else 's' }}
        {% else %}
          ☆☆☆☆☆ No reviews yet
        {% endif %}
        <span class="rev-cta">Read or add yours</span>
      </button>

      <div class="rev-panel" hidden>
        {% for r in w.reviews %}
          <div class="rev-item">
            <div class="rev-head"><b>{{ r.display_name }}</b><span class="rev-stars">{{ '★' * r.rating }}{{ '☆' * (5 - r.rating) }}</span>
              {% if is_owner_view or (user and user.id == r.user_id) %}
                <form method="POST" action="{{ url_for('work_review_delete', review_id=r.id) }}" onsubmit="return confirm('Delete this review?');" style="margin-left:auto;"><input type="hidden" name="csrf_token" value="{{ csrf_token() }}"><button class="rev-del" type="submit">Delete</button></form>
              {% endif %}
            </div>
            {% if r.text %}<div class="rev-text">{{ r.text }}</div>{% endif %}
            <button type="button" class="like-btn like-sm {{ 'liked' if r.liked }}" data-url="{{ url_for('work_review_like', review_id=r.id) }}" aria-label="Like this review"><span class="like-icon">{{ '♥' if r.liked else '♡' }}</span> <span class="like-count">{{ r.like_count }}</span></button>
          </div>
        {% endfor %}
        {% if not w.reviews %}<div class="rev-empty">Be the first to say what you think.</div>{% endif %}

        {% if user and user.role == 'customer' %}
          <form method="POST" action="{{ url_for('work_review', work_id=w.id) }}" class="rev-form"><input type="hidden" name="csrf_token" value="{{ csrf_token() }}">
            <div class="rev-form-title">{{ 'Update your review' if w.my_review else 'Rate this job' }}</div>
            <div class="stars-input">
              {% for n in [5, 4, 3, 2, 1] %}
                <input type="radio" id="s{{ n }}-{{ w.id }}" name="rating" value="{{ n }}" {{ 'checked' if w.my_review and w.my_review.rating == n }} required><label for="s{{ n }}-{{ w.id }}" title="{{ n }} star{{ '' if n == 1 else 's' }}">★</label>
              {% endfor %}
            </div>
            <textarea name="text" rows="3" maxlength="500" placeholder="What do you think about this job? (optional)">{{ w.my_review.text if w.my_review else '' }}</textarea>
            <button class="btn btn-purple" type="submit">{{ 'Update review' if w.my_review else 'Post review' }}</button>
          </form>
        {% elif user %}
          <div class="rev-empty">Only customers can leave reviews.</div>
        {% else %}
          <button class="btn btn-purple" type="button" onclick="document.getElementById('authModal').classList.add('open')">Sign up or log in to review</button>
        {% endif %}
      </div>
    </div>

    {% if is_owner_view %}
      <form method="POST" action="{{ url_for('delete_work', work_id=w.id) }}" style="margin-top:12px;" onsubmit="return confirm('Remove this work and its photos?');"><input type="hidden" name="csrf_token" value="{{ csrf_token() }}">
        <button class="btn btn-outline" type="submit" style="font-size:11px;padding:6px 10px;">Remove</button>
      </form>
    {% endif %}
  </article>
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
<style>body{margin:0;background:#0A1020;color:#fff;font-family:-apple-system,sans-serif;display:flex;align-items:center;justify-content:center;min-height:100vh;text-align:center;padding:20px;}.box{max-width:360px;}.logo{font-size:40px;margin-bottom:10px;}h1{font-size:22px;margin:10px 0;}p{color:#9ca3af;font-size:14px;line-height:1.6;}</style>
</head><body><div class="box"><div class="logo">🔺</div><h1>ANDY is taking a short break</h1><p>We are doing some maintenance right now. Please check back shortly.</p><p style="margin-top:28px"><a href="/staff-login" style="color:#4b5563;font-size:12px">Staff login</a></p></div></body></html>
''',

}

TEMPLATES.update(MORE_TEMPLATES_1)
TEMPLATES.update(MORE_TEMPLATES_2)
TEMPLATES.update(MORE_TEMPLATES_3)

STYLE_CSS = '''
:root {
  --purple: #6C4FD6;
  --purple-dark: #5539B8;
  --navy: #0F172A;
  --bg: #FFFFFF;
  --border: #E3E8EF;
  --text-muted: #5B6B82;
  --teal: #2E9E7C;
  --gold: #D9A63D;
  --sidebar-bg: #1B1F3B;
  --accent: #6C4FD6;
  --accent-dark: #5539B8;
  --card-bg: #FFFFFF;
  --chrome-bg: #FFFFFF;
  --chrome-text: #0F172A;
  --chrome-dim: #475569;
  --chrome-faint: #94A3B8;
  --chrome-hover: rgba(15,23,42,.05);
  --chrome-active: rgba(34,197,94,.12);
  --chrome-border: #E3E8EF;
}
body { --chrome-active: color-mix(in srgb, var(--accent) 12%, transparent); }
body.theme-teal {
  --accent: #1F8A70;
  --accent-dark: #17654F;
  --sidebar-bg: #142622;
  --gold: #D9A63D;
}
body.theme-green {
  --sidebar-bg: #0B1220;
  --accent: #22C55E;
  --accent-dark: #16A34A;
  --gold: #22C55E;
  --teal: #22C55E;
}
body.theme-green .btn-purple,
body.theme-green .btn-teal,
body.theme-green .btn-gold { color: #04140A; }
/* soft shadows keep white cards readable on a white page */
body:not(.dark-mode) :where(.card, .job-card, .feed-post, .info-card, .settings-card, .lp-card, .svc-card, .lp-work-card, .step-card, .stat-tile) {
  box-shadow: 0 1px 2px rgba(15,23,42,.05), 0 10px 30px rgba(15,23,42,.06);
}
/* ---------- dark mode (the toggle switch) ---------- */
body.dark-mode {
  --bg: #0A1020;
  --navy: #EAF1FB;
  --border: #1E2D4A;
  --text-muted: #8FA3C4;
  --sidebar-bg: #070B16;
  --card-bg: #111A2E;
  --chrome-bg: var(--sidebar-bg);
  --chrome-text: #FFFFFF;
  --chrome-dim: rgba(255,255,255,.75);
  --chrome-faint: rgba(255,255,255,.35);
  --chrome-hover: rgba(255,255,255,.06);
  --chrome-active: rgba(255,255,255,.1);
  --chrome-border: rgba(255,255,255,.08);
}
body.dark-mode .card,
body.dark-mode .job-card,
body.dark-mode .feed-post,
body.dark-mode .info-card,
body.dark-mode .video-card,
body.dark-mode .post-composer,
body.dark-mode .chat-box,
body.dark-mode .referral-box,
body.dark-mode .modal-box,
body.dark-mode .video-thumb.locked {
  background: #111A2E;
  border-color: var(--border);
  color: var(--navy);
}
body.dark-mode .msg.them { background: #17223A; }
body.dark-mode .phone-locked { background: #111A2E; }
body.dark-mode .auth-form input,
body.dark-mode .auth-form select,
body.dark-mode .auth-form textarea,
body.dark-mode .search-bar input {
  background: #111A2E;
  border-color: var(--border);
  color: var(--navy);
}
body.dark-mode .theme-option { background: #111A2E; }
body.dark-mode .close-btn { color: #8FA3C4; }
* { box-sizing: border-box; margin: 0; padding: 0; }
body {
  font-family: 'DM Sans', -apple-system, sans-serif;
  background: var(--bg);
  color: var(--navy);
}
a { text-decoration: none; color: inherit; }

.app-shell { display: flex; min-height: 100vh; }
.sidebar {
  width: 220px;
  background: var(--chrome-bg);
  color: var(--chrome-text);
  border-right: 1px solid var(--chrome-border);
  display: flex;
  flex-direction: column;
  padding: 20px 0;
  flex-shrink: 0;
}
.sidebar .logo {
  font-family: 'Poppins', sans-serif;
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
  border: 2px solid var(--chrome-bg);
  background: rgba(255,255,255,0.15);
  background: color-mix(in srgb, var(--accent) 55%, #fff);
}
.sidebar nav { flex: 1; display: flex; flex-direction: column; gap: 2px; }
.sidebar nav a, .sidebar nav button {
  display: flex; align-items: center; gap: 12px;
  padding: 11px 22px; color: var(--chrome-dim);
  font-size: 14px; background: none; border: none; width: 100%; text-align: left; cursor: pointer;
}
.sidebar nav a:hover, .sidebar nav button:hover { background: var(--chrome-hover); color: var(--chrome-text); }
.sidebar nav a.active { background: var(--chrome-active); color: var(--chrome-text); border-left: 3px solid var(--accent); }
.nav-section-label {
  font-size: 10px;
  font-weight: 700;
  letter-spacing: 0.08em;
  text-transform: uppercase;
  color: var(--chrome-faint);
  padding: 16px 22px 6px;
}
.sidebar .icon { font-size: 16px; width: 18px; text-align: center; }
.sidebar .wallet-pill {
  margin: 10px 22px; background: rgba(255,255,255,0.08); padding: 8px 12px;
  border-radius: 10px; font-size: 13px; font-family: 'IBM Plex Mono', monospace;
}
.sidebar .bottom-links a, .sidebar .bottom-links button {
  display: flex; align-items: center; gap: 12px; padding: 11px 22px; color: var(--chrome-dim);
  font-size: 14px; background: none; border: none; width: 100%; text-align: left; cursor: pointer;
}
.sidebar .bottom-links a:hover, .sidebar .bottom-links button:hover { background: var(--chrome-hover); color: var(--chrome-text); }
.sidebar .bottom-links { border-top: 1px solid var(--chrome-border); padding-top: 8px; margin-top: 8px; }

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
.hero-name { font-family: 'Poppins', sans-serif; font-weight: 700; font-size: 30px; }
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
.section-title { font-family: 'Poppins', sans-serif; font-weight: 600; font-size: 16px; margin-bottom: 12px; }

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
.sidebar-profile-name { color: var(--chrome-text); font-size: 13px; font-weight: 600; overflow: hidden; text-overflow: ellipsis; white-space: nowrap; }
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
.wallet-balance { font-family: 'Poppins', sans-serif; font-size: 32px; font-weight: 700; margin: 6px 0 16px; }
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
  font-family: 'Poppins', sans-serif; font-weight: 700; font-size: 16px;
  display: flex; align-items: center; justify-content: center; flex-shrink: 0; position: relative;
}

/* ===== Job vacancies ===== */
.job-card { background: #fff; border: 1px solid var(--border); border-radius: 14px; padding: 16px 18px; margin-bottom: 12px; }
.job-title { font-family: 'Poppins', sans-serif; font-weight: 600; font-size: 15px; }
.job-meta { font-size: 12px; color: var(--text-muted); margin: 4px 0 8px; }
.job-desc { font-size: 13px; margin-bottom: 10px; color: var(--navy); }

/* ===== Catalog ===== */
.cat-filter-row { display: flex; gap: 8px; flex-wrap: wrap; }
.cat-filter { padding: 8px 14px; border-radius: 20px; border: 1px solid var(--border); font-size: 12px; font-weight: 600; background: #fff; }
body.dark-mode .cat-filter { background: #111A2E; }
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
  /* items already in the bottom tab bar / top bar are not repeated in the slide-out menu */
  .sidebar .dup-tab, .mobile-topbar .dup-tab { display: none !important; }
  .mobile-topbar {
    display: flex;
    align-items: center;
    gap: 10px;
    position: sticky;
    top: 0;
    background: var(--chrome-bg);
    color: var(--chrome-text);
    border-bottom: 1px solid var(--chrome-border);
    padding: 14px 16px;
    z-index: 95;
  }
  .mobile-topbar-title { font-family: 'Poppins', sans-serif; font-weight: 700; flex: 1; }
  .hamburger-btn { background: none; border: none; color: var(--chrome-text); font-size: 20px; }
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
    background: var(--chrome-bg);
    border-top: 1px solid var(--chrome-border);
    z-index: 90;
  }
  .bottom-tabs a, .bottom-tabs button {
    flex: 1;
    display: flex; flex-direction: column; align-items: center; gap: 2px;
    padding: 10px 0 8px;
    color: var(--chrome-dim);
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



/* --- Notification opt-in bar --- */
.push-bar { display: flex; align-items: center; justify-content: space-between; gap: 10px; flex-wrap: wrap;
  background: linear-gradient(135deg, var(--accent), #0e5a35); color: #fff; padding: 10px 16px; font-size: 13px; font-weight: 500; }
.push-actions { display: flex; gap: 8px; }
.push-bar button { border: none; border-radius: 8px; padding: 7px 14px; font-size: 12px; font-weight: 700; cursor: pointer; background: #fff; color: #0e5a35; }
.push-bar .push-later { background: transparent; color: #fff; opacity: .85; }


/* --- Our Work review --- */
.work-tag { font-family: 'DM Sans', sans-serif; font-size: 11px; font-weight: 600; background: rgba(128,128,128,.18); border-radius: 10px; padding: 2px 8px; margin-left: 4px; vertical-align: middle; }
.work-status { font-family: 'DM Sans', sans-serif; font-size: 11px; font-weight: 700; border-radius: 10px; padding: 2px 9px; margin-left: 6px; vertical-align: middle; }
.work-status-pending { background: rgba(217,166,61,.2); color: #d9a63d; }
.work-status-approved { background: rgba(37,211,102,.18); color: #25D366; }
.work-status-rejected { background: rgba(239,68,68,.18); color: #ef4444; }


/* ================= Public site (nav, hero, sections, footer, motion) ================= */
html { scroll-behavior: smooth; }
section[id] { scroll-margin-top: 90px; }
body { font-family: 'DM Sans', -apple-system, sans-serif; line-height: 1.6; }
h1, h2, h3, h4, .section-title { font-family: 'Poppins', sans-serif; }

.site-nav { display: none; }
.site-footer { margin-top: 40px; }
@media (min-width: 721px) {
  body.guest-site .sidebar { display: none; }
  body.guest-site .content-area { width: 100%; }
  body.guest-site main { max-width: 1120px; padding: 28px 32px 20px; }
  .site-nav {
    display: flex; position: sticky; top: 0; z-index: 90; align-items: center; gap: 32px;
    padding: 14px 40px; background: color-mix(in srgb, var(--bg) 85%, transparent); backdrop-filter: blur(14px);
    border-bottom: 1px solid transparent; transition: border-color .3s, box-shadow .3s;
  }
  .site-nav.scrolled { border-bottom-color: var(--border); box-shadow: 0 8px 30px rgba(15,23,42,.12); }
  .site-nav-logo { display: flex; align-items: center; gap: 10px; font-family: 'Poppins', sans-serif; font-weight: 800; font-size: 22px; color: var(--navy); text-decoration: none; letter-spacing: -.01em; }
  .nav-word span { color: var(--accent); }
  .site-nav-links { display: flex; gap: 6px; flex: 1; justify-content: center; }
  .site-nav-links a { position: relative; color: var(--text-muted); text-decoration: none; font-size: 14px; font-weight: 500; padding: 8px 14px; border-radius: 8px; transition: color .2s, background .2s; }
  .site-nav-links a::after { content: ""; position: absolute; left: 14px; right: 14px; bottom: 3px; height: 2px; background: var(--accent); transform: scaleX(0); transform-origin: left; transition: transform .25s ease; }
  .site-nav-links a:hover, .site-nav-links a.active { color: var(--navy); }
  .site-nav-links a:hover::after, .site-nav-links a.active::after { transform: scaleX(1); }
  .site-nav-cta { display: flex; gap: 10px; }
  .site-nav-cta .btn { padding: 9px 20px; border-radius: 999px; }
  .site-nav-cta { align-items: center; }
  .site-nav-cta .btn-outline { color: var(--navy); border-color: var(--border); }
  .site-nav .logo-mark::after { border-color: var(--bg); }
}

/* hero */
.hero { min-height: 440px; border-radius: 20px; margin-top: 8px; box-shadow: 0 16px 40px rgba(15,23,42,.18); }
.hero-overlay { padding: 56px 48px; background: linear-gradient(0deg, rgba(6,10,22,.92) 0%, rgba(6,10,22,.35) 60%, transparent 100%); }
.hero-kicker { display: inline-block; font-size: 12px; font-weight: 600; letter-spacing: .12em; text-transform: uppercase; color: var(--accent); background: rgba(34,197,94,.12); border: 1px solid rgba(34,197,94,.3); padding: 6px 14px; border-radius: 999px; margin-bottom: 16px; }
.hero-name { font-size: clamp(34px, 5.6vw, 66px); font-weight: 800; letter-spacing: -.03em; line-height: 1.08; max-width: 760px; }
.hero-title { font-size: clamp(16px, 2vw, 21px); color: rgba(255,255,255,.88); max-width: 560px; margin-top: 14px; font-weight: 500; line-height: 1.5; }
.hero-actions { margin-top: 28px; gap: 14px; }
.hero-actions .btn { padding: 14px 28px; font-size: 15px; border-radius: 999px; transition: transform .2s, box-shadow .2s, background .2s; }
.hero-actions .btn:hover { transform: translateY(-3px); box-shadow: 0 12px 30px rgba(34,197,94,.35); }
.hero-kicker, .hero-name, .hero-title, .hero-actions { animation: heroUp .9s cubic-bezier(.2,.7,.2,1) both; }
.hero-name { animation-delay: .1s; } .hero-title { animation-delay: .25s; } .hero-actions { animation-delay: .4s; }
.hero-default-bg svg { animation: heroDrift 22s ease-in-out infinite alternate; transform-origin: 50% 100%; }
.hero-default-bg g[fill="#22C55E"] rect { animation: twinkle 3.6s ease-in-out infinite; }
.hero-default-bg g[fill="#22C55E"] rect:nth-child(3n) { animation-delay: 1.2s; }
.hero-default-bg g[fill="#22C55E"] rect:nth-child(3n+1) { animation-delay: 2.4s; }
@keyframes heroUp { from { opacity: 0; transform: translateY(26px); } to { opacity: 1; transform: none; } }
@keyframes heroDrift { from { transform: scale(1); } to { transform: scale(1.07); } }
@keyframes twinkle { 0%,100% { opacity: .9; } 50% { opacity: .2; } }

/* sections: roomy, consistent spacing */
.lp-section { padding: 88px 0 8px; }
.lp-head { max-width: 720px; margin-bottom: 34px; }
.lp-eyebrow { display: inline-block; font-size: 12px; font-weight: 700; letter-spacing: .14em; text-transform: uppercase; color: var(--accent); margin-bottom: 10px; }
.lp-title { font-size: clamp(26px, 3.4vw, 38px); font-weight: 700; letter-spacing: -.02em; line-height: 1.2; color: var(--navy); }
.lp-lead { font-size: 17px; line-height: 1.75; color: var(--text-muted); margin-top: 14px; }
.lp-offer-intro { max-width: 760px; margin-bottom: 30px; }
.lp-offer-intro h3 { font-size: 20px; margin-bottom: 8px; color: var(--navy); }
.lp-offer-intro p { color: var(--text-muted); line-height: 1.75; }
.lp-grid { display: grid; gap: 22px; }
.lp-offers { grid-template-columns: repeat(3, 1fr); }
.lp-steps { grid-template-columns: repeat(4, 1fr); }
.lp-work { grid-template-columns: repeat(3, 1fr); }
.lp-card { background: var(--card-bg); border: 1px solid var(--border); border-radius: 20px; padding: 28px 26px; transition: transform .3s cubic-bezier(.2,.7,.2,1), box-shadow .3s, border-color .3s; }
.lp-card h3 { font-size: 17px; margin: 14px 0 8px; color: var(--navy); }
.lp-card p { font-size: 14.5px; line-height: 1.7; color: var(--text-muted); }
.lp-icon { width: 52px; height: 52px; border-radius: 14px; display: flex; align-items: center; justify-content: center; font-size: 26px; background: rgba(34,197,94,.12); transition: transform .35s; }
.lp-step-num { width: 44px; height: 44px; border-radius: 50%; background: var(--accent); color: #04140A; display: flex; align-items: center; justify-content: center; font-family: 'Poppins', sans-serif; font-weight: 700; font-size: 18px; box-shadow: 0 0 0 0 rgba(34,197,94,.5); }
.lp-note { margin-top: 28px; padding: 20px 24px; border-left: 4px solid var(--accent); background: rgba(34,197,94,.07); border-radius: 0 14px 14px 0; color: var(--text-muted); line-height: 1.7; font-size: 15px; }
.lp-note b { color: var(--navy); }
.lp-work-card { display: block; background: var(--card-bg); border: 1px solid var(--border); border-radius: 20px; overflow: hidden; text-decoration: none; color: inherit; transition: transform .3s cubic-bezier(.2,.7,.2,1), box-shadow .3s, border-color .3s; }
.lp-work-img { aspect-ratio: 4/3; background-size: cover; background-position: center; background-color: rgba(128,128,128,.15); transition: transform .6s cubic-bezier(.2,.7,.2,1); }
.lp-work-card { overflow: hidden; }
.lp-work-img { overflow: hidden; }
.lp-work-info { padding: 16px 18px 18px; display: flex; align-items: center; gap: 8px; flex-wrap: wrap; font-size: 15px; color: var(--navy); }
.lp-contact { text-align: center; padding: 64px 28px; border-radius: 28px; border: 1px solid var(--border); background: radial-gradient(ellipse at 50% 0%, rgba(34,197,94,.16), transparent 65%), var(--card-bg); }
.lp-contact .lp-lead { max-width: 520px; margin: 14px auto 0; }
.lp-cta-row { display: flex; justify-content: center; gap: 14px; flex-wrap: wrap; margin-top: 28px; }
.lp-cta-row .btn { padding: 14px 30px; font-size: 15px; border-radius: 999px; }
.lp-contact-list { display: flex; justify-content: center; gap: 22px; flex-wrap: wrap; margin-top: 28px; font-size: 14.5px; }
.lp-contact-list a, .lp-contact-list span { color: var(--navy); text-decoration: none; }
.lp-contact-list a:hover { color: var(--accent); }

/* card motion */
html.js .reveal { opacity: 0; transform: translateY(30px); transition: opacity .8s ease, transform .8s cubic-bezier(.2,.7,.2,1), box-shadow .3s, border-color .3s; transition-delay: var(--d, 0ms); }
html.js .reveal.in { opacity: 1; transform: none; }
@media (hover: hover) {
  html.js .lp-card.reveal.in:hover, .lp-card:hover, .lp-work-card.reveal.in:hover, .lp-work-card:hover {
    transform: translateY(-8px); border-color: var(--accent);
    box-shadow: 0 22px 50px rgba(0,0,0,.4), 0 0 0 1px rgba(34,197,94,.3); transition-delay: 0ms;
  }
  .lp-card:hover .lp-icon { transform: scale(1.18) rotate(-6deg); }
  .lp-work-card:hover .lp-work-img { transform: scale(1.08); }
  .step-card, .job-card, .feed-post, .settings-card { transition: transform .25s, box-shadow .25s, border-color .25s; }
  .step-card:hover, .job-card:hover, .feed-post:hover { transform: translateY(-4px); box-shadow: 0 14px 34px rgba(0,0,0,.28); border-color: var(--accent); }
}
html.js .reveal.in .lp-step-num { animation: stepPulse 2.4s .6s ease-out 2; }
@keyframes stepPulse { 0% { box-shadow: 0 0 0 0 rgba(34,197,94,.55); } 100% { box-shadow: 0 0 0 18px rgba(34,197,94,0); } }
.btn { transition: transform .2s, box-shadow .2s, background .2s, border-color .2s; }

/* footer */
.site-footer { border-top: 1px solid var(--border); background: var(--sidebar-bg); color: rgba(255,255,255,.72); padding: 56px 40px 26px; margin-top: 64px; }
.footer-grid { max-width: 1120px; margin: 0 auto; display: grid; grid-template-columns: 1.6fr 1fr 1fr 1.3fr; gap: 40px; }
.footer-logo .logo-mark::after { border-color: var(--sidebar-bg); }
.footer-logo { display: flex; align-items: center; gap: 10px; font-family: 'Poppins', sans-serif; font-weight: 800; font-size: 22px; color: #fff; margin-bottom: 12px; }

.footer-motto { color: var(--accent) !important; font-family: 'Poppins', sans-serif; font-weight: 600; font-size: 16px !important; margin-bottom: 8px; }
.footer-brand p { font-size: 14px; line-height: 1.7; max-width: 320px; }
.site-footer h4 { color: #fff; font-size: 14px; letter-spacing: .06em; text-transform: uppercase; margin-bottom: 14px; }
.site-footer .footer-col a, .site-footer .footer-col span { display: block; color: rgba(255,255,255,.68); text-decoration: none; font-size: 14px; margin-bottom: 10px; transition: color .2s, transform .2s; }
.site-footer .footer-col a:hover { color: var(--accent); transform: translateX(4px); }
.footer-bottom { max-width: 1120px; margin: 36px auto 0; padding-top: 20px; border-top: 1px solid rgba(255,255,255,.08); font-size: 13px; color: rgba(255,255,255,.5); text-align: center; }

@media (max-width: 960px) {
  .lp-offers, .lp-work { grid-template-columns: repeat(2, 1fr); }
  .lp-steps { grid-template-columns: repeat(2, 1fr); }
  .footer-grid { grid-template-columns: 1fr 1fr; }
}
@media (max-width: 720px) {
  .hero { min-height: 340px; border-radius: 18px; }
  .hero-overlay { padding: 28px 20px; }
  .hero-actions .btn { padding: 12px 22px; flex: 1; text-align: center; }
  .lp-section { padding: 56px 0 4px; }
  .lp-head { margin-bottom: 24px; }
  .lp-lead { font-size: 16px; }
  .lp-offers, .lp-steps, .lp-work { grid-template-columns: 1fr; gap: 16px; }
  .lp-card { padding: 22px 20px; }
  .lp-contact { padding: 44px 20px; border-radius: 22px; }
  .site-footer { padding: 40px 22px 90px; margin-top: 44px; }
  .footer-grid { grid-template-columns: 1fr; gap: 28px; }
}
@media (prefers-reduced-motion: reduce) {
  html { scroll-behavior: auto; }
  html.js .reveal { opacity: 1; transform: none; transition: none; }
  .hero-kicker, .hero-name, .hero-title, .hero-actions, .hero-default-bg svg, .hero-default-bg g[fill="#22C55E"] rect { animation: none; }
}


/* ================= Photo gallery (full photos), lightbox, reviews ================= */
.works-intro { font-size: 14px; color: var(--text-muted); margin: -4px 0 16px; }
.gal { column-count: 2; column-gap: 10px; margin-top: 12px; }
.gal.single { column-count: 1; }
.gal img { display: block; width: 100%; height: auto; border-radius: 12px; margin-bottom: 10px; break-inside: avoid; cursor: zoom-in; background: rgba(128,128,128,.14); transition: transform .25s, box-shadow .25s; }
@media (hover: hover) { .gal img:hover { transform: scale(1.015); box-shadow: 0 12px 30px rgba(0,0,0,.35); } }
@media (min-width: 900px) { .gal:not(.single) { column-count: 3; } }
@media (max-width: 720px) { .gal { column-count: 1; } }

.lp-work-img { position: relative; aspect-ratio: 4/3; overflow: hidden; background-color: rgba(128,128,128,.15); }
.lp-work-img::before { content: ""; position: absolute; inset: -20px; background-image: var(--bg); background-size: cover; background-position: center; filter: blur(22px) brightness(.55); }
.lp-work-img img { position: relative; width: 100%; height: 100%; object-fit: contain; display: block; }

.lb { position: fixed; inset: 0; z-index: 30000; background: rgba(4,7,14,.96); display: none; flex-direction: column; touch-action: none; }
.lb.open { display: flex; animation: lbIn .2s ease; }
@keyframes lbIn { from { opacity: 0; } to { opacity: 1; } }
.lb-top { display: flex; justify-content: space-between; align-items: center; padding: 14px 16px; color: #fff; font-size: 14px; }
.lb-close { background: rgba(255,255,255,.12); border: none; color: #fff; width: 40px; height: 40px; border-radius: 50%; font-size: 18px; cursor: pointer; }
.lb-stage { flex: 1; min-height: 0; display: flex; align-items: center; justify-content: center; overflow: hidden; touch-action: none; cursor: zoom-in; }
.lb-stage.zoomed { cursor: grab; }
.lb-img { max-width: 100%; max-height: 100%; object-fit: contain; user-select: none; -webkit-user-drag: none; transition: transform .12s ease-out; will-change: transform; }
.lb-nav { position: absolute; top: 50%; transform: translateY(-50%); background: rgba(255,255,255,.12); border: none; color: #fff; width: 44px; height: 64px; font-size: 30px; cursor: pointer; border-radius: 10px; z-index: 2; }
.lb-prev { left: 8px; } .lb-next { right: 8px; }
.lb-bottom { display: flex; align-items: center; justify-content: space-between; gap: 12px; padding: 12px 16px calc(14px + env(safe-area-inset-bottom, 0px)); color: #fff; font-size: 14px; }
.lb-cap { font-weight: 600; }
.lb-rate { background: var(--accent); color: #04140A; border: none; border-radius: 999px; padding: 9px 16px; font-weight: 700; font-size: 13px; cursor: pointer; white-space: nowrap; }

.work-reviews { margin-top: 14px; border-top: 1px solid var(--border); padding-top: 12px; }
.rev-toggle { width: 100%; display: flex; align-items: center; gap: 8px; flex-wrap: wrap; text-align: left; background: none; border: none; color: inherit; font-size: 14px; cursor: pointer; padding: 6px 0; font-family: inherit; }
.rev-stars { color: #F5B301; letter-spacing: 1px; }
.rev-cta { margin-left: auto; font-size: 12px; font-weight: 600; color: var(--accent); }
.rev-panel { padding-top: 10px; }
.rev-item { padding: 12px 0; border-top: 1px solid var(--border); }
.rev-head { display: flex; align-items: center; gap: 10px; font-size: 14px; }
.rev-text { font-size: 14px; line-height: 1.6; margin-top: 4px; color: var(--text-muted); white-space: pre-line; }
.rev-del { background: none; border: none; color: #ef4444; font-size: 12px; cursor: pointer; }
.rev-empty { font-size: 13px; color: var(--text-muted); padding: 8px 0 12px; }
.rev-form { margin-top: 10px; display: grid; gap: 10px; }
.rev-form textarea { padding: 10px 12px; border: 1px solid var(--border); border-radius: 10px; font-family: inherit; font-size: 14px; background: transparent; color: inherit; }
.rev-form-title { font-weight: 600; font-size: 14px; }
.stars-input { display: inline-flex; flex-direction: row-reverse; justify-content: flex-end; gap: 4px; }
.stars-input input { position: absolute; opacity: 0; pointer-events: none; }
.stars-input label { font-size: 32px; line-height: 1; color: rgba(128,128,128,.45); cursor: pointer; transition: color .15s, transform .15s; }
.stars-input label:hover, .stars-input label:hover ~ label, .stars-input input:checked ~ label { color: #F5B301; }
.stars-input label:hover { transform: scale(1.2); }


/* --- likes + video --- */
.gal-video { display: block; width: 100%; height: auto; max-height: 75vh; border-radius: 12px; margin-bottom: 10px; background: #000; break-inside: avoid; }
.media-hint { font-size: 12px; color: var(--text-muted); margin: -2px 0 2px; }
.work-actions { display: flex; align-items: center; gap: 10px; margin-bottom: 4px; }
.like-btn { display: inline-flex; align-items: center; gap: 6px; background: rgba(128,128,128,.12); border: 1px solid var(--border); color: inherit; border-radius: 999px; padding: 7px 16px; font-size: 14px; font-weight: 600; cursor: pointer; font-family: inherit; transition: background .2s, border-color .2s, transform .15s; }
.like-btn .like-icon { font-size: 18px; line-height: 1; transition: color .2s; }
.like-btn:hover { border-color: #ef4444; }
.like-btn.liked { background: rgba(239,68,68,.14); border-color: rgba(239,68,68,.5); }
.like-btn.liked .like-icon { color: #ef4444; }
.like-btn.pop .like-icon { animation: likePop .45s ease; }
.like-sm { padding: 3px 11px; font-size: 12px; margin-top: 8px; }
.like-sm .like-icon { font-size: 14px; }
@keyframes likePop { 0% { transform: scale(1); } 40% { transform: scale(1.7); } 100% { transform: scale(1); } }
.lp-work-img video { position: relative; width: 100%; height: 100%; object-fit: contain; display: block; background: #000; }
.lp-play { position: absolute; right: 12px; bottom: 12px; width: 38px; height: 38px; border-radius: 50%; background: rgba(0,0,0,.6); color: #fff; display: flex; align-items: center; justify-content: center; font-size: 14px; }



/* ===== Marketplace layout: compact services, carousels, sections ===== */
/* top bar on tablets / landscape phones: links scroll instead of pushing the page wider */
@media (min-width: 721px) {
  .site-nav { gap: 16px; padding: 12px 20px; }
  .site-nav-logo, .site-nav-cta { flex-shrink: 0; }
  .site-nav-links { min-width: 0; flex: 1; overflow-x: auto; scrollbar-width: none; justify-content: flex-start; gap: 2px; }
  .site-nav-links::-webkit-scrollbar { display: none; }
  .site-nav-links a { flex: 0 0 auto; padding: 8px 10px; }
}
@media (min-width: 1100px) { .site-nav { gap: 28px; padding: 14px 40px; } .site-nav-links { justify-content: center; overflow: visible; } .site-nav-links a { padding: 8px 14px; } }

:root { --r-card: 16px; --r-sm: 10px; --tabs-h: 58px; }
html, body { max-width: 100%; }
body { overflow-x: clip; }
.lp-section { padding: 56px 0 4px; overflow-x: clip; }
.lp-head { max-width: 680px; margin-bottom: 22px; }
.lp-title { font-size: clamp(24px, 3vw, 32px); }
.lp-lead { font-size: 16px; line-height: 1.7; margin-top: 10px; }
.lp-subhead { display: flex; justify-content: space-between; align-items: baseline; margin: 30px 0 10px; }
.lp-subhead h3 { font-size: 18px; color: var(--navy); }
.lp-subhead a { font-size: 14px; font-weight: 600; color: var(--accent); text-decoration: none; }

/* carousel component (touch swipe by scroll-snap, arrows on desktop) */
.carousel { position: relative; min-width: 0; max-width: 100%; }
.carousel-track { display: flex; gap: 14px; overflow-x: auto; overflow-y: hidden; scroll-snap-type: x mandatory; -webkit-overflow-scrolling: touch; overscroll-behavior-x: contain; scrollbar-width: none; padding: 4px 2px 10px; scroll-padding-inline: 2px; }
.carousel-track::-webkit-scrollbar { display: none; }
.carousel-track:focus-visible { outline: 2px solid var(--accent); outline-offset: 2px; border-radius: var(--r-sm); }
.carousel-track > * { flex: 0 0 var(--slide-w, 100%); scroll-snap-align: start; min-width: 0; }
.carousel-btn { position: absolute; top: 40%; transform: translateY(-50%); width: 42px; height: 42px; border-radius: 50%; border: 1px solid var(--border); background: var(--card-bg); color: var(--navy); font-size: 24px; line-height: 1; cursor: pointer; display: none; align-items: center; justify-content: center; box-shadow: 0 6px 18px rgba(15,23,42,.18); z-index: 3; transition: opacity .2s, transform .2s; padding: 0 0 3px; }
.carousel-btn.prev { left: 8px; } .carousel-btn.next { right: 8px; }
.carousel-btn:disabled { opacity: 0; pointer-events: none; }
.carousel-btn:hover { transform: translateY(-50%) scale(1.06); }
.carousel-dots { display: flex; justify-content: center; gap: 8px; margin-top: 6px; }
.carousel-dots button { width: 8px; height: 8px; border-radius: 50%; border: none; padding: 0; background: rgba(128,128,128,.4); cursor: pointer; position: relative; transition: width .2s, background .2s; }
.carousel-dots button::after { content: ""; position: absolute; inset: -10px -4px; }
.carousel-dots button.on { width: 22px; border-radius: 4px; background: var(--accent); }
.carousel.no-scroll .carousel-btn, .carousel.no-scroll .carousel-dots { display: none !important; }
@media (hover: hover) and (min-width: 721px) { .carousel-btn { display: flex; } }

/* services: swipeable cards on phones, responsive grid on larger screens */
.carousel-cards { --slide-w: min(72vw, 280px); }
.svc-card { display: flex; flex-direction: column; background: var(--card-bg); border: 1px solid var(--border); border-radius: var(--r-card); padding: 10px 10px 14px; text-align: center; text-decoration: none; color: inherit; transition: transform .25s, box-shadow .25s, border-color .25s; }
.svc-art { border-radius: 12px; padding: 6px 4px 2px; margin-bottom: 8px; background: radial-gradient(ellipse at 50% 42%, rgba(34,197,94,.14), transparent 70%), #EDF2F8; }
body.dark-mode .svc-art { background: radial-gradient(ellipse at 50% 42%, rgba(34,197,94,.16), transparent 70%), rgba(7,12,26,.55); }
.svc-art .svc-svg { filter: drop-shadow(0 6px 8px rgba(15,23,42,.22)); }
.svc-art .svc-svg { display: block; width: auto; max-width: 100%; height: 150px; margin: 0 auto; filter: drop-shadow(0 8px 10px rgba(0,0,0,.3)); animation: none; transition: transform .35s; }
.svc-card h3 { font-size: 16px; margin: 4px 0 2px; color: var(--navy); }
.svc-card p { font-size: 13px; line-height: 1.5; color: var(--text-muted); max-width: none; margin: 0 6px 8px; min-height: 2.9em; flex: 1; }
.svc-go { font-size: 12.5px; font-weight: 700; color: var(--accent); margin-top: auto; }
@media (hover: hover) { .svc-card:hover { transform: translateY(-4px); border-color: var(--accent); box-shadow: 0 14px 30px rgba(15,23,42,.18); } .svc-card:hover .svc-svg { transform: scale(1.04); } }
.svc-card:focus-visible { outline: 2px solid var(--accent); outline-offset: 2px; }
@media (min-width: 721px) {
  .carousel-cards .carousel-track { display: grid; grid-template-columns: repeat(3, 1fr); overflow: visible; gap: 16px; scroll-snap-type: none; padding: 0; }
  .carousel-cards .carousel-track > * { flex: none; }
}
@media (min-width: 1040px) { .carousel-cards .carousel-track { grid-template-columns: repeat(5, 1fr); gap: 14px; } .svc-art .svc-svg { height: 118px; } }

/* featured products strip */
.carousel-mini { --slide-w: 150px; }
.pcard-mini { display: block; text-decoration: none; color: inherit; background: var(--card-bg); border: 1px solid var(--border); border-radius: 14px; padding: 8px; transition: transform .25s, border-color .25s; }
.pcard-mini:hover { transform: translateY(-3px); border-color: var(--accent); }
.pm-name { font-size: 13px; font-weight: 600; margin: 8px 2px 0; color: var(--navy); white-space: nowrap; overflow: hidden; text-overflow: ellipsis; }
.pm-price { font-size: 13px; font-weight: 700; color: var(--accent); margin: 2px 2px 2px; }
@media (min-width: 721px) { .carousel-mini { --slide-w: 190px; } }

/* image tile that always shows the WHOLE picture (blurred fill behind it) */
.pimg { position: relative; aspect-ratio: 4 / 3; border-radius: 10px; overflow: hidden; background: rgba(128,128,128,.14); }
.pimg::before { content: ""; position: absolute; inset: -16px; background-image: var(--bg); background-size: cover; background-position: center; filter: blur(18px) brightness(.7); }
.pimg img { position: relative; width: 100%; height: 100%; object-fit: contain; display: block; }
.pimg-art::before { display: none; }
.pimg-art { background: #0A1426; }
.pimg-art svg { width: 100%; height: 100%; display: block; }

/* how it works */
.steps3 { list-style: none; display: grid; grid-template-columns: repeat(3, minmax(0, 1fr)); gap: 16px; padding: 0; margin: 0; }
.step3 { display: flex; gap: 14px; align-items: flex-start; background: var(--card-bg); border: 1px solid var(--border); border-radius: var(--r-card); padding: 18px; }
.step3-num { flex: 0 0 38px; height: 38px; border-radius: 50%; background: var(--accent); color: #04140A; font-family: 'Poppins', sans-serif; font-weight: 700; display: flex; align-items: center; justify-content: center; }
.step3 h3 { font-size: 16px; margin-bottom: 4px; color: var(--navy); }
.step3 p { font-size: 14px; line-height: 1.6; color: var(--text-muted); }
.steps-note { margin-top: 14px; font-size: 13.5px; color: var(--text-muted); }

/* why andy */
.why-grid { display: grid; grid-template-columns: repeat(4, 1fr); gap: 14px; }
.why-item { display: flex; gap: 12px; align-items: flex-start; padding: 16px; border: 1px solid var(--border); border-radius: var(--r-card); background: var(--card-bg); }
.why-ico { flex: 0 0 40px; height: 40px; border-radius: 12px; background: rgba(34,197,94,.14); display: flex; align-items: center; justify-content: center; font-size: 20px; }
.why-item h3 { font-size: 15px; margin-bottom: 3px; color: var(--navy); }
.why-item p { font-size: 13.5px; line-height: 1.55; color: var(--text-muted); }

/* about: text + image carousel */
.about-grid { display: grid; grid-template-columns: minmax(0, 1.05fr) minmax(0, 1fr); gap: 36px; align-items: start; }
.about-grid > *, .why-grid > *, .steps3 > * { min-width: 0; }
.about-points { display: grid; gap: 14px; margin-bottom: 18px; }
.about-point { display: flex; gap: 12px; align-items: flex-start; }
.ap-ico { flex: 0 0 36px; height: 36px; border-radius: 10px; background: rgba(34,197,94,.14); display: flex; align-items: center; justify-content: center; font-size: 18px; }
.about-point h3 { font-size: 15px; margin-bottom: 2px; color: var(--navy); }
.about-point p, .about-point li { font-size: 14px; line-height: 1.6; color: var(--text-muted); }
.about-point ul { margin: 4px 0 0 18px; }
.about-link { padding: 10px 20px; border-radius: 999px; }
.carousel-hero { --slide-w: 100%; }
.carousel-hero .carousel-track { gap: 0; padding: 0 0 8px; }
.carousel-hero .carousel-btn { top: 42%; }
.slide { margin: 0; border-radius: var(--r-card); overflow: hidden; border: 1px solid var(--border); background: var(--card-bg); }
.slide-img { position: relative; aspect-ratio: 4 / 3; overflow: hidden; background: #0B1630; }
.slide-img::before { content: ""; position: absolute; inset: -20px; background-image: var(--bg); background-size: cover; background-position: center; filter: blur(22px) brightness(.6); }
.slide-img img { position: relative; width: 100%; height: 100%; object-fit: contain; display: block; }
.slide figcaption { padding: 10px 14px; font-size: 13.5px; font-weight: 600; color: var(--navy); display: flex; align-items: center; justify-content: space-between; gap: 10px; }
.slide-tag { font-size: 11px; font-weight: 600; padding: 2px 9px; border-radius: 999px; background: rgba(128,128,128,.18); color: var(--text-muted); white-space: nowrap; }

/* final call to action: keep it light */
.lp-contact { padding: 40px 22px; border-radius: 20px; background: var(--card-bg); }
.lp-cta-row .btn { padding: 12px 26px; }

/* catalogue */
.cat-head { display: flex; justify-content: space-between; align-items: flex-start; gap: 12px; margin-bottom: 12px; }
.cat-sub { font-size: 13.5px; color: var(--text-muted); }
.cat-cart { font-size: 13px; font-weight: 600; color: var(--accent); text-decoration: none; white-space: nowrap; padding: 8px 12px; border: 1px solid var(--border); border-radius: 999px; }
.cat-filter-row { display: flex; gap: 8px; flex-wrap: nowrap; overflow-x: auto; scroll-snap-type: x proximity; scrollbar-width: none; padding: 2px 2px 8px; margin: 0 -2px; }
.cat-filter-row::-webkit-scrollbar { display: none; }
.cat-filter { flex: 0 0 auto; scroll-snap-align: start; padding: 9px 15px; min-height: 40px; display: inline-flex; align-items: center; gap: 6px; text-decoration: none; color: var(--navy); }
.cat-filter span { font-size: 11px; opacity: .65; }
.cat-filter.active, .cat-filter.active span { color: #fff; opacity: 1; }
.product-grid { display: grid; grid-template-columns: repeat(auto-fill, minmax(215px, 1fr)); gap: 16px; margin-top: 14px; }
.pcard { display: flex; flex-direction: column; background: var(--card-bg); border: 1px solid var(--border); border-radius: var(--r-card); overflow: hidden; transition: transform .25s, box-shadow .25s, border-color .25s; }
@media (hover: hover) { .pcard:hover { transform: translateY(-3px); border-color: var(--accent); box-shadow: 0 12px 28px rgba(15,23,42,.15); } }
.pcard .pimg { border-radius: 0; }
.pvideo { width: 100%; max-height: 170px; background: #000; display: block; }
.pbody { padding: 12px 14px 14px; display: flex; flex-direction: column; gap: 4px; flex: 1; }
.pcat { font-size: 11px; font-weight: 700; letter-spacing: .06em; text-transform: uppercase; color: var(--accent); }
.pname { font-size: 15.5px; line-height: 1.3; color: var(--navy); }
.pdesc { font-size: 13px; line-height: 1.5; color: var(--text-muted); display: -webkit-box; -webkit-line-clamp: 2; -webkit-box-orient: vertical; overflow: hidden; }
.pprice { font-size: 17px; font-weight: 700; color: var(--navy); margin-top: auto; padding-top: 6px; }
.pprice span { font-size: 12px; font-weight: 500; color: var(--text-muted); }
.pform { display: grid; grid-template-columns: minmax(0, 1fr) 62px; gap: 8px; margin-top: 8px; }
.pform:not(:has(select)) { grid-template-columns: 62px minmax(0, 1fr); }
.pform:not(:has(select)) .btn { grid-column: auto; }
.pform select, .pform input { padding: 9px 10px; min-height: 42px; border: 1px solid var(--border); border-radius: 10px; font-size: 14px; background: transparent; color: inherit; width: 100%; font-family: inherit; }
.pform .btn { grid-column: 1 / -1; min-height: 44px; font-size: 14px; }
.pform-login { margin-top: 8px; min-height: 44px; width: 100%; }
.cat-help { margin-top: 26px; padding: 16px; text-align: center; font-size: 14px; color: var(--text-muted); border: 1px dashed var(--border); border-radius: var(--r-card); }
.cat-help a { color: var(--accent); font-weight: 700; margin-left: 6px; text-decoration: none; }

/* responsive */
@media (max-width: 960px) {
  .steps3 { grid-template-columns: minmax(0, 1fr); }
  .why-grid { grid-template-columns: repeat(2, 1fr); }
  .about-grid { grid-template-columns: minmax(0, 1fr); gap: 24px; }
}
@media (max-width: 720px) {
  .lp-section { padding: 40px 0 2px; }
  .lp-lead { font-size: 15px; }
  .why-grid { grid-template-columns: 1fr; gap: 10px; }
  .why-item { padding: 12px 14px; }
  .step3 { padding: 14px; }
  .product-grid { grid-template-columns: repeat(2, minmax(0, 1fr)); gap: 10px; }
  .pbody { padding: 10px 10px 12px; }
  .pname { font-size: 14px; } .pprice { font-size: 15px; }
  .cat-head { flex-direction: column; }
}
@media (max-width: 380px) { .product-grid { grid-template-columns: 1fr; } }

/* phones: respect the notch / gesture bar, never hide content under fixed bars */
@media (max-width: 720px) {
  .mobile-topbar { padding-top: calc(10px + env(safe-area-inset-top, 0px)); padding-left: calc(14px + env(safe-area-inset-left, 0px)); padding-right: calc(14px + env(safe-area-inset-right, 0px)); }
  .bottom-tabs { padding-bottom: env(safe-area-inset-bottom, 0px); padding-left: env(safe-area-inset-left, 0px); padding-right: env(safe-area-inset-right, 0px); }
  .bottom-tabs a, .bottom-tabs button { min-height: 54px; padding: 6px 0; justify-content: center; line-height: 1.1; text-decoration: none; }
  .bottom-tabs a span, .bottom-tabs button span { line-height: 1.1; display: block; }
  main { padding-bottom: calc(var(--tabs-h) + env(safe-area-inset-bottom, 0px) + 26px); padding-left: max(14px, env(safe-area-inset-left, 0px)); padding-right: max(14px, env(safe-area-inset-right, 0px)); }
  .app-footer { padding-bottom: calc(var(--tabs-h) + env(safe-area-inset-bottom, 0px) + 18px); }
  .site-footer { padding-bottom: calc(var(--tabs-h) + env(safe-area-inset-bottom, 0px) + 26px); }
  .sidebar { padding-top: calc(20px + env(safe-area-inset-top, 0px)); }
  .hero { min-height: 300px; }
}
/* short landscape screens (phones turned sideways) */
@media (max-height: 500px) and (orientation: landscape) {
  .hero { min-height: 230px; }
  .hero-overlay { padding: 18px 22px; }
  .hero-name { font-size: 26px; max-width: 520px; }
  .hero-title { font-size: 13px; margin-top: 6px; }
  .hero-actions { margin-top: 12px; }
  .hero-actions .btn { padding: 8px 18px; }
  .hero-kicker { margin-bottom: 8px; padding: 3px 10px; font-size: 10px; }
  .lp-section { padding-top: 32px; }
  .bottom-tabs a, .bottom-tabs button { min-height: 44px; padding: 4px 0; flex-direction: row; justify-content: center; gap: 8px; }
  :root { --tabs-h: 46px; }
}

/* --- light/dark switch, legal pages, notices --- */
.mode-switch { position: relative; width: 58px; height: 30px; border-radius: 999px; border: 1px solid var(--border); background: #E8EDF4; cursor: pointer; padding: 0; flex-shrink: 0; transition: background .3s, border-color .3s; }
.mode-switch.sm { width: 48px; height: 26px; }
.mode-switch .ms-ico { position: absolute; top: 50%; transform: translateY(-50%); font-size: 13px; line-height: 1; }
.mode-switch.sm .ms-ico { font-size: 11px; }
.mode-switch .ms-sun { left: 7px; } .mode-switch .ms-moon { right: 7px; }
.mode-switch .ms-knob { position: absolute; top: 2px; left: 2px; width: 24px; height: 24px; border-radius: 50%; background: #fff; box-shadow: 0 2px 6px rgba(15,23,42,.3); transition: transform .3s cubic-bezier(.2,.8,.2,1), background .3s; }
.mode-switch.sm .ms-knob { width: 20px; height: 20px; }
body.dark-mode .mode-switch { background: #1E2D4A; border-color: #2C4166; }
body.dark-mode .mode-switch .ms-knob { transform: translateX(28px); background: #0A1020; box-shadow: 0 2px 6px rgba(0,0,0,.5), inset 0 0 0 1px #2C4166; }
body.dark-mode .mode-switch.sm .ms-knob { transform: translateX(22px); }
.mode-row { display: flex; align-items: center; justify-content: space-between; padding: 8px 22px 12px; font-size: 14px; color: var(--chrome-dim); }
.terms-note { font-size: 12px; line-height: 1.5; color: var(--text-muted); text-align: center; margin-top: 12px; }
.terms-note a { color: var(--accent); font-weight: 600; text-decoration: underline; }
.footer-legal { display: block; margin-top: 8px; }
.footer-legal a { display: inline; margin: 0 10px; font-size: 13px; color: rgba(255,255,255,.6); }
.app-footer { text-align: center; font-size: 12px; color: var(--text-muted); padding: 6px 16px 26px; }
.app-footer a { color: var(--text-muted); text-decoration: underline; }
@media (max-width: 720px) { .app-footer { padding-bottom: 86px; } .mobile-topbar .mode-switch { margin-right: 4px; } }
.legal { max-width: 780px; margin: 0 auto; padding: 8px 0 30px; } .legal h1 { font-size: clamp(28px,4vw,38px); letter-spacing: -.02em; margin-bottom: 6px; } .legal .legal-date { color: var(--text-muted); font-size: 14px; margin-bottom: 26px; } .legal h2 { font-size: 19px; margin: 28px 0 8px; } .legal p, .legal li { color: var(--text-muted); line-height: 1.75; font-size: 15.5px; }
.legal p { margin-bottom: 14px; }
.legal li { margin-bottom: 6px; } .legal ul { margin: 8px 0 8px 22px; } .legal a { color: var(--accent); font-weight: 600; }


.sidebar .bottom-links .mode-row .mode-switch { display: block; width: 48px; height: 26px; padding: 0; position: relative; border: 1px solid var(--border); background: #E8EDF4; border-radius: 999px; flex-shrink: 0; }
body.dark-mode .sidebar .bottom-links .mode-row .mode-switch { background: #1E2D4A; border-color: #2C4166; }
.sidebar .bottom-links .mode-row .mode-switch:hover { background: #E8EDF4; }
body.dark-mode .sidebar .bottom-links .mode-row .mode-switch:hover { background: #1E2D4A; }
.sidebar .bottom-links .mode-row span:first-child { font-size: 14px; }
@media (max-width: 720px) { .sidebar .bottom-links .mode-row .mode-switch { min-height: 26px; height: 26px; } }
.sidebar .logo .nav-word { color: var(--chrome-text); }
.sidebar .logo .nav-word span { color: var(--accent); }


/* --- mobile menu polish (Android) --- */
.menu-close { display: none; }
@media (max-width: 720px) {
  body.menu-open, html:has(body.menu-open) { overflow: hidden; }
  .sidebar { height: 100vh; height: 100dvh; bottom: auto; overscroll-behavior: contain; -webkit-overflow-scrolling: touch; padding-bottom: calc(24px + env(safe-area-inset-bottom, 0px)); }
  body.menu-open .sidebar { box-shadow: 8px 0 30px rgba(0,0,0,.25); }
  .menu-close { display: flex; align-items: center; justify-content: center; position: absolute; top: 10px; right: 10px; width: 44px; height: 44px; border-radius: 50%; border: none; background: var(--chrome-hover); color: var(--chrome-text); font-size: 18px; z-index: 2; cursor: pointer; }
  .sidebar .logo { padding-right: 64px; }
  .sidebar nav a, .sidebar nav button, .sidebar .bottom-links a, .sidebar .bottom-links button { min-height: 46px; }
  .mode-row { min-height: 48px; }
  .mode-switch::after { content: ""; position: absolute; inset: -10px; }
  .hamburger-btn, .help-icon-btn { min-width: 44px; min-height: 44px; display: inline-flex; align-items: center; justify-content: center; }
  .bottom-tabs a, .bottom-tabs button { min-height: 56px; }
  /* fewer always-on animations on phones: smoother and kinder to the battery */
  .svc-art .svc-svg, .svc-shine, .svc-twinkle, .hero-default-bg svg, .hero-default-bg g[fill="#22C55E"] rect { animation: none !important; }
}

.pay-note { margin-bottom: 14px; font-size: 13.5px; border-color: var(--accent); }


/* ===== Explore Services page ===== */
.svc-all { margin-top: 16px; text-align: center; }
.svc-all .btn { padding: 11px 26px; border-radius: 999px; }
.svcp-head { max-width: 640px; margin: 4px 0 14px; }
.svcp-upload { margin: 8px 0 18px; border: 1px dashed var(--accent); border-radius: 14px; padding: 12px 16px; background: var(--card-bg); }
.svcp-upload summary { cursor: pointer; font-weight: 700; color: var(--accent); min-height: 32px; display: flex; align-items: center; }
.svcp-upload form { margin-top: 12px; }
.svcp-sec { padding: 26px 0 8px; scroll-margin-top: 80px; border-top: 1px solid var(--border); margin-top: 14px; }
.svcp-sec:first-of-type { border-top: none; }
.svcp-sec-head { display: flex; gap: 18px; align-items: center; margin-bottom: 14px; }
.svcp-art { flex: 0 0 150px; border-radius: 14px; background: #EDF2F8; padding: 6px; display: flex; align-items: center; justify-content: center; min-height: 112px; }
body.dark-mode .svcp-art { background: rgba(7,12,26,.55); }
.svcp-art .svc-svg { width: 100%; height: auto; max-height: 110px; animation: none; }
.svcp-emoji { font-size: 44px; }
.svcp-sec-text h2 { font-size: 22px; color: var(--navy); }
.svcp-sec-text p { font-size: 14.5px; color: var(--text-muted); margin: 4px 0 10px; }
.svcp-actions { display: flex; gap: 8px; flex-wrap: wrap; }
.svcp-actions .btn { padding: 9px 16px; font-size: 13.5px; border-radius: 999px; min-height: 40px; }
.svcp-grid { display: grid; grid-template-columns: repeat(auto-fill, minmax(190px, 1fr)); gap: 14px; }
.svcp-item { margin: 0; background: var(--card-bg); border: 1px solid var(--border); border-radius: 14px; overflow: hidden; display: flex; flex-direction: column; transition: transform .25s, border-color .25s, box-shadow .25s; }
@media (hover: hover) { .svcp-item:hover { transform: translateY(-3px); border-color: var(--accent); box-shadow: 0 12px 26px rgba(15,23,42,.14); } }
.svcp-item .pimg { border-radius: 0; cursor: zoom-in; }
.svcp-item figcaption { padding: 10px 12px 12px; display: flex; flex-direction: column; gap: 2px; }
.svcp-item figcaption b { font-size: 14px; color: var(--navy); line-height: 1.3; }
.svcp-item figcaption span { font-size: 13px; font-weight: 700; color: var(--accent); }
.svcp-del { margin-top: 6px; background: none; border: none; color: #ef4444; font-size: 12px; text-align: left; padding: 6px 0; cursor: pointer; min-height: 32px; }
.svcp-empty { padding: 22px 14px; }
.svcp-foot { text-align: center; padding: 30px 0 6px; color: var(--text-muted); }
.svcp-foot .btn { margin-top: 10px; padding: 12px 26px; border-radius: 999px; }
.svcp-foot h3 { font-size: 18px; color: var(--navy); margin: 0 0 4px; }
.svcp-foot p { margin: 0; }
.svcp-grid { align-items: start; }
.svcp-info { display: grid; gap: 6px; margin: 2px 0 12px; font-size: 13.5px; line-height: 1.45; }
.svcp-info div { display: flex; gap: 8px; }
.svcp-info dt { flex: 0 0 74px; font-weight: 700; color: var(--navy); }
.svcp-info dd { margin: 0; color: var(--text-muted); }
.svcp-more { margin-top: 4px; }
.svcp-more summary { cursor: pointer; font-size: 13px; font-weight: 600; color: var(--accent); min-height: 32px; display: flex; align-items: center; list-style: none; }
.svcp-more summary::-webkit-details-marker { display: none; }
.svcp-more summary::after { content: "▾"; margin-left: 6px; }
.svcp-more[open] summary::after { content: "▴"; }
.svcp-more p { margin: 2px 0 8px; font-size: 13px; line-height: 1.5; color: var(--text-muted); white-space: pre-line; overflow-wrap: anywhere; }
.svcp-ask { font-size: 13px; font-weight: 700; color: var(--accent); text-decoration: none; display: inline-block; padding: 4px 0 6px; }
.pimg-broken img { visibility: hidden; }
.pimg-broken::before { display: none; }
.pimg-broken { background: var(--card-bg); }
.pimg-broken::after { content: "Photo unavailable"; position: absolute; inset: 0; display: flex; align-items: center; justify-content: center; font-size: 12px; color: var(--text-muted); }

/* Professional consultation */
.cons { margin: 36px auto 0; padding: 22px 20px; max-width: 760px; border: 1px solid var(--border); border-radius: 14px; background: var(--card-bg); scroll-margin-top: 80px; }
.cons-intro h2 { font-size: 22px; color: var(--navy); margin: 2px 0 6px; }
.cons-intro p { font-size: 14.5px; line-height: 1.55; color: var(--text-muted); margin: 0 0 10px; }
.cons-intro .cons-prep-title { font-size: 13.5px; font-weight: 700; color: var(--navy); margin-bottom: 4px; }
.cons-prep { margin: 0 0 16px; padding-left: 18px; font-size: 14px; line-height: 1.6; color: var(--text-muted); }
.cons-safety { border-left: 4px solid var(--accent); background: var(--bg); padding: 12px 14px; border-radius: 0 10px 10px 0; font-size: 14px; line-height: 1.55; color: var(--navy); margin: 0 0 20px; }
.cons-safety span { display: block; margin-top: 6px; font-size: 13px; color: var(--text-muted); }
.cons-hint { font-size: 12px; line-height: 1.4; color: var(--text-muted); }
.cons-submit { align-self: flex-start; padding: 12px 24px; border-radius: 999px; }
.cons-submit:disabled { opacity: .6; cursor: default; }
.cons-start { display: flex; flex-direction: column; gap: 8px; align-items: flex-start; }

/* Guided consultation chat: dark panel with green accents, built on the existing chat styles */
.cg { max-width: 680px; margin: 0 auto; }
.cg-back { display: inline-block; margin: 0 0 10px; font-size: 14px; font-weight: 600; color: var(--accent); text-decoration: none; min-height: 32px; line-height: 32px; }
.cg .rq-chat { --bg: #0A1426; --card-bg: #101C34; --border: rgba(255,255,255,.12); --navy: #F1F5F9; --text-muted: #9FB0C8; --accent: #22C55E; background: #0A1426; border-color: rgba(34,197,94,.35); }
.cg-note { padding: 8px 14px; font-size: 12.5px; line-height: 1.4; color: var(--text-muted); background: var(--card-bg); border-bottom: 1px solid var(--border); }
.cg-note b { color: #22C55E; }
.cg .rq-msg.wide { max-width: 100%; }
.cg .rq-msg.wide .rq-bub { width: 100%; box-sizing: border-box; }
.cg .rq-msg.cg-safe .rq-bub { border-left: 3px solid #22C55E; border-top-left-radius: 4px; }
.cg .rq-msg.cg-warn .rq-bub { border: 1px solid #F59E0B; background: rgba(245,158,11,.12); }
.cg-hint { color: var(--text-muted); font-size: 12.5px; line-height: 1.4; }
.cg-sum h5 { margin: 12px 0 4px; font-size: 11px; text-transform: uppercase; letter-spacing: .06em; color: #22C55E; }
.cg-sum h5:first-child { margin-top: 2px; }
.cg-sum ul { margin: 0; padding-left: 18px; font-size: 14px; line-height: 1.5; }
.cg-sum li { margin-bottom: 3px; }
.cg-fine { margin: 12px 0 0; font-size: 12px; color: var(--text-muted); }
.cg-share { margin: 10px 0; padding: 8px 10px; border: 1px solid var(--border); border-radius: 10px; font-size: 13px; overflow-wrap: anywhere; }
.cg-consent-row { display: flex; gap: 10px; align-items: flex-start; margin-top: 12px; font-size: 13.5px; line-height: 1.45; cursor: pointer; }
.cg-consent-row input { width: 22px; height: 22px; flex: 0 0 22px; margin: 1px 0 0; accent-color: #22C55E; }
@media (max-width: 720px) {
  .cons { padding: 18px 14px; margin-top: 28px; }
  .cons-submit { align-self: stretch; }
  .svcp-info dt { flex-basis: 64px; }
}
@media (max-width: 720px) {
  .svcp-sec-head { flex-direction: column; align-items: stretch; gap: 10px; }
  .svcp-art { flex-basis: auto; min-height: 120px; }
  .svcp-art .svc-svg { max-height: 120px; }
  .svcp-grid { grid-template-columns: repeat(2, minmax(0, 1fr)); gap: 10px; }
  .svcp-sec { scroll-margin-top: 70px; }
}

/* ===== Request a Service: chat with Andy ===== */
.rq-chat { display: flex; flex-direction: column; max-width: 680px; margin: 0 auto; height: min(640px, calc(100dvh - 150px)); min-height: 440px; background: var(--card-bg); border: 1px solid var(--border); border-radius: 18px; overflow: hidden; }
.rq-head { display: flex; align-items: center; gap: 12px; padding: 12px 16px; border-bottom: 1px solid var(--border); background: var(--card-bg); }
.rq-avatar, .rq-av { width: 38px; height: 38px; border-radius: 50%; background: var(--accent); color: #04140A; display: flex; align-items: center; justify-content: center; font-family: 'Poppins', sans-serif; font-weight: 700; flex-shrink: 0; }
.rq-av { width: 30px; height: 30px; font-size: 13px; margin-top: 2px; }
.rq-name { font-family: 'Poppins', sans-serif; font-weight: 600; font-size: 15px; color: var(--navy); }
.rq-status { font-size: 12px; color: var(--text-muted); display: flex; align-items: center; gap: 6px; }
.rq-dot { width: 8px; height: 8px; border-radius: 50%; background: #22C55E; }
.rq-body { flex: 1; overflow-y: auto; padding: 16px 14px 8px; display: flex; flex-direction: column; gap: 10px; background: var(--bg); overscroll-behavior: contain; }
.rq-msg { display: flex; gap: 8px; max-width: 88%; animation: rqIn .25s ease both; }
.rq-msg.andy { align-self: flex-start; }
.rq-msg.user { align-self: flex-end; flex-direction: row-reverse; }
.rq-bub { padding: 10px 14px; border-radius: 16px; font-size: 14.5px; line-height: 1.5; word-wrap: break-word; overflow-wrap: anywhere; }
.rq-msg.andy .rq-bub { background: var(--card-bg); border: 1px solid var(--border); color: var(--navy); border-top-left-radius: 4px; }
.rq-msg.user .rq-bub { background: var(--accent); color: #04140A; border-top-right-radius: 4px; }
@keyframes rqIn { from { opacity: 0; transform: translateY(6px); } to { opacity: 1; transform: none; } }
.rq-typing { display: flex; gap: 4px; padding: 14px; }
.rq-typing i { width: 7px; height: 7px; border-radius: 50%; background: var(--text-muted); animation: rqDot 1s infinite ease-in-out; }
.rq-typing i:nth-child(2) { animation-delay: .15s; } .rq-typing i:nth-child(3) { animation-delay: .3s; }
@keyframes rqDot { 0%, 80%, 100% { opacity: .3; transform: scale(.8); } 40% { opacity: 1; transform: scale(1); } }
.rq-quick { display: flex; flex-wrap: wrap; gap: 8px; padding: 6px 14px 4px; background: var(--bg); min-height: 0; }
.rq-quick:empty { display: none; }
.rq-chip { border: 1.5px solid var(--accent); background: var(--card-bg); color: var(--accent); border-radius: 999px; padding: 10px 16px; font-size: 14px; font-weight: 600; cursor: pointer; min-height: 44px; font-family: inherit; transition: background .2s, color .2s; }
.rq-chip.primary { background: var(--accent); color: #04140A; }
@media (hover: hover) { .rq-chip:hover { background: var(--accent); color: #04140A; } }
.rq-composer { display: flex; align-items: flex-end; gap: 8px; padding: 10px 12px calc(10px + env(safe-area-inset-bottom, 0px)); border-top: 1px solid var(--border); background: var(--card-bg); }
.rq-composer textarea { flex: 1; resize: none; border: 1px solid var(--border); border-radius: 20px; padding: 11px 14px; font-size: 15px; font-family: inherit; line-height: 1.4; max-height: 120px; background: var(--bg); color: var(--navy); }
.rq-composer textarea:disabled { opacity: .6; }
.rq-attach, .rq-send { width: 44px; height: 44px; border-radius: 50%; border: none; cursor: pointer; font-size: 18px; flex-shrink: 0; display: flex; align-items: center; justify-content: center; }
.rq-attach { background: var(--chrome-hover, rgba(128,128,128,.14)); }
.rq-send { background: var(--accent); color: #04140A; }
.rq-attach:disabled, .rq-send:disabled { opacity: .4; cursor: default; }
.rq-sum { margin-top: 10px; border-top: 1px solid var(--border); padding-top: 8px; display: grid; gap: 8px; }
.rq-sum span { display: block; font-size: 11px; text-transform: uppercase; letter-spacing: .06em; color: var(--text-muted); }
.rq-sum p { margin: 0; font-size: 14px; white-space: pre-line; }
.rq-thumbs { display: flex; gap: 6px; flex-wrap: wrap; margin-top: 6px; }
.rq-thumb { width: 64px; height: 64px; object-fit: cover; border-radius: 8px; }
.rq-file { font-size: 12px; background: rgba(255,255,255,.35); padding: 4px 8px; border-radius: 8px; }
@media (max-width: 720px) {
  .rq-chat { height: calc(100dvh - 60px - var(--tabs-h) - env(safe-area-inset-bottom, 0px) - 36px); min-height: 380px; border-radius: 14px; }
  .rq-msg { max-width: 94%; }
  .app-footer { display: none; }
}
@media (max-height: 500px) and (orientation: landscape) { .rq-chat { height: calc(100dvh - 80px); min-height: 280px; } }
@media (prefers-reduced-motion: reduce) { .rq-msg { animation: none; } .rq-typing i { animation: none; opacity: .7; } }

/* --- Splash screen --- */
html.no-splash #splash { display: none; }
#splash {
  position: fixed; inset: 0; z-index: 20000; cursor: pointer;
  background: radial-gradient(ellipse at 50% 42%, #12264A 0%, #0A1020 62%);
  display: flex; align-items: center; justify-content: center; text-align: center;
  transition: opacity .7s ease, visibility .7s ease, transform .7s ease;
}
#splash.hide { opacity: 0; visibility: hidden; transform: scale(1.06); }
.splash-glow {
  position: absolute; width: 70vmin; height: 70vmin; border-radius: 50%;
  background: radial-gradient(circle, var(--accent) 0%, transparent 68%);
  opacity: .28; filter: blur(30px); animation: splashGlow 3.2s ease-in-out infinite;
}
.splash-center { position: relative; display: flex; flex-direction: column; align-items: center; padding: 0 20px; }
.splash-float { animation: splashFloat 3.2s ease-in-out infinite, splashIn 1s cubic-bezier(.2,.9,.3,1.2) both; }
.splash-logo {
  display: flex; align-items: center; gap: .28em;
  font-family: 'Poppins', sans-serif; font-weight: 700; color: #fff;
  font-size: clamp(54px, 17vw, 120px); letter-spacing: -.02em;
  filter: drop-shadow(0 0 28px rgba(34,197,94,.45));
}
.splash-word span { color: var(--accent); }
.splash-logo .logo-mark {
  border-left: .55em solid transparent; border-right: .55em solid transparent;
  border-bottom: .95em solid var(--accent);
}
.splash-logo .logo-mark::after {
  left: -.3em; top: .35em; width: .6em; height: .6em;
  border: .1em solid #0A1020; background: rgba(255,255,255,0.15);
}
.splash-shadow {
  width: clamp(120px, 38vw, 260px); height: 14px; margin-top: 26px; border-radius: 50%;
  background: radial-gradient(ellipse, rgba(0,0,0,.65), transparent 70%);
  animation: splashShadow 3.2s ease-in-out infinite;
}
.splash-caption {
  margin-top: 22px; color: rgba(255,255,255,.88); font-family: 'Poppins', sans-serif; font-weight: 600;
  font-size: clamp(14px, 4vw, 20px); letter-spacing: .01em; animation: splashUp .9s .9s ease both;
}
.splash-smile { display: inline-block; animation: splashPop 1.6s 1.6s ease-in-out infinite; }
.splash-bar { position: absolute; left: 0; right: 0; bottom: 0; height: 3px; background: rgba(255,255,255,.08); }
.splash-bar i { display: block; height: 100%; width: 0; background: var(--accent); animation: splashBar 3.7s linear forwards; }
.splash-tap { position: absolute; bottom: 22px; left: 0; right: 0; font-size: 12px; color: rgba(255,255,255,.4); animation: splashUp 1s 1.8s ease both; }
@keyframes splashFloat { 0%,100% { transform: translateY(0); } 50% { transform: translateY(-16px); } }
@keyframes splashShadow { 0%,100% { transform: scaleX(1); opacity: .9; } 50% { transform: scaleX(.78); opacity: .5; } }
@keyframes splashGlow { 0%,100% { opacity: .22; transform: scale(1); } 50% { opacity: .38; transform: scale(1.08); } }
@keyframes splashIn { from { opacity: 0; transform: scale(.4) translateY(30px); } to { opacity: 1; } }
@keyframes splashUp { from { opacity: 0; transform: translateY(14px); } to { opacity: 1; transform: none; } }
@keyframes splashPop { 0%,100% { transform: scale(1) rotate(0); } 50% { transform: scale(1.3) rotate(-8deg); } }
@keyframes splashBar { to { width: 100%; } }
@media (prefers-reduced-motion: reduce) {
  .splash-float, .splash-glow, .splash-shadow, .splash-smile { animation: none; }
}

/* --- Spotlight tour --- */
.tour-block { position: fixed; inset: 0; z-index: 9998; }
.tour-spot {
  position: fixed; z-index: 9999; border-radius: 12px; pointer-events: none;
  box-shadow: 0 0 0 9999px rgba(0,0,0,.78), 0 0 0 3px var(--accent), 0 0 24px 4px var(--accent);
  transition: all .35s ease;
}
.tour-card {
  position: fixed; z-index: 10000; background: #fff; color: #111; border-radius: 16px; padding: 16px 16px 14px;
  box-shadow: 0 12px 40px rgba(0,0,0,.45); font-size: 14px; line-height: 1.45; animation: tourFade .3s ease both; max-width: calc(100vw - 24px);
}
body.dark-mode .tour-card { background: #151a16; color: #eef3ef; }
.tour-x { position: absolute; top: 6px; right: 6px; width: 34px; height: 34px; border: none; border-radius: 50%; background: rgba(128,128,128,.16); color: inherit; font-size: 15px; cursor: pointer; }
.tour-card .tour-title { padding-right: 34px; }
@keyframes tourFade { from { opacity: 0; } to { opacity: 1; } }
.tour-next { min-height: 42px; min-width: 88px; }
.tour-skip { min-height: 42px; }
.tour-title { font-family: 'Poppins', sans-serif; font-weight: 700; font-size: 16px; margin-bottom: 4px; }
.tour-text { opacity: .8; }
.tour-foot { display: flex; align-items: center; justify-content: space-between; margin-top: 14px; gap: 10px; }
.tour-dots { display: flex; gap: 4px; flex-wrap: wrap; }
.tour-dots i { width: 6px; height: 6px; border-radius: 50%; background: rgba(128,128,128,.4); }
.tour-dots i.on { background: var(--accent); width: 16px; border-radius: 4px; }
.tour-skip { background: none; border: none; color: inherit; opacity: .6; font-size: 13px; padding: 8px 10px; cursor: pointer; }
.tour-next { background: var(--accent); color: #fff; border: none; border-radius: 10px; padding: 9px 18px; font-weight: 600; font-size: 13px; cursor: pointer; }

/* --- WhatsApp-style chat --- */
.chat-box { height: 70vh; min-height: 360px; }
.chat-messages { background: #ECE5DD; gap: 3px; }
body.dark-mode .chat-messages { background: #0B141A; }
.msg { position: relative; max-width: 78%; padding: 6px 9px 4px; border-radius: 8px; font-size: 14px; line-height: 1.35; box-shadow: 0 1px 0.5px rgba(0,0,0,0.13); word-wrap: break-word; }
.msg.me { background: #DCF8C6; color: #111; border-top-right-radius: 0; }
.msg.them { background: #fff; color: #111; border-top-left-radius: 0; }
body.dark-mode .msg.me { background: #005C4B; color: #E9EDEF; }
body.dark-mode .msg.them { background: #202C33; color: #E9EDEF; }
.msg-sender { font-size: 11px; font-weight: 600; color: #128C7E; margin-bottom: 2px; }
.msg-meta { float: right; margin: 6px 0 0 10px; font-size: 10.5px; color: rgba(0,0,0,0.45); white-space: nowrap; }
body.dark-mode .msg-meta { color: rgba(255,255,255,0.55); }
.ticks { font-size: 12px; letter-spacing: -2px; color: #8696A0; }
.ticks-read { color: #16A34A; font-weight: 700; }
body.dark-mode .ticks-read { color: #4ADE80; }
.msg::after { content: ""; display: block; clear: both; }
.unread-badge { background: #25D366 !important; color: #fff; min-width: 20px; text-align: center; }
.unread-dot { background: #25D366 !important; color: #fff; }
.chat-row-preview-unread { color: #111; font-weight: 600; }

.unread-badge-old { background: #C0392B; color: #fff; font-size: 10px; font-weight: 700; padding: 1px 7px; border-radius: 10px; margin-left: 6px; display: inline-block; }
.steps-grid { display: grid; grid-template-columns: repeat(auto-fit, minmax(180px, 1fr)); gap: 14px; margin-top: 10px; }
.step-card { background: #fff; border: 1px solid var(--border); border-radius: 14px; padding: 18px; }
body.dark-mode .step-card { background: #111A2E; }
.step-num { width: 28px; height: 28px; border-radius: 50%; background: var(--accent); color: #fff; display: flex; align-items: center; justify-content: center; font-weight: 700; font-size: 13px; margin-bottom: 10px; }
.step-title { font-weight: 600; font-size: 14px; margin-bottom: 4px; }
.step-desc { font-size: 12px; color: var(--text-muted); }
.stats-grid { display: grid; grid-template-columns: repeat(auto-fit, minmax(130px, 1fr)); gap: 12px; }
.stat-tile { background: #fff; border: 1px solid var(--border); border-radius: 14px; padding: 18px; text-align: center; }
body.dark-mode .stat-tile { background: #111A2E; }
.stat-num { font-family: 'Poppins', sans-serif; font-size: 26px; font-weight: 700; color: var(--accent); }
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
body.dark-mode .reel-card { background: #111A2E; }
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
body.dark-mode .settings-card { background: #111A2E; }
.settings-card-header { display: flex; align-items: center; gap: 12px; margin-bottom: 16px; }
.settings-icon { font-size: 22px; }
.settings-card-title { font-family: 'Poppins', sans-serif; font-weight: 600; font-size: 15px; }
.settings-card-sub { font-size: 12px; color: var(--text-muted); }
.profile-avatar {
  width: 56px; height: 56px; border-radius: 50%; background-size: cover; background-position: center;
  background-color: var(--navy); flex-shrink: 0; border: 2px solid var(--accent);
}
.profile-avatar-placeholder {
  display: flex; align-items: center; justify-content: center; color: #fff;
  font-family: 'Poppins', sans-serif; font-weight: 700; font-size: 22px; background: var(--accent);
}
.modal-brand { display: flex; align-items: center; gap: 8px; justify-content: center; margin-bottom: 18px; }
.modal-brand-name { font-family: 'Poppins', sans-serif; font-weight: 700; font-size: 18px; color: var(--navy); }
.modal-headline { font-family: 'Poppins', sans-serif; font-size: 19px; font-weight: 700; }
.chat-search-bar { display: flex; align-items: center; gap: 8px; background: #fff; border: 1px solid var(--border); border-radius: 20px; padding: 10px 16px; margin-bottom: 16px; }
body.dark-mode .chat-search-bar { background: #111A2E; }
.chat-search-bar input { flex: 1; border: none; outline: none; background: transparent; font-size: 14px; color: var(--navy); }
.chat-search-icon { font-size: 14px; opacity: 0.6; }
.chat-row-link { text-decoration: none; }
.chat-row {
  position: relative; display: flex; align-items: center; gap: 12px;
  background: #fff; border: 1px solid var(--border); border-radius: 14px; padding: 14px; margin-bottom: 10px;
}
body.dark-mode .chat-row { background: #111A2E; }
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
.measure-step canvas { touch-action: none; max-width: 100%; border-radius: 12px; display: block; margin: 0 auto; cursor: crosshair; border: 1px solid var(--border); }
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
SERVICE_ART = re.findall(r'<svg viewBox="0 0 400 300" class="svc-svg".*?</svg>', TEMPLATES["home.html"], re.S)
app.jinja_env.globals["service_art"] = SERVICE_ART


@app.context_processor
def inject_unread_count():
    user = current_user()
    out = {"admin_unread_count": 0, "customer_unread_count": 0, "pending_work_count": 0,
           "default_mode": "dark" if os.environ.get("DEFAULT_MODE", "light").lower() == "dark" else "light",
           "current_year": datetime.now().year, "db_supabase": supabase_db_configured(),
           "contact": {"phone": os.environ.get("CONTACT_PHONE", ""), "whatsapp": "".join(c for c in os.environ.get("CONTACT_WHATSAPP", "") if c.isdigit()),
                       "email": os.environ.get("CONTACT_EMAIL", ""), "address": os.environ.get("CONTACT_ADDRESS", "")}}
    if not user:
        return out
    conn = get_db()
    try:
        if is_owner(user):
            out["admin_unread_count"] = _unread_for(user, conn)
            out["pending_work_count"] = conn.execute(
                "SELECT COUNT(*) AS c FROM work_posts WHERE status = 'pending'").fetchone()["c"]
        elif is_customer(user) or is_artisan(user):
            out["customer_unread_count"] = _unread_for(user, conn)
    finally:
        conn.close()
    return out


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
    conn = get_db()
    recent_works = [dict(r) for r in conn.execute(
        "SELECT work_posts.id, work_posts.title, work_posts.category, "
        "(SELECT filename FROM work_photos WHERE work_id = work_posts.id AND COALESCE(kind, 'image') = 'image' ORDER BY id LIMIT 1) AS photo, "
        "(SELECT filename FROM work_photos WHERE work_id = work_posts.id AND kind = 'video' ORDER BY id LIMIT 1) AS video "
        "FROM work_posts WHERE COALESCE(status, 'approved') = 'approved' ORDER BY id DESC LIMIT 6").fetchall()]
    conn.close()
    return render_template("home.html", user=user, site=get_site_content(), hero_photos=get_hero_photos(),
                            recent_works=recent_works, about_slides=get_about_slides(), featured=get_featured_products(),
                            active_page="home", auto_open_auth=False)


@app.route("/about")
def about():
    return render_template("about.html", about_slides=get_about_slides(), user=current_user(), site=get_site_content(),
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
    return redirect(url_for("home"))


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
    return redirect(url_for("home"))


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
            # The link is only ever sent to the account's own email (when SMTP is set up) or shown
            # to the owner in the admin overview. It is NEVER shown to the person making the request.
            if email_configured():
                send_email_async(user["email"], "Reset your ANDY password",
                                 f"Hi {user['name']},\n\nUse this link within 1 hour to choose a new password:\n{reset_link}\n\n"
                                 "If you didn't ask for this, you can ignore this email.\n")
            send_push_to_users([r["id"] for r in conn.execute("SELECT id FROM users WHERE role='owner'").fetchall()],
                               {"title": "🔑 Password reset requested", "body": f"{user['name']} asked to reset their password.",
                                "url": url_for("admin_dashboard"), "tag": "pw-reset"})
        conn.close()
        flash("If that email is registered, a reset link has been sent. If it doesn't arrive, message Andy for help.", "success")
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

def _render_services(user):
    conn = get_db()
    rows = conn.execute("SELECT * FROM products ORDER BY id DESC").fetchall()
    conn.close()
    by_cat = {}
    for r in rows:
        by_cat.setdefault(r["category"], []).append(_product_dict(r))
    # "Custom Solutions" photos have no matching job category, so requests for them go in as custom aluminum work
    sections = [dict(sv, items=by_cat.get(sv["cat"], []),
                     job_cat=sv["cat"] if sv["cat"] in JOB_CATEGORIES else "Aluminum Fabrication") for sv in SERVICES]
    add_cat = request.args.get("add", "")
    return render_template("services.html", user=user, sections=sections, product_categories=PRODUCT_CATEGORIES,
                           add_cat=add_cat if add_cat in PRODUCT_CATEGORIES else "", active_page="services", auto_open_auth=False)


@app.route("/services")
def services():
    return _render_services(current_user())


@app.route("/consultation/guide")
def consult_guide():
    user = current_user()
    return render_template("consult_guide.html", user=user, guide=CONSULT_GUIDE, active_page="services", auto_open_auth=False)


def _consult_reply(wants_json, ok, message, status=None, url=None):
    if wants_json:
        return jsonify(ok=ok, message=message, url=url), (status or (200 if ok else 400))
    flash(message, "success" if ok else "error")
    return redirect(url or url_for("consult_guide"))


@app.route("/consultation", methods=["GET", "POST"])
def consultation_request():
    """Receives a finished guided consultation. It is saved as a normal job so it uses the same thread, attachments and alerts."""
    if request.method == "GET":
        return redirect(url_for("consult_guide"))
    wj = request.headers.get("X-Requested-With") == "fetch"
    user = require_login()
    if not user or not is_customer(user):
        return _consult_reply(wj, False, "Please log in with a customer account to send this request.", 401)

    labels = dict(REQUEST_CHIPS)
    category = request.form.get("category", "")
    topic = " ".join(request.form.get("topic", "").split())[:80]
    summary = request.form.get("summary", "").strip()[:4000]
    location = " ".join(request.form.get("location", "").split())[:120]
    dimensions = " ".join(request.form.get("dimensions", "").split())[:200]
    if category not in labels:
        return _consult_reply(wj, False, "Please start the consultation again and choose a category.")
    if request.form.get("consent") != "1":
        return _consult_reply(wj, False, "Please confirm that you agree to share this summary before sending.")
    if not topic or len(summary) < 20:
        return _consult_reply(wj, False, "The summary looks incomplete. Please go back and finish the questions.")

    title = f"Consultation: {topic}"[:120]
    lines = ["Consultation request (guided consultation)", f"Service category: {labels[category]}"]
    if location:
        lines.append(f"Project location: {location}")
    if dimensions:
        lines.append(f"Dimensions given by customer (estimate, not verified): {dimensions}")
    lines.append("The customer agreed to share this summary.")
    description = "\n".join(lines) + "\n\n" + summary

    conn = None
    try:
        conn = get_db()
        dup = conn.execute(
            "SELECT id FROM jobs WHERE customer_id=? AND title=? AND description=? AND status != 'cancelled' ORDER BY id DESC LIMIT 1",
            (user["id"], title, description)).fetchone()
        if dup:  # the same request was already sent (double tap or retry), so don't create a second one
            job_id = dup["id"]
            conn.close()
            return _consult_reply(wj, True, "This request was already sent. Here is its conversation.", url=url_for("job_thread", job_id=job_id))
        cur = conn.execute(
            "INSERT INTO jobs (customer_id, title, description, category, track, status) VALUES (?, ?, ?, ?, 'standard', 'submitted')",
            (user["id"], title, description, category))
        job_id = cur.lastrowid
        skipped = 0
        files = [f for f in request.files.getlist("attachments") if f and f.filename]
        for f in files[:6]:
            stored, kind = _save_attachment(f, ATTACHMENTS_UPLOAD_DIR)
            if stored:
                conn.execute("INSERT INTO job_attachments (job_id, filename, kind) VALUES (?, ?, ?)", (job_id, stored, kind))
            else:
                skipped += 1
        skipped += max(0, len(files) - 6)
        conn.commit()
        conn.close()
    except Exception as exc:
        print("[ANDY] Consultation request failed:", exc)
        try:
            if conn:
                conn.close()
        except Exception:
            pass
        return _consult_reply(wj, False, "Sorry, we could not send your request just now and nothing was submitted. Please try again.", 500)

    _notify_owner_new_request(user, {"id": job_id, "title": title, "category": category,
                                     "customer_id": user["id"], "artisan_id": None}, description, "consultation request")
    msg = "Your consultation request has been sent. It has not been confirmed or scheduled yet. You can follow up in this conversation."
    if skipped:
        msg += f" {skipped} file{'s' if skipped != 1 else ''} could not be attached (photos and PDF, Word, Excel or text files only, up to 6)."
    return _consult_reply(wj, True, msg, url=url_for("job_thread", job_id=job_id))


@app.route("/services/add", methods=["POST"])
def services_add():
    user = require_owner()
    if not user:
        return redirect(url_for("home"))
    category = request.form.get("category", "")
    slug = next((sv["slug"] for sv in SERVICES if sv["cat"] == category), "")
    back = url_for("services") + (f"#{slug}" if slug else "")
    name = " ".join(request.form.get("name", "").split())[:120]
    description = request.form.get("description", "").strip()[:600]
    try:
        price = max(0, int(request.form.get("price") or 0))
    except ValueError:
        price = 0
    if category not in PRODUCT_CATEGORIES or not name:
        flash("Choose a category and give the photo a short name.", "error")
        return redirect(back)
    files = [f for f in request.files.getlist("images") if f and f.filename][:12]
    conn = get_db()
    saved = 0
    for i, f in enumerate(files):
        stored, kind = _save_attachment(f, PRODUCTS_UPLOAD_DIR)
        if stored and kind == "image":
            conn.execute("INSERT INTO products (name, category, description, price, sizes_csv, image_filename, video_url) VALUES (?, ?, ?, ?, ?, ?, ?)",
                         (name + (f" {i + 1}" if len(files) > 1 else ""), category, description, price, "", stored, ""))
            saved += 1
    conn.commit()
    conn.close()
    flash(f"{saved} photo{'s' if saved != 1 else ''} added to {category}." if saved else "Please choose at least one JPG, PNG or WEBP photo.", "success" if saved else "error")
    return redirect(back)


@app.route("/request-service", methods=["GET", "POST"])
def request_service():
    user = require_login()
    if not user or not is_customer(user):
        flash("Log in as a customer to request a service.", "error")
        return redirect(url_for("home"))

    if request.method == "POST":
        title = " ".join(request.form.get("title", "").split())[:120]
        category = request.form.get("category", "Other")
        if category not in JOB_CATEGORIES:
            category = "Other"
        description = request.form.get("description", "").strip()[:3000]
        if not title or len(description) < 10:
            flash("Please add a short title and describe the job in at least a sentence.", "error")
            return redirect(url_for("request_service"))

        conn = get_db()
        cur = conn.execute(
            "INSERT INTO jobs (customer_id, title, description, category, track, status) VALUES (?, ?, ?, ?, 'standard', 'submitted')",
            (user["id"], title, description, category),
        )
        job_id = cur.lastrowid
        files = request.files.getlist("attachments")[:6]
        for f in files:
            stored, kind = _save_attachment(f, ATTACHMENTS_UPLOAD_DIR)
            if stored:
                conn.execute("INSERT INTO job_attachments (job_id, filename, kind) VALUES (?, ?, ?)", (job_id, stored, kind))
        conn.commit()
        conn.close()
        _notify_owner_new_request(user, {"id": job_id, "title": title, "category": category,
                                         "customer_id": user["id"], "artisan_id": None}, description)
        flash("Request submitted! Andy will review it shortly.", "success")
        return redirect(url_for("job_thread", job_id=job_id))

    prefill = request.args.get("category", "")
    labels = dict(REQUEST_CHIPS)
    if prefill and prefill not in JOB_CATEGORIES:
        prefill = ""
    return render_template("request_service.html", user=user, categories=JOB_CATEGORIES,
                            chips=[{"value": v, "label": l} for v, l in REQUEST_CHIPS],
                            prefill=prefill, prefill_label=labels.get(prefill, prefill),
                            first_name=(user["name"] or "there").split()[0],
                            active_page="request_service", auto_open_auth=False)


def _open_support_thread(category, title, description):
    user = require_login()
    if not user or not (is_customer(user) or is_artisan(user)):
        return redirect(url_for("home"))
    artisan_row = get_artisan_profile(user["id"]) if is_artisan(user) else None
    if is_artisan(user) and not artisan_row:
        return redirect(url_for("home"))
    conn = get_db()
    existing = conn.execute(
        "SELECT * FROM jobs WHERE customer_id=? AND category=? AND status != 'completed' AND status != 'cancelled' ORDER BY id DESC LIMIT 1",
        (user["id"], category),
    ).fetchone()
    if existing:
        conn.close()
        return redirect(url_for("job_thread", job_id=existing["id"]))
    cur = conn.execute(
        "INSERT INTO jobs (customer_id, artisan_id, title, description, category, track, status) VALUES (?, ?, ?, ?, ?, 'standard', 'submitted')",
        (user["id"], artisan_row["id"] if artisan_row else None, title, description, category),
    )
    job_id = cur.lastrowid
    conn.commit()
    conn.close()
    return redirect(url_for("job_thread", job_id=job_id))


@app.route("/contact-support")
def contact_support():
    return _open_support_thread("General Support", "General Support", "Support conversation with Andy.")


@app.route("/support/feedback")
def support_feedback():
    return _open_support_thread("Feedback", "Feedback", "Share your feedback with the Andy team.")


@app.route("/support/bug")
def support_bug():
    return _open_support_thread("Bug Report", "Bug Report", "Tell us what went wrong and we will look into it.")


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
        WHERE jobs.artisan_id = ? AND COALESCE(jobs.category, '') NOT IN ('General Support', 'Feedback', 'Bug Report')
        ORDER BY jobs.id DESC
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
    _mark_read(conn, user, job_id)
    messages = [dict(m) for m in conn.execute("""
        SELECT messages.*, users.name AS sender_name, users.avatar_filename AS sender_avatar
        FROM messages JOIN users ON messages.sender_id = users.id
        WHERE messages.job_id=? ORDER BY messages.id
    """, (job_id,)).fetchall()]

    _mark_read(conn, user, job_id)
    for m in messages:
        m["is_read"] = _is_read_by_other(m)

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
        payments_enabled=paystack_configured(), statuses=JOB_STATUSES,
        artisan_name=artisan_name, attachments=attachments, messages=messages, artisans=artisans,
        review=review, is_owner_view=is_owner(user), is_customer_view=is_customer(user),
        active_page="my_jobs", auto_open_auth=False,
    )



def _message_payload(m, user):
    """Serialise one message row for the live-chat JSON feed."""
    d = dict(m)
    other_read = _is_read_by_other(d)
    avatar = d.get("sender_avatar")
    return {
        "id": d["id"], "sender_id": d["sender_id"], "sender_name": d["sender_name"],
        "sender_role_label": (d["sender_role"] or "").title(),
        "text": d.get("text") or "",
        "attachment_url": photo_url_filter(d["attachment_filename"], "attachments") if d.get("attachment_filename") else "",
        "attachment_kind": d.get("attachment_kind") or "",
        "avatar_url": photo_url_filter(avatar, "avatars") if avatar else "",
        "time": str(d.get("created_at") or "")[11:16],
        "is_read": bool(other_read),
    }


def _is_read_by_other(d):
    role = d.get("sender_role")
    if role == "customer":
        return bool(d.get("read_by_owner"))
    if role == "owner":
        return bool(d.get("read_by_customer") or d.get("read_by_artisan"))
    return bool(d.get("read_by_owner") or d.get("read_by_customer"))


def _unread_for(user, conn):
    if is_owner(user):
        return conn.execute("SELECT COUNT(*) AS c FROM messages WHERE sender_role != 'owner' AND read_by_owner = 0").fetchone()["c"]
    if is_customer(user):
        return conn.execute(
            "SELECT COUNT(*) AS c FROM messages JOIN jobs ON messages.job_id = jobs.id "
            "WHERE jobs.customer_id = ? AND messages.sender_role != 'customer' AND messages.read_by_customer = 0",
            (user["id"],)).fetchone()["c"]
    if is_artisan(user):
        return conn.execute(
            "SELECT COUNT(*) AS c FROM messages JOIN jobs ON messages.job_id = jobs.id "
            "WHERE jobs.artisan_id = (SELECT id FROM artisans WHERE user_id = ?) "
            "AND messages.sender_role != 'artisan' AND messages.read_by_artisan = 0",
            (user["id"],)).fetchone()["c"]
    return 0


def _mark_read(conn, user, job_id):
    if is_owner(user):
        conn.execute("UPDATE messages SET read_by_owner = 1 WHERE job_id = ? AND sender_role != 'owner'", (job_id,))
    if is_customer(user):
        conn.execute("UPDATE messages SET read_by_customer = 1 WHERE job_id = ? AND sender_role != 'customer'", (job_id,))
    if is_artisan(user):
        conn.execute("UPDATE messages SET read_by_artisan = 1 WHERE job_id = ? AND sender_role != 'artisan'", (job_id,))
    conn.commit()


_MSG_SELECT = """
    SELECT messages.*, users.name AS sender_name, users.avatar_filename AS sender_avatar
    FROM messages JOIN users ON messages.sender_id = users.id
"""


def _feed(conn, user, job_id, after):
    _mark_read(conn, user, job_id)
    new_rows = conn.execute(_MSG_SELECT + " WHERE messages.job_id=? AND messages.id>? ORDER BY messages.id", (job_id, after)).fetchall()
    mine_rows = conn.execute(_MSG_SELECT + " WHERE messages.job_id=? AND messages.sender_id=? ORDER BY messages.id", (job_id, user["id"])).fetchall()
    return {
        "messages": [_message_payload(r, user) for r in new_rows],
        "read_ids": [dict(r)["id"] for r in mine_rows if _is_read_by_other(dict(r))],
        "unread": _unread_for(user, conn),
    }


@app.route("/job/<int:job_id>/messages.json")
def job_messages_json(job_id):
    user = require_login()
    if not user:
        return jsonify({"error": "auth"}), 401
    conn = get_db()
    job = conn.execute("SELECT * FROM jobs WHERE id=?", (job_id,)).fetchone()
    if not job or not job_visible_to(user, dict(job)):
        conn.close()
        return jsonify({"error": "forbidden"}), 403
    after = request.args.get("after", 0, type=int)
    data = _feed(conn, user, job_id, after)
    conn.close()
    resp = jsonify(data)
    resp.headers["Cache-Control"] = "no-store"
    return resp


@app.route("/api/unread")
def api_unread():
    user = require_login()
    if not user:
        return jsonify({"unread": 0})
    conn = get_db()
    n = _unread_for(user, conn)
    conn.close()
    resp = jsonify({"unread": n})
    resp.headers["Cache-Control"] = "no-store"
    return resp


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
        artisan_read_flag = 1 if user["role"] == "artisan" else 0
        conn.execute(
            "INSERT INTO messages (job_id, sender_id, sender_role, text, attachment_filename, attachment_kind, read_by_owner, read_by_customer, read_by_artisan) VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?)",
            (job_id, user["id"], user["role"], text, attachment_value or "", attachment_kind or "", owner_read_flag, customer_read_flag, artisan_read_flag),
        )
        conn.commit()
        if user["role"] != "owner":
            _notify_owner_of_message(user, dict(job), text, attachment_kind)
        _notify_push(user, dict(job), text, attachment_kind)
    if request.headers.get("X-Requested-With") == "fetch":
        # return everything newer than what the sender's page has
        last_seen = request.form.get("after", 0, type=int) or 0
        data = _feed(conn, user, job_id, last_seen)
        conn.close()
        return jsonify(data)
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
    if artisan_id:
        ok = conn.execute("SELECT id FROM artisans WHERE id=? AND active=1", (artisan_id,)).fetchone()
        artisan_id = ok["id"] if ok else None
    track = request.form.get("track", "standard")
    if track not in ("standard", "eas"):
        track = "standard"
    try:
        amount = max(0, int(request.form.get("amount", 0)))
    except ValueError:
        amount = 0

    chosen = request.form.get("status", job["status"])
    if chosen not in JOB_STATUSES:
        chosen = job["status"]
    new_status = chosen
    if chosen == job["status"] and artisan_id and job["status"] == "submitted":
        new_status = "assigned"          # assigning an artisan moves a new request forward

    conn.execute("UPDATE jobs SET artisan_id=?, track=?, amount=?, status=? WHERE id=?",
                 (artisan_id, track, amount, new_status, job_id))
    fresh = dict(conn.execute("SELECT * FROM jobs WHERE id=?", (job_id,)).fetchone())
    if new_status != job["status"]:
        if new_status == "cancelled":
            _refund_escrow(conn, fresh)
        elif new_status == "completed":
            _release_escrow(conn, fresh)
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
    if not paystack_configured():
        conn.close()
        flash("In-app payment isn't switched on yet. Andy will share payment details in this chat.", "error")
        return redirect(url_for("job_thread", job_id=job_id))
    if not job or job["status"] != "assigned" or not job["amount"]:
        conn.close()
        flash("This job isn't ready for payment yet.", "error")
        return redirect(url_for("job_thread", job_id=job_id))
    # Conditional updates make a double-tap or two parallel requests safe: only one can win.
    moved = conn.execute("UPDATE jobs SET status='in_progress', escrow_held=1 WHERE id=? AND status='assigned'", (job_id,))
    charged = conn.execute("UPDATE users SET wallet = wallet - ? WHERE id=? AND wallet >= ?", (job["amount"], user["id"], job["amount"])) if moved.rowcount == 1 else None
    if moved.rowcount != 1 or charged is None or charged.rowcount != 1:
        conn.rollback()
        conn.close()
        flash("Not enough CONNECT coins (or this job was already paid). Top up your wallet first.", "error")
        return redirect(url_for("job_thread", job_id=job_id))
    conn.execute("INSERT INTO transactions (user_id, label, amount) VALUES (?, ?, ?)",
                 (user["id"], f"Payment for job: {job['title']} (held in escrow)", -job["amount"]))
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
    done = conn.execute("UPDATE jobs SET status='completed' WHERE id=? AND status='in_progress'", (job_id,))
    if done.rowcount != 1:
        conn.rollback()
        conn.close()
        return redirect(url_for("job_thread", job_id=job_id))
    _release_escrow(conn, dict(job))
    conn.commit()
    conn.close()
    flash("Job marked complete." + (" Payment released to your artisan." if job["escrow_held"] else ""), "success")
    return redirect(url_for("job_thread", job_id=job_id))


def _release_escrow(conn, job):
    """Pays the artisan from escrow ONCE, and only if the customer really paid in-app."""
    tech = conn.execute("SELECT * FROM artisans WHERE id=?", (job["artisan_id"],)).fetchone() if job.get("artisan_id") else None
    if tech:
        conn.execute("UPDATE artisans SET jobs_completed = jobs_completed + 1 WHERE id=?", (tech["id"],))
    if tech and job.get("escrow_held") and job.get("amount"):
        took = conn.execute("UPDATE jobs SET escrow_held=0 WHERE id=? AND escrow_held=1", (job["id"],))
        if took.rowcount == 1:
            conn.execute("UPDATE users SET wallet = wallet + ? WHERE id=?", (job["amount"], tech["user_id"]))
            conn.execute("INSERT INTO transactions (user_id, label, amount) VALUES (?, ?, ?)",
                         (tech["user_id"], f"Payment released: {job['title']}", job["amount"]))


def _refund_escrow(conn, job):
    took = conn.execute("UPDATE jobs SET escrow_held=0 WHERE id=? AND escrow_held=1", (job["id"],))
    if took.rowcount == 1 and job.get("amount"):
        conn.execute("UPDATE users SET wallet = wallet + ? WHERE id=?", (job["amount"], job["customer_id"]))
        conn.execute("INSERT INTO transactions (user_id, label, amount) VALUES (?, ?, ?)",
                     (job["customer_id"], f"Refund: {job['title']} (cancelled)", job["amount"]))


@app.route("/job/<int:job_id>/cancel", methods=["POST"])
def cancel_job(job_id):
    user = require_login()
    if not user or not is_customer(user):
        return redirect(url_for("home"))
    conn = get_db()
    job = conn.execute("SELECT * FROM jobs WHERE id=? AND customer_id=?", (job_id, user["id"])).fetchone()
    if not job or job["status"] not in ("submitted", "assigned") or (job["category"] or "") in ("General Support", "Feedback", "Bug Report"):
        conn.close()
        flash("This request can't be cancelled here. Message Andy in the chat and we will help.", "error")
        return redirect(url_for("job_thread", job_id=job_id))
    conn.execute("UPDATE jobs SET status='cancelled' WHERE id=? AND status IN ('submitted', 'assigned')", (job_id,))
    owners = [r["id"] for r in conn.execute("SELECT id FROM users WHERE role='owner'").fetchall()]
    conn.commit()
    conn.close()
    send_push_to_users(owners, {"title": "Request cancelled", "body": f"{user['name']} cancelled “{job['title']}”.",
                                "url": url_for("job_thread", job_id=job_id), "tag": f"job-{job_id}"})
    flash("Your request was cancelled.", "success")
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
    resets = []
    for r in conn.execute("SELECT name, email, reset_token, reset_token_expires FROM users WHERE reset_token IS NOT NULL AND reset_token != ''").fetchall():
        try:
            if __import__("datetime").datetime.fromisoformat(str(r["reset_token_expires"])) > __import__("datetime").datetime.utcnow():
                resets.append({"name": r["name"], "email": r["email"], "link": url_for("reset_password", token=r["reset_token"], _external=True)})
        except Exception:
            pass
    conn.close()
    warnings = []
    try:
        if check_password_hash(user["password_hash"], "changeme123"):
            warnings.append("Your owner password is still the old default. Change it now in Settings.")
    except Exception:
        pass
    if not os.environ.get("SECRET_KEY"):
        warnings.append("SECRET_KEY is not set on the server, so everyone is logged out whenever it restarts.")
    if not supabase_db_configured():
        warnings.append("Data is stored in a local file. On free Render hosting it can be wiped on redeploy. Set SUPABASE_DB_URL for permanent storage.")
    stats = {"customers": customers, "artisans": artisans, "pending_jobs": pending_jobs, "eas_jobs": eas_jobs}
    return render_template("admin_dashboard.html", user=user, stats=stats, recent_jobs=[dict(r) for r in recent],
                            warnings=warnings, resets=resets, active_page="admin_dashboard", auto_open_auth=False)


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
    name = " ".join(name.split())[:60]
    if len(name) < 2 or not re.fullmatch(r"[^@\s]+@[^@\s]+\.[^@\s]+", email) or len(password) < 8:
        flash("Please enter a name, a valid email and a password of at least 8 characters.", "error")
        return redirect(url_for("admin_artisans"))

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
    counts = {r["category"]: r["c"] for r in conn.execute("SELECT category, COUNT(*) AS c FROM products GROUP BY category").fetchall()}
    conn.close()
    products = [_product_dict(r) for r in rows]
    return render_template("catalog.html", user=user, products=products, categories=PRODUCT_CATEGORIES, counts=counts,
                            total_products=sum(counts.values()), active_cat=active_cat, active_page="catalog", auto_open_auth=False)


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
    if product["price"] <= 0:
        conn.close()
        flash("This item is priced on request. Tell Andy what you need and we will quote you.", "success")
        return redirect(url_for("request_service", category=product["category"]))
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
    if not name or price < 0:
        flash("Give the item a name. Leave the price at 0 to show 'Ask for a quote'.", "error")
        return redirect(_safe_next(url_for("dashboard_catalog")))

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
    flash("Removed.", "success")
    return redirect(_safe_next(url_for("dashboard_catalog")))


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
    if not user or not (is_customer(user) or is_artisan(user)):
        return redirect(url_for("home"))
    conn = get_db()
    if is_artisan(user):
        tech = get_artisan_profile(user["id"])
        rows = conn.execute("""
            SELECT jobs.id AS job_id, jobs.title, jobs.status,
                   (SELECT text FROM messages WHERE job_id = jobs.id ORDER BY id DESC LIMIT 1) AS last_text,
                   (SELECT created_at FROM messages WHERE job_id = jobs.id ORDER BY id DESC LIMIT 1) AS last_at,
                   (SELECT COUNT(*) FROM messages WHERE job_id = jobs.id AND sender_role != 'artisan' AND read_by_artisan = 0) AS unread
            FROM jobs WHERE jobs.artisan_id = ?
            AND EXISTS (SELECT 1 FROM messages WHERE messages.job_id = jobs.id AND messages.sender_role != 'artisan')
            ORDER BY last_at DESC
        """, (tech["id"] if tech else -1,)).fetchall()
    else:
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
        category = request.form.get("category", "").strip()
        category = category if category in WORK_CATEGORIES else ""
        if not title:
            flash("Give the project a title.", "error")
            return redirect(_safe_next(url_for("works")))
        conn = get_db()
        cur = conn.execute("INSERT INTO work_posts (title, description, category, status) VALUES (?, ?, ?, 'approved')", (title, description, category))
        work_id = cur.lastrowid
        _save_work_media(conn, work_id, request.files.getlist("photos"), limit=12)
        conn.commit()
        conn.close()
        flash("Work posted.", "success")
        return redirect(_safe_next(url_for("works")))

    conn = get_db()
    rows = conn.execute("SELECT * FROM work_posts WHERE COALESCE(status, 'approved') = 'approved' ORDER BY id DESC").fetchall()
    posts = []
    for r in rows:
        w = dict(r)
        photos = conn.execute("SELECT * FROM work_photos WHERE work_id=?", (w["id"],)).fetchall()
        w["photos"] = [dict(p) for p in photos]
        posts.append(w)
    for w in posts:
        w["like_count"] = conn.execute("SELECT COUNT(*) AS c FROM work_likes WHERE work_id=?", (w["id"],)).fetchone()["c"]
        w["liked"] = bool(user and conn.execute("SELECT 1 FROM work_likes WHERE work_id=? AND user_id=?", (w["id"], user["id"])).fetchone())
        revs = conn.execute(
            "SELECT work_reviews.id, work_reviews.user_id, work_reviews.rating, work_reviews.text, users.name AS name "
            "FROM work_reviews JOIN users ON work_reviews.user_id = users.id WHERE work_reviews.work_id=? ORDER BY work_reviews.id DESC",
            (w["id"],)).fetchall()
        w["reviews"] = []
        for r in revs:
            d = dict(r)
            d["display_name"] = _short_name(d.pop("name"))
            d["like_count"] = conn.execute("SELECT COUNT(*) AS c FROM review_likes WHERE review_id=?", (d["id"],)).fetchone()["c"]
            d["liked"] = bool(user and conn.execute("SELECT 1 FROM review_likes WHERE review_id=? AND user_id=?", (d["id"], user["id"])).fetchone())
            w["reviews"].append(d)
        w["review_count"] = len(w["reviews"])
        w["avg_rating"] = (sum(r["rating"] for r in w["reviews"]) / len(w["reviews"])) if w["reviews"] else 0
        w["my_review"] = next((r for r in w["reviews"] if user and r["user_id"] == user["id"]), None)
    conn.close()
    return render_template("works.html", user=user, work_posts=posts, is_owner_view=is_owner(user), categories=WORK_CATEGORIES,
                            active_page="works", auto_open_auth=False)


MEDIA_ACCEPT = ".jpg,.jpeg,.png,.webp,.mp4,.mov,.webm,.m4v"


def _save_work_media(conn, work_id, files, limit=8):
    """Saves photos AND videos (sound kept) for a work post. Returns how many were stored."""
    n = 0
    for f in [f for f in files if f and f.filename][:limit]:
        stored, kind = _save_attachment(f, WORKS_UPLOAD_DIR, allow_video=True)
        if stored and kind in ("image", "video"):
            conn.execute("INSERT INTO work_photos (work_id, filename, kind) VALUES (?, ?, ?)", (work_id, stored, kind))
            n += 1
    return n


def _short_name(name):
    parts = (name or "Customer").split()
    if len(parts) > 1:
        return f"{parts[0]} {parts[-1][0].upper()}."
    return parts[0] if parts else "Customer"


@app.route("/works/<int:work_id>/review", methods=["POST"])
def work_review(work_id):
    user = require_login()
    anchor = f"#reviews-{work_id}"
    if not user:
        return redirect(url_for("works") + anchor)
    if not is_customer(user):
        flash("Only customers can leave reviews.", "error")
        return redirect(url_for("works") + anchor)
    try:
        rating = int(request.form.get("rating", "0"))
    except ValueError:
        rating = 0
    if rating < 1 or rating > 5:
        flash("Please pick a star rating.", "error")
        return redirect(url_for("works") + anchor)
    text = request.form.get("text", "").strip()[:500]
    text = mask_phone_numbers(text) if text else text
    conn = get_db()
    work = conn.execute("SELECT id FROM work_posts WHERE id=? AND COALESCE(status,'approved')='approved'", (work_id,)).fetchone()
    if not work:
        conn.close()
        return redirect(url_for("works"))
    cutoff = (datetime.utcnow() - __import__("datetime").timedelta(hours=1)).strftime("%Y-%m-%d %H:%M:%S")
    recent = conn.execute("SELECT COUNT(*) AS c FROM work_reviews WHERE user_id=? AND created_at > ?", (user["id"], cutoff)).fetchone()["c"]
    if recent >= 20:
        conn.close()
        flash("You're reviewing a lot. Please try again later.", "error")
        return redirect(url_for("works") + anchor)
    conn.execute("DELETE FROM work_reviews WHERE work_id=? AND user_id=?", (work_id, user["id"]))
    conn.execute("INSERT INTO work_reviews (work_id, user_id, rating, text, created_at) VALUES (?, ?, ?, ?, ?)",
                 (work_id, user["id"], rating, text, datetime.utcnow().strftime("%Y-%m-%d %H:%M:%S")))
    owners = [r["id"] for r in conn.execute("SELECT id FROM users WHERE role='owner'").fetchall()]
    title = conn.execute("SELECT title FROM work_posts WHERE id=?", (work_id,)).fetchone()["title"]
    conn.commit()
    conn.close()
    send_push_to_users(owners, {"title": f"{'★' * rating} New review", "body": f"{_short_name(user['name'])} on “{title}”: {text}"[:140],
                                "url": url_for("works") + anchor, "tag": f"review-{work_id}"})
    flash("Thanks for your review!", "success")
    return redirect(url_for("works") + anchor)


def _toggle_like(table, key_col, key_val):
    user = current_user()
    if not user:
        return jsonify({"error": "auth"}), 401
    conn = get_db()
    exists = conn.execute(f"SELECT 1 FROM {table} WHERE {key_col}=? AND user_id=?", (key_val, user["id"])).fetchone()
    if exists:
        conn.execute(f"DELETE FROM {table} WHERE {key_col}=? AND user_id=?", (key_val, user["id"]))
    else:
        conn.execute(f"INSERT INTO {table} ({key_col}, user_id) VALUES (?, ?)", (key_val, user["id"]))
    conn.commit()
    count = conn.execute(f"SELECT COUNT(*) AS c FROM {table} WHERE {key_col}=?", (key_val,)).fetchone()["c"]
    conn.close()
    return jsonify({"liked": not exists, "count": count})


@app.route("/works/<int:work_id>/like", methods=["POST"])
def work_like(work_id):
    conn = get_db()
    ok = conn.execute("SELECT 1 FROM work_posts WHERE id=? AND COALESCE(status,'approved')='approved'", (work_id,)).fetchone()
    conn.close()
    if not ok:
        return jsonify({"error": "missing"}), 404
    return _toggle_like("work_likes", "work_id", work_id)


@app.route("/works/review/<int:review_id>/like", methods=["POST"])
def work_review_like(review_id):
    conn = get_db()
    ok = conn.execute("SELECT 1 FROM work_reviews WHERE id=?", (review_id,)).fetchone()
    conn.close()
    if not ok:
        return jsonify({"error": "missing"}), 404
    return _toggle_like("review_likes", "review_id", review_id)


@app.route("/works/review/<int:review_id>/delete", methods=["POST"])
def work_review_delete(review_id):
    user = require_login()
    if not user:
        return redirect(url_for("works"))
    conn = get_db()
    r = conn.execute("SELECT * FROM work_reviews WHERE id=?", (review_id,)).fetchone()
    work_id = r["work_id"] if r else None
    if r and (is_owner(user) or r["user_id"] == user["id"]):
        conn.execute("DELETE FROM review_likes WHERE review_id=?", (review_id,))
        conn.execute("DELETE FROM work_reviews WHERE id=?", (review_id,))
        conn.commit()
        flash("Review deleted.", "success")
    conn.close()
    return redirect(url_for("works") + (f"#reviews-{work_id}" if work_id else ""))


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
    conn.execute("DELETE FROM work_likes WHERE work_id=?", (work_id,))
    conn.execute("DELETE FROM work_posts WHERE id=?", (work_id,))
    conn.execute("DELETE FROM review_likes WHERE review_id IN (SELECT id FROM work_reviews WHERE work_id=?)", (work_id,))
    conn.execute("DELETE FROM work_reviews WHERE work_id=?", (work_id,))
    conn.execute("DELETE FROM work_likes WHERE work_id=?", (work_id,))
    conn.commit()
    conn.close()
    flash("Work post removed.", "success")
    return redirect(_safe_next(url_for("works")))


# ---------------------------------------------------------------------------
# OUR WORK — owner uploads + artisan submissions reviewed by the owner.
# Artisan work only goes live after approval, and is shown as ANDY's work
# (no artisan name is ever shown to the public).
# ---------------------------------------------------------------------------
WORK_CATEGORIES = ["Windows", "Doors", "Partitions", "Gates & Rails", "Other"]


def _safe_next(default):
    nxt = request.form.get("next", "")
    return nxt if nxt.startswith("/") and not nxt.startswith("//") else default


def _load_work_posts(conn, where, params=()):
    rows = conn.execute(
        "SELECT work_posts.*, users.name AS submitter FROM work_posts "
        "LEFT JOIN users ON work_posts.submitted_by = users.id "
        f"WHERE {where} ORDER BY work_posts.id DESC", params).fetchall()
    out = []
    for r in rows:
        w = dict(r)
        w["photos"] = [dict(p) for p in conn.execute("SELECT * FROM work_photos WHERE work_id=?", (w["id"],)).fetchall()]
        out.append(w)
    return out


def _delete_work_files(conn, work_id):
    for p in conn.execute("SELECT * FROM work_photos WHERE work_id=?", (work_id,)).fetchall():
        if not p["filename"].startswith("http"):
            try:
                os.remove(os.path.join(WORKS_UPLOAD_DIR, p["filename"]))
            except OSError:
                pass
    conn.execute("DELETE FROM work_photos WHERE work_id=?", (work_id,))
    conn.execute("DELETE FROM work_posts WHERE id=?", (work_id,))


@app.route("/admin/works")
def admin_works():
    user = require_owner()
    if not user:
        return redirect(url_for("home"))
    conn = get_db()
    pending = _load_work_posts(conn, "work_posts.status = 'pending'")
    published = _load_work_posts(conn, "COALESCE(work_posts.status, 'approved') = 'approved'")
    conn.close()
    return render_template("admin_works.html", user=user, pending=pending, published=published,
                           categories=WORK_CATEGORIES, active_page="admin_works", auto_open_auth=False)


@app.route("/admin/works/<int:work_id>/approve", methods=["POST"])
def admin_work_approve(work_id):
    user = require_owner()
    if not user:
        return redirect(url_for("home"))
    conn = get_db()
    w = conn.execute("SELECT * FROM work_posts WHERE id=?", (work_id,)).fetchone()
    if not w:
        conn.close()
        return redirect(url_for("admin_works"))
    title = request.form.get("title", "").strip() or w["title"]
    description = request.form.get("description", "").strip()
    category = request.form.get("category", "").strip()
    category = category if category in WORK_CATEGORIES else ""
    conn.execute("UPDATE work_posts SET title=?, description=?, category=?, status='approved', reject_reason='' WHERE id=?",
                 (title, description, category, work_id))
    conn.commit()
    submitter = w["submitted_by"]
    conn.close()
    if submitter:
        send_push_to_users([submitter], {"title": "✅ Your work is live", "body": f"“{title}” was approved and is now on Our Work.",
                                         "url": url_for("artisan_work"), "tag": f"work-{work_id}"})
    flash("Approved. It is now live on Our Work.", "success")
    return redirect(url_for("admin_works"))


@app.route("/admin/works/<int:work_id>/reject", methods=["POST"])
def admin_work_reject(work_id):
    user = require_owner()
    if not user:
        return redirect(url_for("home"))
    reason = request.form.get("reason", "").strip()[:200]
    conn = get_db()
    w = conn.execute("SELECT * FROM work_posts WHERE id=?", (work_id,)).fetchone()
    if w:
        conn.execute("UPDATE work_posts SET status='rejected', reject_reason=? WHERE id=?", (reason, work_id))
        conn.commit()
    conn.close()
    if w and w["submitted_by"]:
        send_push_to_users([w["submitted_by"]], {"title": "Work not approved", "body": reason or f"“{w['title']}” wasn't approved this time.",
                                                  "url": url_for("artisan_work"), "tag": f"work-{work_id}"})
    flash("Sent back to the artisan.", "success")
    return redirect(url_for("admin_works"))


@app.route("/artisan/work", methods=["GET", "POST"])
def artisan_work():
    user = require_login()
    if not user or not is_artisan(user):
        return redirect(url_for("home"))
    conn = get_db()
    if request.method == "POST":
        action = request.form.get("action", "submit")
        if action == "delete":
            w = conn.execute("SELECT * FROM work_posts WHERE id=? AND submitted_by=? AND status != 'approved'",
                             (request.form.get("work_id", type=int), user["id"])).fetchone()
            if w:
                _delete_work_files(conn, w["id"])
                conn.commit()
                flash("Removed.", "success")
            conn.close()
            return redirect(url_for("artisan_work"))
        title = " ".join(request.form.get("title", "").split())[:120]
        description = request.form.get("description", "").strip()[:1000]
        description = mask_phone_numbers(description) if description else description
        category = request.form.get("category", "").strip()
        category = category if category in WORK_CATEGORIES else ""
        files = [f for f in request.files.getlist("photos") if f and f.filename][:8]  # photos and videos
        waiting = conn.execute("SELECT COUNT(*) AS c FROM work_posts WHERE submitted_by=? AND status='pending'", (user["id"],)).fetchone()["c"]
        if not title or not files:
            flash("Add a title and at least one photo.", "error")
        elif waiting >= 10:
            flash("You have 10 items waiting for review. Please wait for Andy to review them first.", "error")
        else:
            cur = conn.execute(
                "INSERT INTO work_posts (title, description, category, status, submitted_by) VALUES (?, ?, ?, 'pending', ?)",
                (title, description, category, user["id"]))
            saved = _save_work_media(conn, cur.lastrowid, files)
            if not saved:
                conn.execute("DELETE FROM work_posts WHERE id=?", (cur.lastrowid,))
                conn.commit()
                flash("Please upload JPG, PNG or WEBP photos, or MP4 / MOV / WEBM videos.", "error")
            else:
                conn.commit()
                _notify_work_submitted(user, title)
                flash("Sent to Andy for review. It goes live once approved.", "success")
        conn.close()
        return redirect(url_for("artisan_work"))
    mine = _load_work_posts(conn, "work_posts.submitted_by = ?", (user["id"],))
    conn.close()
    return render_template("artisan_work.html", user=user, mine=mine, categories=WORK_CATEGORIES,
                           active_page="artisan_work", auto_open_auth=False)


def _notify_work_submitted(user, title):
    conn = get_db()
    owners = [r["id"] for r in conn.execute("SELECT id FROM users WHERE role='owner'").fetchall()]
    conn.close()
    send_push_to_users(owners, {"title": "📸 New work to review", "body": f"{user['name']}: {title}"[:140],
                                "url": url_for("admin_works"), "tag": "work-review"})
    send_email_async(NOTIFY_EMAIL, f"📸 {user['name']} submitted work for review",
                     f"{user['name']} uploaded \"{title}\".\n\nReview it: {url_for('admin_works', _external=True)}\n")


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
    if not paystack_configured():
        flash("Online top-up isn't switched on yet. Please contact Andy.", "error")
        return redirect(url_for("wallet"))
    if naira_amount < 100 or naira_amount > 1000000:
        flash("Please choose an amount between ₦100 and ₦1,000,000.", "error")
        return redirect(url_for("wallet"))
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
    reference = request.args.get("reference") or request.args.get("trxref") or ""
    if not re.fullmatch(r"[A-Za-z0-9_.\-]{6,100}", reference):
        flash("No valid payment reference found.", "error")
        return redirect(url_for("wallet"))
    if not paystack_configured():
        flash("Online payments aren't switched on yet.", "error")
        return redirect(url_for("wallet"))

    conn = get_db()
    already = conn.execute("SELECT 1 FROM paystack_refs WHERE reference=?", (reference,)).fetchone() or \
        conn.execute("SELECT 1 FROM transactions WHERE label LIKE ?", (f"%ref:{reference}%",)).fetchone()
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

    if data.get("status") and data["data"].get("status") == "success":
        meta = data["data"].get("metadata") or {}
        if str(meta.get("user_id")) != str(user["id"]):
            conn.close()
            flash("That payment belongs to a different account.", "error")
            return redirect(url_for("wallet"))
        try:  # the reference is the primary key, so a payment can only ever be credited once
            conn.execute("INSERT INTO paystack_refs (reference, user_id) VALUES (?, ?)", (reference, user["id"]))
        except Exception:
            conn.close()
            flash("This payment was already processed.", "success")
            return redirect(url_for("wallet"))
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
            new_name = " ".join(request.form.get("name", "").split())[:60]
            if len(new_name) >= 2 and new_name != user["name"]:
                conn.execute("UPDATE users SET name=? WHERE id=?", (new_name, user["id"]))
            bio = request.form.get("bio", "").strip()[:500]
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
                resp = redirect(url_for("settings"))
                resp.set_cookie("andy_mode", "dark" if dark else "light", max_age=31536000, samesite="Lax")
                return resp
            conn.close()
            return redirect(url_for("settings"))
    return render_template("settings.html", user=user, active_page="settings", auto_open_auth=False)


init_db()

if __name__ == "__main__":
    app.run(debug=FLASK_DEBUG)
