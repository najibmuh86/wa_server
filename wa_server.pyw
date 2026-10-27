# -*- coding: utf-8 -*-
"""
WhatsApp Web Client berbasis WEB (tanpa API resmi, tanpa Google Cloud Console)

Jalankan file ini (klik dua kali wa_server.pyw) di SATU komputer (server).
Client lain cukup membuka  http://IP-SERVER:5000  di browser, login, lalu
kirim / lihat pesan.

- Login client   -> tab USER_CLIENT (via Apps Script Web App, WebApp.gs)
- Inbox/Outbox   -> tab WhatsApp_Database_Client (kolom Client = user yang login)
- Gambar         -> folder wa_images/ (+ opsional upload ke Google Drive)

Install:
    pip install flask playwright requests
    (butuh Google Chrome terpasang)
"""
import base64
import calendar
import csv
import io
import hashlib
import json
import logging
import mimetypes
import os
import re
import secrets
import shutil
import socket
import sys
import threading
import queue
import time
import uuid
from datetime import datetime, timedelta
from functools import wraps

import requests
from werkzeug.utils import secure_filename
from html import escape as esc
from flask import (Flask, Response, abort, jsonify, redirect, render_template_string,
                   request, send_from_directory, session, url_for)
from playwright.sync_api import sync_playwright

# ======================= KONFIGURASI =======================
WEB_APP_URL = ""  # URL Apps Script (.../exec). Diisi lewat prompt saat pertama dijalankan -> disimpan di config.json (tidak diunggah ke GitHub)

# Login server diminta saat program dibuka (username/password dari tab USER_CLIENT).
# Akun itu dipakai untuk mencatat INBOX (kolom Client).

UPLOAD_KE_DRIVE = False      # True = file ikut diupload ke Google Drive (default mati: simpan lokal saja)
POLL_DETIK = 3              # jeda cek pesan masuk
KODE_NEGARA = "62"          # nomor berawalan 0 -> 62
HOST = "0.0.0.0"            # 0.0.0.0 = bisa diakses komputer lain di jaringan
PORT = 5000
HEADLESS = False           # True = Chrome berjalan tersembunyi (tanpa jendela); QR dipindai lewat halaman /qr
# ===========================================================

if getattr(sys, "frozen", False):          # berjalan sebagai .exe (PyInstaller)
    BASE_DIR = os.path.dirname(sys.executable)
else:
    BASE_DIR = os.path.dirname(os.path.abspath(__file__))
PROFILE_DIR = os.path.join(BASE_DIR, "wa_profile")
IMG_DIR = os.path.join(BASE_DIR, "wa_images")
TMP_DIR = os.path.join(BASE_DIR, "wa_tmp")
SEEN_FILE = os.path.join(BASE_DIR, "seen_ids.json")
PENDING_FILE = os.path.join(BASE_DIR, "pending_log.jsonl")
MSG_FILE = os.path.join(BASE_DIR, "messages.jsonl")
KEY_FILE = os.path.join(BASE_DIR, "secret.key")
LAST_USER_FILE = os.path.join(BASE_DIR, "last_user.txt")
for d in (IMG_DIR, TMP_DIR):
    os.makedirs(d, exist_ok=True)

# Mode .pyw (pythonw) tidak punya konsol: arahkan output ke server.log
if sys.stdout is None or sys.stderr is None:
    _lf = open(os.path.join(BASE_DIR, "server.log"), "a", encoding="utf-8", buffering=1)
    sys.stdout = sys.stdout or _lf
    sys.stderr = sys.stderr or _lf
logging.getLogger("werkzeug").setLevel(logging.ERROR)

CONFIG_FILE = os.path.join(BASE_DIR, "config.json")


def muat_config():
    """Timpa pengaturan di atas dengan isi config.json (bila ada)."""
    try:
        with open(CONFIG_FILE, "r", encoding="utf-8") as f:
            cfg = json.load(f)
    except Exception:
        return
    for k in ("WEB_APP_URL", "PORT", "KODE_NEGARA", "UPLOAD_KE_DRIVE", "POLL_DETIK", "HEADLESS"):
        if k in cfg:
            globals()[k] = cfg[k]


def simpan_config(**kv):
    try:
        with open(CONFIG_FILE, "r", encoding="utf-8") as f:
            cfg = json.load(f)
    except Exception:
        cfg = {}
    cfg.update(kv)
    with open(CONFIG_FILE, "w", encoding="utf-8") as f:
        json.dump(cfg, f, indent=2, ensure_ascii=False)


muat_config()

WA_URL = "https://web.whatsapp.com"
ROW_SEL = '#pane-side [role="listitem"], #pane-side [role="row"]'
IMG_EXT = {".jpg", ".jpeg", ".png", ".webp", ".gif"}
DOC_EXT = {".pdf", ".doc", ".docx", ".xls", ".xlsx", ".ppt", ".pptx", ".txt", ".csv",
           ".zip", ".rar", ".7z"}
FILE_EXT = IMG_EXT | DOC_EXT
MAX_UPLOAD_MB = 20
OWN_FILE = os.path.join(BASE_DIR, "owners.json")
ALIAS_FILE = os.path.join(BASE_DIR, "aliases.json")
AUTO_FILE = os.path.join(BASE_DIR, "auto_rules.json")
AUTO_STATE_FILE = os.path.join(BASE_DIR, "auto_state.json")
AUTO_DIR = os.path.join(BASE_DIR, "wa_auto")
JADWAL_FILE = os.path.join(BASE_DIR, "jadwal.json")
JADWAL_DIR = os.path.join(BASE_DIR, "wa_jadwal")
TEMA_FILE = os.path.join(BASE_DIR, "tema.json")
TEMA_DIR = os.path.join(BASE_DIR, "wa_tema")
MAX_AUTO_PER_JAM = 5
QR_FILE = os.path.join(BASE_DIR, "wa_qr.png")


# ----------------------- Apps Script API -----------------------
def api(payload):
    r = requests.post(
        WEB_APP_URL,
        data=json.dumps(payload),
        headers={"Content-Type": "text/plain;charset=utf-8"},
        timeout=90,
    )
    return r.json()


class Session:
    def __init__(self, username, password, token=None, admin=False):
        self.username, self.password, self.token, self.admin = username, password, token, admin

    def _login(self):
        r = api({"action": "login", "username": self.username, "password": self.password})
        if r.get("ok"):
            self.token = r["token"]
            self.admin = bool(r.get("admin"))
        return r

    def call(self, payload):
        if not self.token:
            r = self._login()
            if not r.get("ok"):
                return r
        res = api(dict(payload, token=self.token))
        if not res.get("ok") and res.get("code") == "TOKEN":
            if self._login().get("ok"):
                res = api(dict(payload, token=self.token))
        return res


SERVER_SESSION = Session("", "")  # diisi saat login server
SESSIONS = {}  # username -> Session (milik user web yang sedang login)


# ----------------------- Penyimpanan pesan untuk tampilan web -----------------------
class Store:
    def __init__(self):
        self.lock = threading.Lock()
        self.items = []
        self.next_id = 1
        self.file_chat = {}   # nama file tersimpan -> kunci chat (untuk cek hak akses)
        self.file_orig = {}   # nama file tersimpan -> nama asli
        self.chats = set()
        try:
            with open(MSG_FILE, "r", encoding="utf-8") as f:
                rows = [json.loads(x) for x in f if x.strip()]
            for r in rows:
                self._index(r)
            self.items = rows[-500:]
            if rows:
                self.next_id = max(r["id"] for r in rows) + 1
        except Exception:
            pass

    def _index(self, e):
        if e.get("type") == "SYS":
            return
        chat = e.get("chat") or e.get("who") or ""
        self.chats.add(chat)
        for n in e.get("images", []):
            self.file_chat[n] = chat
            self.file_orig[n] = n
        for fl in e.get("files", []):
            self.file_chat[fl["n"]] = chat
            self.file_orig[fl["n"]] = fl.get("o") or fl["n"]

    def add(self, **kw):
        with self.lock:
            e = {"id": self.next_id, "time": datetime.now().strftime("%Y-%m-%d %H:%M:%S"), **kw}
            self.next_id += 1
            self.items.append(e)
            self.items = self.items[-1000:]
            self._index(e)
            try:
                with open(MSG_FILE, "a", encoding="utf-8") as f:
                    f.write(json.dumps(e, ensure_ascii=False) + "\n")
            except Exception:
                pass
        return e

    def after(self, i):
        with self.lock:
            return [e for e in self.items if e["id"] > i]

    def has_chat(self, chat):
        with self.lock:
            return chat in self.chats


STORE = Store()


# ----------------------- Hak akses: pemilik chat -----------------------
class Owners:
    """chat -> username pemilik. Admin melihat semua; user biasa hanya chat miliknya."""
    def __init__(self):
        self.lock = threading.Lock()
        try:
            with open(OWN_FILE, "r", encoding="utf-8") as f:
                self.d = json.load(f)
        except Exception:
            self.d = {}

    def get(self, chat):
        return self.d.get(chat)

    def set(self, chat, user):
        with self.lock:
            if user:
                self.d[chat] = user
            else:
                self.d.pop(chat, None)
            try:
                with open(OWN_FILE, "w", encoding="utf-8") as f:
                    json.dump(self.d, f, ensure_ascii=False, indent=1)
            except Exception:
                pass

    def all(self):
        return dict(self.d)


OWN = Owners()
EPOCH = {}  # username -> penghitung; berubah bila daftar chat yang boleh dilihat user berubah


def bump(user):
    if user:
        EPOCH[user] = EPOCH.get(user, 0) + 1


try:
    with open(ALIAS_FILE, "r", encoding="utf-8") as _f:
        ALIAS = json.load(_f)  # nama kontak -> nomor (supaya chat satu kunci)
except Exception:
    ALIAS = {}


GRUP_FILE = os.path.join(BASE_DIR, "grup.json")
try:
    with open(GRUP_FILE, "r", encoding="utf-8") as _f:
        GRUP_KNOWN = set(json.load(_f))  # judul chat yang sudah pasti grup
except Exception:
    GRUP_KNOWN = set()


def grup_catat(judul):
    if judul and judul not in GRUP_KNOWN:
        GRUP_KNOWN.add(judul)
        try:
            with open(GRUP_FILE, "w", encoding="utf-8") as f:
                json.dump(sorted(GRUP_KNOWN), f, ensure_ascii=False, indent=1)
        except Exception:
            pass


FORMAT_TANGGAL = "DMY"  # urutan tanggal di header WhatsApp: "DMY" (hari/bulan/tahun) atau "MDY" (bulan/hari/tahun)
_RE_WAKTU = re.compile(r"\s*\[\s*(\d{1,2})[:.](\d{2})(?::\d{2})?(?:\s*([AaPp])\.?[Mm]\.?)?\s*,\s*"
                       r"(\d{1,4})\s*[/.\-]\s*(\d{1,2})\s*[/.\-]\s*(\d{1,4})")


def waktu_pesan(pre, sekarang):
    """Jam pesan yang sebenarnya, dari header WhatsApp ('[10:30, 12/05/2024] Nama: ').
    Return 'YYYY-MM-DD HH:MM:SS', atau None bila tidak terbaca (dipakai waktu saat diterima)."""
    m = _RE_WAKTU.match(pre or "")
    if not m:
        return None
    jam, mnt, ap, a_s, b_s, c_s = m.groups()
    jam, mnt, a, b, c = int(jam), int(mnt), int(a_s), int(b_s), int(c_s)
    if ap:
        jam = jam % 12 + (12 if ap.lower() == "p" else 0)
    if len(a_s) == 4:                       # 2024-05-12
        urutan = [(a, b, c)]
    else:
        th = c + 2000 if c < 100 else c
        if a > 12:
            urutan = [(th, b, a)]
        elif b > 12:
            urutan = [(th, a, b)]
        elif FORMAT_TANGGAL == "MDY":
            urutan = [(th, a, b), (th, b, a)]
        else:
            urutan = [(th, b, a), (th, a, b)]
    for th, bl, tg in urutan:               # pilihan kedua dipakai bila pilihan pertama tidak masuk akal
        try:
            dt = datetime(th, bl, tg, jam, mnt)
        except ValueError:
            continue
        if dt > sekarang + timedelta(minutes=10):
            continue
        if dt.strftime("%Y%m%d%H%M") == sekarang.strftime("%Y%m%d%H%M"):
            dt = sekarang.replace(microsecond=0)   # menit yang sama: pakai detik sebenarnya
        return dt.strftime("%Y-%m-%d %H:%M:%S")
    return None


PESERTA_FILE = os.path.join(BASE_DIR, "peserta.json")
try:
    with open(PESERTA_FILE, "r", encoding="utf-8") as _f:
        PESERTA = json.load(_f)  # id peserta grup (mis. 628xx@c.us) -> nama yang tampil di WhatsApp
except Exception:
    PESERTA = {}
_RE_PESERTA = re.compile(r"^(?:true|false)_[^@_]+@g\.us_[^_]+_(\d+)(?::\d+)?@(c\.us|lid|s\.whatsapp\.net)$")


def peserta_id(msg_id):
    """Ambil id pengirim dari data-id pesan grup, mis. false_<grup>@g.us_<idpesan>_628123@c.us."""
    m = _RE_PESERTA.match(msg_id or "")
    return f"{m.group(1)}@{m.group(2)}" if m else ""


def peserta_nama(pid, nama_dari_pre):
    """Nama pengirim di grup. Nama dari header pesan dipelajari dan diingat, sehingga pesan
    gambar/stiker (yang tidak membawa nama) dari orang yang sama tetap bisa diberi nama."""
    nama = (nama_dari_pre or "").strip()
    if nama:
        if pid and PESERTA.get(pid) != nama:
            PESERTA[pid] = nama
            try:
                with open(PESERTA_FILE, "w", encoding="utf-8") as f:
                    json.dump(PESERTA, f, ensure_ascii=False, indent=1)
            except Exception:
                pass
        return nama
    if not pid:
        return ""
    if PESERTA.get(pid):
        return PESERTA[pid]
    if pid.endswith(("@c.us", "@s.whatsapp.net")):  # id berupa nomor telepon asli
        no = pid.split("@")[0]
        for nm, n in ALIAS.items():
            if n == no:
                return nm
        return _fmt_no(no)
    return ""


def alias_set(name, number):
    if not name or not number or re.fullmatch(r"[+\d\s-]+", name) or ALIAS.get(name) == number:
        return
    ALIAS[name] = number
    try:
        with open(ALIAS_FILE, "w", encoding="utf-8") as f:
            json.dump(ALIAS, f, ensure_ascii=False, indent=1)
    except Exception:
        pass


class AutoReply:
    """Aturan balasan otomatis (teks / gambar / file), disimpan di auto_rules.json.
    Aturan dicek berurutan; aturan pertama yang cocok yang dipakai."""

    def __init__(self):
        self.lock = threading.Lock()
        self.data = {"aktif": False, "rules": []}
        self.state = {}   # "chat|id_aturan" -> waktu balas terakhir (epoch)
        self.hist = {}    # chat -> daftar waktu balas (pembatas per jam)
        os.makedirs(AUTO_DIR, exist_ok=True)
        try:
            with open(AUTO_FILE, "r", encoding="utf-8") as f:
                d = json.load(f)
            if isinstance(d, dict) and isinstance(d.get("rules"), list):
                self.data = d
        except Exception:
            pass
        try:
            with open(AUTO_STATE_FILE, "r", encoding="utf-8") as f:
                self.state = json.load(f)
        except Exception:
            pass

    def _simpan(self):
        try:
            with open(AUTO_FILE, "w", encoding="utf-8") as f:
                json.dump(self.data, f, ensure_ascii=False, indent=1)
        except Exception:
            pass

    def snapshot(self):
        with self.lock:
            return json.loads(json.dumps(self.data))

    def get(self, rid):
        with self.lock:
            for r in self.data["rules"]:
                if r["id"] == rid:
                    return json.loads(json.dumps(r))
        return None

    def set_aktif(self, v):
        with self.lock:
            self.data["aktif"] = bool(v)
            self._simpan()

    def simpan(self, rule):
        with self.lock:
            for i, r in enumerate(self.data["rules"]):
                if r["id"] == rule["id"]:
                    self.data["rules"][i] = rule
                    break
            else:
                self.data["rules"].append(rule)
            self._simpan()

    def toggle(self, rid, aktif):
        with self.lock:
            for r in self.data["rules"]:
                if r["id"] == rid:
                    r["aktif"] = bool(aktif)
                    self._simpan()
                    return True
        return False

    def hapus(self, rid):
        with self.lock:
            sisa = [r for r in self.data["rules"] if r["id"] != rid]
            lama = [r for r in self.data["rules"] if r["id"] == rid]
            self.data["rules"] = sisa
            self._simpan()
        for r in lama:
            self.hapus_berkas(r.get("lampiran"))
        return bool(lama)

    def geser(self, rid, arah):
        with self.lock:
            rs = self.data["rules"]
            for i, r in enumerate(rs):
                if r["id"] == rid:
                    j = i + (-1 if arah < 0 else 1)
                    if 0 <= j < len(rs):
                        rs[i], rs[j] = rs[j], rs[i]
                        self._simpan()
                    return True
        return False

    @staticmethod
    def hapus_berkas(lamp, folder=None):
        if lamp and lamp.get("n"):
            try:
                os.remove(os.path.join(folder or AUTO_DIR, os.path.basename(lamp["n"])))
            except OSError:
                pass

    @staticmethod
    def cocok(r, teks, pertama, now):
        p = r.get("pemicu", "kata_kunci")
        if p == "pertama":
            if not pertama:
                return False
        elif p == "kata_kunci":
            kata = [k.strip().lower() for k in re.split(r"[,\n]", r.get("kata", "")) if k.strip()]
            if not kata or not any(k in (teks or "").lower() for k in kata):
                return False
        mode = r.get("jadwal", "selalu")
        if mode in ("dalam", "luar"):
            hari = r.get("hari") or []
            dalam_hari = (not hari) or now.weekday() in hari
            mulai, selesai = r.get("mulai", "08:00"), r.get("selesai", "16:00")
            hm = now.strftime("%H:%M")
            dalam_jam = (mulai <= hm < selesai) if mulai <= selesai else (hm >= mulai or hm < selesai)
            aktif_waktu = dalam_hari and dalam_jam
            if (mode == "dalam" and not aktif_waktu) or (mode == "luar" and aktif_waktu):
                return False
        return True

    def pilih(self, chat, teks, pertama, now=None):
        """Kembalikan aturan yang harus dibalas, atau None."""
        now = now or datetime.now()
        with self.lock:
            if not self.data.get("aktif"):
                return None
            for r in self.data["rules"]:
                if not r.get("aktif", True) or not self.cocok(r, teks, pertama, now):
                    continue
                ts = time.time()  # aturan pertama yang cocok menang
                if ts - self.state.get(f"{chat}|{r['id']}", 0) < int(r.get("cooldown_menit", 60)) * 60:
                    return None
                self.hist[chat] = [t for t in self.hist.get(chat, []) if ts - t < 3600]
                if len(self.hist[chat]) >= MAX_AUTO_PER_JAM:
                    return None
                return json.loads(json.dumps(r))
        return None

    def catat(self, chat, r):
        with self.lock:
            ts = time.time()
            self.state[f"{chat}|{r['id']}"] = ts
            self.hist.setdefault(chat, []).append(ts)
            for k in [k for k, v in self.state.items() if ts - v > 7 * 86400]:
                del self.state[k]
            try:
                with open(AUTO_STATE_FILE, "w", encoding="utf-8") as f:
                    json.dump(self.state, f)
            except Exception:
                pass

    @staticmethod
    def render(teks, nama, nomor, now):
        return (teks or "").replace("{nama}", nama or "").replace("{nomor}", _fmt_no(nomor or "")) \
            .replace("{jam}", now.strftime("%H:%M")).replace("{tanggal}", now.strftime("%d/%m/%Y"))


AUTO = AutoReply()


class Jadwal:
    """Pesan terjadwal (tanggal + jam, boleh berulang). Disimpan di jadwal.json."""
    TELAT_MAKS_MENIT = 60   # lewat dari ini saat server mati -> dilewati, tidak dikirim terlambat

    def __init__(self):
        self.lock = threading.Lock()
        self.items = []
        os.makedirs(JADWAL_DIR, exist_ok=True)
        try:
            with open(JADWAL_FILE, "r", encoding="utf-8") as f:
                d = json.load(f)
            if isinstance(d, list):
                self.items = d
        except Exception:
            pass
        for it in self.items:
            if it.get("status") == "diproses":  # server berhenti saat sedang mengirim
                it["status"], it["hasil"] = "gagal", "Terputus saat mengirim (server berhenti)"
        self._bersihkan()
        self._simpan()

    def _simpan(self):
        try:
            with open(JADWAL_FILE, "w", encoding="utf-8") as f:
                json.dump(self.items, f, ensure_ascii=False, indent=1)
        except Exception:
            pass

    def _bersihkan(self):
        batas = (datetime.now() - timedelta(days=30)).strftime("%Y-%m-%d")
        sisa = []
        for it in self.items:
            if it.get("status") in ("terkirim", "gagal", "terlewat", "selesai") and \
                    (it.get("terakhir") or "9999")[:10] < batas:
                AutoReply.hapus_berkas(it.get("lampiran"), JADWAL_DIR)
            else:
                sisa.append(it)
        self.items = sisa

    def snapshot(self, user, admin):
        with self.lock:
            hasil = [json.loads(json.dumps(i)) for i in self.items if admin or i.get("user") == user]
        return sorted(hasil, key=lambda i: i.get("waktu", ""))

    def hitung_aktif(self, user):
        with self.lock:
            return len([i for i in self.items if i.get("user") == user and i.get("status") == "menunggu"])

    def tambah(self, item):
        with self.lock:
            self.items.append(item)
            self._simpan()

    def batal(self, rid, user, admin):
        """Hapus jadwal. Return (ok, pesan_error)."""
        with self.lock:
            for it in self.items:
                if it["id"] == rid:
                    if not admin and it.get("user") != user:
                        return False, "Bukan jadwal Anda"
                    if it.get("status") == "diproses":
                        return False, "Sedang dikirim, coba lagi sebentar"
                    self.items.remove(it)
                    AutoReply.hapus_berkas(it.get("lampiran"), JADWAL_DIR)
                    self._simpan()
                    return True, ""
        return False, "Jadwal tidak ditemukan"

    @staticmethod
    def _berikut(w, ulang):
        if ulang == "harian":
            return w + timedelta(days=1)
        if ulang == "mingguan":
            return w + timedelta(days=7)
        y, m = w.year + (w.month // 12), w.month % 12 + 1
        return w.replace(year=y, month=m, day=min(w.day, calendar.monthrange(y, m)[1]))

    def _lanjut(self, it, now, ok, ket):
        it["hasil"] = ket
        it["terakhir"] = now.strftime("%Y-%m-%d %H:%M")
        if it.get("ulang", "sekali") == "sekali":
            it["status"] = "terlewat" if ok is None else ("terkirim" if ok else "gagal")
            return
        w = datetime.strptime(it["waktu"], "%Y-%m-%d %H:%M")
        for _ in range(2000):
            w = self._berikut(w, it["ulang"])
            if w > now:
                break
        if it.get("sampai") and w.strftime("%Y-%m-%d") > it["sampai"]:
            it["status"] = "selesai"
        else:
            it["waktu"], it["status"] = w.strftime("%Y-%m-%d %H:%M"), "menunggu"

    def jatuh_tempo(self, now):
        """Jadwal yang waktunya tiba -> ditandai 'diproses' dan dikembalikan untuk dikirim."""
        due = []
        with self.lock:
            for it in self.items:
                if it.get("status") != "menunggu":
                    continue
                w = datetime.strptime(it["waktu"], "%Y-%m-%d %H:%M")
                if w > now:
                    continue
                if (now - w).total_seconds() / 60 > self.TELAT_MAKS_MENIT:
                    self._lanjut(it, now, None, f"Terlewat: server tidak aktif pada {it['waktu']}")
                    continue
                it["status"] = "diproses"
                due.append(json.loads(json.dumps(it)))
            if due or any(i.get("status") == "terlewat" for i in self.items):
                self._simpan()
        return due

    def hasil(self, rid, ok, err=""):
        with self.lock:
            for it in self.items:
                if it["id"] == rid:
                    self._lanjut(it, datetime.now(), ok, "Terkirim" if ok else f"Gagal: {err}")
                    self._simpan()
                    return


JADWAL = Jadwal()


TEMA_FONT = {
    "sistem": 'system-ui,-apple-system,"Segoe UI",Roboto,Arial,sans-serif',
    "segoe": '"Segoe UI","Helvetica Neue",Arial,sans-serif',
    "arial": 'Arial,Helvetica,sans-serif',
    "tahoma": 'Tahoma,Verdana,sans-serif',
    "verdana": 'Verdana,Geneva,sans-serif',
    "georgia": 'Georgia,"Times New Roman",serif',
}
TEMA_UKURAN = {"kecil": 0.92, "normal": 1.0, "besar": 1.12}
TEMA_DASAR = {  # warna dasar mode terang / gelap
    "terang": {"surface": "#ffffff", "panel": "#f0f2f5", "page-bg": "#d1d7db", "text": "#111b21",
               "muted": "#667781", "border": "#e4e8eb", "hover": "#f5f6f6"},
    "gelap": {"surface": "#111b21", "panel": "#202c33", "page-bg": "#0b141a", "text": "#e9edef",
              "muted": "#8696a0", "border": "#2a3942", "hover": "#1a262d"},
}
TEMA_PRESET = {
    "hijau": {"nama": "Hijau WhatsApp", "brand": "#00a884", "brand_dark": "#128c7e", "aksen": "#25d366",
              "out_bg": "#d9fdd3", "in_bg": "#ffffff", "chat_bg": "#efeae2", "gelap": False},
    "biru": {"nama": "Biru Profesional", "brand": "#2563eb", "brand_dark": "#1e3a8a", "aksen": "#0ea5e9",
             "out_bg": "#dbeafe", "in_bg": "#ffffff", "chat_bg": "#eaf0fa", "gelap": False},
    "ungu": {"nama": "Ungu Elegan", "brand": "#7c3aed", "brand_dark": "#4c1d95", "aksen": "#a855f7",
             "out_bg": "#ede9fe", "in_bg": "#ffffff", "chat_bg": "#f1eefa", "gelap": False},
    "marun": {"nama": "Marun Resmi", "brand": "#be123c", "brand_dark": "#7f1d1d", "aksen": "#f43f5e",
              "out_bg": "#ffe4e6", "in_bg": "#ffffff", "chat_bg": "#f8eeee", "gelap": False},
    "teal": {"nama": "Teal Modern", "brand": "#0f766e", "brand_dark": "#134e4a", "aksen": "#14b8a6",
             "out_bg": "#ccfbf1", "in_bg": "#ffffff", "chat_bg": "#e9f3f2", "gelap": False},
    "abu": {"nama": "Abu Netral", "brand": "#475569", "brand_dark": "#1e293b", "aksen": "#64748b",
            "out_bg": "#e2e8f0", "in_bg": "#ffffff", "chat_bg": "#eef1f5", "gelap": False},
    "gelap": {"nama": "Mode Gelap", "brand": "#00a884", "brand_dark": "#0b3d36", "aksen": "#25d366",
              "out_bg": "#005c4b", "in_bg": "#202c33", "chat_bg": "#0b141a", "gelap": True},
}
TEMA_DEFAULT = {"nama": "WhatsApp Client", "tagline": "Layanan pesan terpadu untuk tim Anda",
                "preset": "hijau", "font": "sistem", "ukuran": "normal", "radius": 8, "wall_vis": 60,
                "logo": "", "login_bg": "", "wallpaper": "", "ver": 1,
                **{k: v for k, v in TEMA_PRESET["hijau"].items() if k != "nama"}}
TEMA_BATAS_MB = {"logo": 2, "login_bg": 5, "wallpaper": 5}


def _hex_rgb(h):
    return int(h[1:3], 16), int(h[3:5], 16), int(h[5:7], 16)


def _lum(h):
    def c(v):
        v /= 255
        return v / 12.92 if v <= 0.03928 else ((v + 0.055) / 1.055) ** 2.4
    r, g, b = _hex_rgb(h)
    return 0.2126 * c(r) + 0.7152 * c(g) + 0.0722 * c(b)


def _teks_di_atas(h):
    """Warna teks (putih/gelap) yang terbaca di atas warna h."""
    return "#ffffff" if _lum(h) < 0.4 else "#111b21"


def _jenis_gambar(data):
    if data[:8] == b"\x89PNG\r\n\x1a\n":
        return ".png"
    if data[:3] == b"\xff\xd8\xff":
        return ".jpg"
    if data[:4] == b"GIF8":
        return ".gif"
    if data[:4] == b"RIFF" and data[8:12] == b"WEBP":
        return ".webp"
    return ""


class Tema:
    """Tema & identitas tampilan (warna, font, logo, gambar). Disimpan di tema.json + folder wa_tema."""

    def __init__(self):
        self.lock = threading.Lock()
        self.data = json.loads(json.dumps(TEMA_DEFAULT))
        os.makedirs(TEMA_DIR, exist_ok=True)
        try:
            with open(TEMA_FILE, "r", encoding="utf-8") as f:
                d = json.load(f)
            if isinstance(d, dict):
                self.data.update({k: v for k, v in d.items() if k in TEMA_DEFAULT})
        except Exception:
            pass

    def _simpan(self):
        self.data["ver"] = int(time.time())
        try:
            with open(TEMA_FILE, "w", encoding="utf-8") as f:
                json.dump(self.data, f, ensure_ascii=False, indent=1)
        except Exception:
            pass

    def get(self):
        with self.lock:
            return json.loads(json.dumps(self.data))

    def publik(self):
        t = self.get()
        return {"nama": t["nama"], "tagline": t["tagline"], "ver": t["ver"],
                "logo_url": ("/tema/" + t["logo"]) if t["logo"] else ""}

    def nama_berkas(self):
        with self.lock:
            return {self.data[k] for k in ("logo", "login_bg", "wallpaper") if self.data.get(k)}

    def _hapus_berkas(self, nama):
        if nama:
            try:
                os.remove(os.path.join(TEMA_DIR, os.path.basename(nama)))
            except OSError:
                pass

    def perbarui(self, d, hapus, gambar):
        """d: isian teks/warna; hapus: daftar jenis gambar yang dihapus; gambar: {jenis: bytes}.
        Raise ValueError bila tidak valid."""
        baru = {}
        baru["nama"] = str(d.get("nama", "")).strip()[:60]
        if not baru["nama"]:
            raise ValueError("Nama aplikasi wajib diisi")
        baru["tagline"] = str(d.get("tagline", "")).strip()[:120]
        for k in ("brand", "brand_dark", "aksen", "out_bg", "in_bg", "chat_bg"):
            v = str(d.get(k, ""))
            if not re.fullmatch(r"#[0-9a-fA-F]{6}", v):
                raise ValueError(f"Warna '{k}' tidak valid (format #RRGGBB)")
            baru[k] = v.lower()
        baru["gelap"] = bool(d.get("gelap"))
        if d.get("font") not in TEMA_FONT:
            raise ValueError("Font tidak dikenal")
        baru["font"] = d["font"]
        if d.get("ukuran") not in TEMA_UKURAN:
            raise ValueError("Ukuran teks tidak valid")
        baru["ukuran"] = d["ukuran"]
        try:
            baru["radius"] = max(0, min(20, int(d.get("radius", 8))))
            baru["wall_vis"] = max(0, min(100, int(d.get("wall_vis", 60))))
        except (TypeError, ValueError):
            raise ValueError("Angka tidak valid")
        baru["preset"] = d.get("preset") if d.get("preset") in TEMA_PRESET else "kustom"

        tersimpan, lama = {}, []
        with self.lock:
            for jenis in ("logo", "login_bg", "wallpaper"):
                if jenis in gambar:
                    data = gambar[jenis]
                    if len(data) > TEMA_BATAS_MB[jenis] * 1024 * 1024:
                        raise ValueError(f"Gambar {jenis} maksimal {TEMA_BATAS_MB[jenis]} MB")
                    ext = _jenis_gambar(data)
                    if not ext:
                        raise ValueError("Berkas bukan gambar PNG / JPG / WEBP / GIF yang valid")
                    nama = f"{jenis}_{int(time.time())}_{secrets.token_hex(3)}{ext}"
                    with open(os.path.join(TEMA_DIR, nama), "wb") as f:
                        f.write(data)
                    tersimpan[jenis] = nama
            for jenis in ("logo", "login_bg", "wallpaper"):
                if jenis in tersimpan:
                    lama.append(self.data.get(jenis))
                    baru[jenis] = tersimpan[jenis]
                elif jenis in hapus:
                    lama.append(self.data.get(jenis))
                    baru[jenis] = ""
            self.data.update(baru)
            self._simpan()
        for n in lama:
            self._hapus_berkas(n)

    def reset(self):
        with self.lock:
            lama = [self.data.get(k) for k in ("logo", "login_bg", "wallpaper")]
            self.data = json.loads(json.dumps(TEMA_DEFAULT))
            self._simpan()
        for n in lama:
            self._hapus_berkas(n)

    def css(self):
        t = self.get()
        v = dict(TEMA_DASAR["gelap" if t["gelap"] else "terang"])
        v.update({"brand": t["brand"], "brand-dark": t["brand_dark"], "accent": t["aksen"],
                  "out-bg": t["out_bg"], "in-bg": t["in_bg"], "chat-bg": t["chat_bg"],
                  "on-brand": _teks_di_atas(t["brand"]), "on-header": _teks_di_atas(t["brand_dark"]),
                  "radius": f"{t['radius']}px", "font": TEMA_FONT[t["font"]], "fsm": TEMA_UKURAN[t["ukuran"]]})
        out = [":root{" + ";".join(f"--{k}:{val}" for k, val in v.items()) + "}"]
        if t["wallpaper"]:
            r, g, b = _hex_rgb(t["chat_bg"])
            a = round(1 - t["wall_vis"] / 100, 2)
            out.append(f"#main{{background-image:linear-gradient(rgba({r},{g},{b},{a}),rgba({r},{g},{b},{a})),"
                       f"url(/tema/{t['wallpaper']});background-size:cover;background-position:center}}")
        if t["login_bg"]:
            r, g, b = _hex_rgb(t["brand_dark"])
            r2, g2, b2 = _hex_rgb(t["brand"])
            out.append(f".lg-art{{background-image:linear-gradient(135deg,rgba({r},{g},{b},.78),rgba({r2},{g2},{b2},.45)),"
                       f"url(/tema/{t['login_bg']});background-size:cover;background-position:center}}")
        return "\n".join(out)


TEMA = Tema()


IZIN = {
    "lihat_semua": "Melihat semua chat (bukan hanya chat miliknya)",
    "kirim": "Mengirim pesan & lampiran",
    "jadwal": "Pesan terjadwal",
    "lempar": "Melempar chat ke user lain",
    "tetapkan": "Menetapkan / memindahkan pemilik chat",
    "rekap": "Rekap, laporan, CSV & transkrip",
    "auto": "Mengatur balasan otomatis",
    "tema": "Mengubah tampilan aplikasi",
    "wa": "Scan QR / koneksi WhatsApp",
    "peran": "Mengelola peran & izin user",
}
PERAN_FILE = os.path.join(BASE_DIR, "roles.json")
PERAN_DEFAULT = {
    "admin": {"nama": "Admin", "izin": list(IZIN)},
    "operator": {"nama": "Operator", "izin": ["kirim", "jadwal", "lempar"]},
    "supervisor": {"nama": "Supervisor", "izin": ["lihat_semua", "kirim", "jadwal", "lempar", "tetapkan", "rekap"]},
    "pengamat": {"nama": "Pengamat", "izin": ["lihat_semua", "rekap"]},
}
PERAN_TETAP = ("admin", "operator")  # tidak bisa dihapus; admin juga tidak bisa diubah izinnya


class Peran:
    """Peran (role) user. Admin dari Apps Script selalu 'admin'. User lain memakai peran yang
    ditetapkan di sini; yang belum ditetapkan otomatis 'operator' (sama seperti perilaku lama)."""

    def __init__(self):
        self.lock = threading.RLock()
        self.peran = json.loads(json.dumps(PERAN_DEFAULT))
        self.user = {}
        try:
            with open(PERAN_FILE, "r", encoding="utf-8") as f:
                d = json.load(f)
            for k, v in (d.get("peran") or {}).items():
                if k not in PERAN_TETAP[:1]:
                    self.peran[k] = {"nama": str(v.get("nama", k))[:30],
                                     "izin": [i for i in v.get("izin", []) if i in IZIN]}
            self.user = {u: r for u, r in (d.get("user") or {}).items() if r in self.peran}
        except Exception:
            pass

    def _simpan(self):
        try:
            with open(PERAN_FILE, "w", encoding="utf-8") as f:
                json.dump({"peran": self.peran, "user": self.user}, f, ensure_ascii=False, indent=1)
        except Exception:
            pass

    def peran_user(self, user):
        sess = SESSIONS.get(user)
        if sess and sess.admin:
            return "admin"
        with self.lock:
            r = self.user.get(user, "operator")
            return r if r in self.peran else "operator"

    def nama_peran(self, user):
        pid = self.peran_user(user)
        with self.lock:
            return self.peran.get(pid, {}).get("nama", "")

    def izin_user(self, user):
        pid = self.peran_user(user)
        with self.lock:
            return set(self.peran.get(pid, {}).get("izin", []))

    def punya(self, user, izin):
        return izin in self.izin_user(user)

    def snapshot(self):
        with self.lock:
            return json.loads(json.dumps({"peran": self.peran, "user": self.user}))

    def simpan_peran(self, pid, nama, izin):
        with self.lock:
            if pid == "admin":
                return False, "Peran admin tidak bisa diubah"
            self.peran[pid] = {"nama": nama, "izin": [i for i in izin if i in IZIN]}
            self._simpan()
        return True, ""

    def hapus_peran(self, pid):
        with self.lock:
            if pid in PERAN_TETAP or pid not in self.peran:
                return False, "Peran ini tidak bisa dihapus"
            del self.peran[pid]
            self.user = {u: r for u, r in self.user.items() if r != pid}
            self._simpan()
        return True, ""

    def set_user(self, user, pid):
        with self.lock:
            if pid not in self.peran:
                return False
            if pid == "operator":
                self.user.pop(user, None)
            else:
                self.user[user] = pid
            self._simpan()
        return True

    def user_dengan(self, pid):
        with self.lock:
            return [u for u, r in self.user.items() if r == pid]


PERAN = Peran()


def is_admin(user):
    sess = SESSIONS.get(user)
    return bool(sess and sess.admin)


def punya(user, izin):
    return PERAN.punya(user, izin)


def can_see(user, chat):
    return punya(user, "lihat_semua") or OWN.get(chat) == user


def visible_items(user, items):
    if punya(user, "lihat_semua"):
        return items
    out = []
    for e in items:
        if e.get("type") == "SYS":
            if e.get("user") == user:
                out.append(e)
        elif OWN.get(e.get("chat") or e.get("who") or "") == user:
            out.append(e)
    return out


_USERS = {"t": 0, "v": []}


def users_list(sess):
    if _USERS["v"] and time.time() - _USERS["t"] < 300:
        return _USERS["v"]
    res = sess.call({"action": "users"})
    if not res.get("ok"):
        raise RuntimeError(res.get("error", "gagal memuat user"))
    _USERS["t"], _USERS["v"] = time.time(), res["users"]
    return res["users"]


# ----------------------- JavaScript di halaman WA -----------------------
JS_UNREAD = """
() => {
  const out = [];
  const rows = document.querySelectorAll('#pane-side [role="listitem"], #pane-side [role="row"]');
  rows.forEach((row, idx) => {
    let n = 0;
    const badge = [...row.querySelectorAll('[aria-label]')]
      .find(s => /unread|belum dibaca|belum terbaca/i.test(s.getAttribute('aria-label')));
    if (badge) n = parseInt(badge.textContent) || parseInt(badge.getAttribute('aria-label')) || 1;
    if (!n) {
      const leaf = [...row.querySelectorAll('span')].find(s =>
        s.children.length === 0 && /^\\d{1,4}$/.test(s.textContent.trim()) && !s.closest('span[title]'));
      if (leaf) n = parseInt(leaf.textContent.trim());
    }
    if (n) {
      const t = row.querySelector('span[title]');
      out.push({ idx, title: t ? t.getAttribute('title') : '?', n });
    }
  });
  return out;
}
"""

JS_HEADER = """
() => {
  const hd = document.querySelector('#main header');
  if (!hd) return '';
  const bad = /info kontak|contact info|click here|klik di sini/i;
  for (const c of hd.querySelectorAll('span[dir="auto"], span[title]')) {
    const ttl = c.getAttribute('title') || '';
    if (bad.test(ttl)) continue;
    const t = (c.textContent || ttl).trim();
    if (t && !bad.test(t)) return t;
  }
  return '';
}
"""

JS_KLIK_BARIS = """
(judul) => {
  const rows = [...document.querySelectorAll('#pane-side [role="listitem"], #pane-side [role="row"]')];
  const r = rows.find(x => { const t = x.querySelector('span[title]'); return t && t.title === judul; });
  if (!r) return false;
  r.scrollIntoView({ block: 'nearest' });
  const tgt = r.querySelector('[role="gridcell"]') || r.querySelector('span[title]') || r;
  for (const t of ['mousedown', 'mouseup', 'click'])
    tgt.dispatchEvent(new MouseEvent(t, { bubbles: true, cancelable: true, view: window }));
  return true;
}
"""

JS_GRUP = """
() => {
  const hd = document.querySelector('#main header');
  if (!hd) return false;
  if (hd.querySelector('[data-icon*="group"], [data-icon*="community"]')) return true;
  const t = hd.innerText || '';
  return t.includes(',') && /(Anda|You)(,|\\s*$)|,\\s*(Anda|You)/.test(t);
}
"""

JS_READ = """
async ({n, seen}) => {
  const main = document.querySelector('#main');
  if (!main) return [];
  let rows = [...main.querySelectorAll('[data-id^="false_"]')]
    .filter(e => !e.parentElement || !e.parentElement.closest('[data-id^="false_"]'));
  if (!rows.length) rows = [...main.querySelectorAll('div.message-in')];
  if (!rows.length) {
    const mr = main.getBoundingClientRect();
    const mid = mr.left + mr.width / 2;
    rows = [...main.querySelectorAll('[data-pre-plain-text]')]
      .filter(e => { const r = e.getBoundingClientRect(); return r.width > 0 && (r.left + r.width / 2) < mid; })
      .map(e => e.closest('[role="row"]') || e.parentElement);
  }
  rows = rows.slice(-n);
  const out = [];
  for (const m of rows) {
    const holder = m.matches('[data-id]') ? m : (m.closest('[data-id]') || m.querySelector('[data-id]'));
    const id = holder ? holder.getAttribute('data-id') : '';
    if (id && seen.includes(id)) continue;
    const meta = m.querySelector('[data-pre-plain-text]');
    const pre = meta ? meta.getAttribute('data-pre-plain-text') : '';
    let text = [...m.querySelectorAll('span.selectable-text')]
      .filter(e => !e.querySelector('span.selectable-text'))
      .map(e => e.innerText).join('\\n').trim();
    if (!text && meta) text = meta.innerText.trim();
    const images = [];
    const imgEls = m.querySelectorAll('img[src^="blob:"]');
    for (const img of imgEls) {
      if (!(img.complete && img.naturalWidth > 0)) continue;
      try {
        const blob = await (await fetch(img.src)).blob();
        const data = await new Promise(r => {
          const f = new FileReader(); f.onload = () => r(f.result); f.readAsDataURL(blob);
        });
        images.push(data);
      } catch (e) {}
    }
    if (!text && !images.length) {
      text = m.innerText.replace(/\\s*\\d{1,2}[:.]\\d{2}(\\s?[APap][Mm])?\\s*$/, '').trim();
    }
    out.push({ id, pre, text, images, imgEls: imgEls.length });
  }
  return out;
}
"""

JS_VISIBLE_IDS = """
() => [...document.querySelectorAll('#main [data-id^="false_"]')].map(e => e.getAttribute('data-id'))
"""

JS_DIAG = """
() => {
  const q = s => document.querySelectorAll(s).length;
  const mask = s => (s || '').replace(/[0-9]/g, '#');
  const rows = [...document.querySelectorAll('#pane-side [role="listitem"], #pane-side [role="row"]')];
  const sample = rows.slice(0, 6).map(r => ({
    title: (r.querySelector('span[title]') || {}).title || null,
    aria: [...r.querySelectorAll('[aria-label]')].map(e => e.getAttribute('aria-label')).slice(0, 6),
    texts: [...r.querySelectorAll('span')].filter(s => s.children.length === 0)
      .map(s => s.textContent.trim()).filter(Boolean).slice(0, 8)
  }));
  const mainEl = document.querySelector('#main');
  const lastRows = mainEl ? [...mainEl.querySelectorAll('[data-id]')].slice(-4).map(e => ({
    tag: e.tagName,
    cls: String(e.className).slice(0, 120),
    id_mask: mask(e.getAttribute('data-id')).slice(0, 70),
    html: mask(e.outerHTML.replace(/>[^<]+</g, '>...<')).slice(0, 700)
  })) : [];
  const pre = mainEl ? [...mainEl.querySelectorAll('[data-pre-plain-text]')].slice(-4).map(e => {
    const r = e.getBoundingClientRect(); const mr = mainEl.getBoundingClientRect();
    return { pre_mask: mask(e.getAttribute('data-pre-plain-text')).slice(0, 40),
             tengah_x: Math.round(r.left + r.width / 2), tengah_main: Math.round(mr.left + mr.width / 2) };
  }) : [];
  const ft = document.querySelector('#main footer');
  const footer_ikon = ft ? [...ft.querySelectorAll('[data-icon],[aria-label],[title]')].slice(0, 30).map(e => ({
    tag: e.tagName, icon: e.getAttribute('data-icon'), aria: e.getAttribute('aria-label'), title: e.getAttribute('title')
  })) : null;
  return {
    footer_ikon,
    url: location.href,
    pane_side: q('#pane-side'),
    rows_listitem: q('#pane-side [role="listitem"]'),
    rows_row: q('#pane-side [role="row"]'),
    main: q('#main'),
    header_terbaca: (function () {
      const hd = document.querySelector('#main header');
      return hd ? mask(hd.innerText).slice(0, 80) : null;
    })(),
    pesan_masuk_data_id_false: q('#main [data-id^="false_"]'),
    pesan_keluar_data_id_true: q('#main [data-id^="true_"]'),
    data_id_lainnya: q('#main [data-id]'),
    message_in_class: q('#main div.message-in'),
    message_out_class: q('#main div.message-out'),
    selectable_text: q('#main span.selectable-text'),
    pre_plain_text: q('#main [data-pre-plain-text]'),
    sample,
    baris_pesan_terakhir: lastRows,
    posisi_pesan: pre
  };
}
"""


ATTACH_SEL = ('footer [data-icon^="plus"], footer [data-icon*="attach"], footer [data-icon="clip"], '
              'footer button[aria-label*="Attach" i], footer button[aria-label*="Lampir" i], '
              'footer [aria-label*="Attach" i], footer [aria-label*="Lampir" i], '
              'footer [title*="Attach" i], footer [title*="Lampir" i]')
PREVIEW_SEL = ('[data-icon*="send"], button[aria-label*="Send" i], button[aria-label*="Kirim" i], '
               'div[role="button"][aria-label*="Send" i], div[role="button"][aria-label*="Kirim" i]')

IMG_MENU_RE = re.compile(r"^\s*(Photos?\s*(&|and|dan)\s*videos?|Foto\s*(&|dan)\s*video|Photos|Foto)\s*$", re.I)
DOC_MENU_RE = re.compile(r"^\s*(Document|Dokumen)\s*$", re.I)

JS_MENU = """
() => {
  const vis = e => { const r = e.getBoundingClientRect(); return r.width > 0 && r.height > 0; };
  return {
    inputs: [...document.querySelectorAll('input[type="file"]')].map(i => ({ accept: i.getAttribute('accept'), multiple: i.multiple })),
    item_menu: [...document.querySelectorAll('li, [role="menuitem"], [role="button"], button')]
      .filter(e => vis(e) && !e.closest('#pane-side') && !e.closest('#main [data-id]'))
      .map(e => (e.innerText || e.getAttribute('aria-label') || '').trim())
      .filter(t => t && t.length < 30).slice(0, 40)
  };
}
"""

JS_LAMPIR = """
async ({name, mime, b64, mode}) => {
  const bin = atob(b64);
  const arr = new Uint8Array(bin.length);
  for (let i = 0; i < bin.length; i++) arr[i] = bin.charCodeAt(i);
  const file = new File([arr], name, { type: mime });
  const dt = new DataTransfer();
  dt.items.add(file);
  if (mode === 'paste') {
    const t = document.querySelector('#main footer div[contenteditable="true"]') || document.querySelector('#main footer');
    if (!t) return false;
    t.focus();
    t.dispatchEvent(new ClipboardEvent('paste', { clipboardData: dt, bubbles: true, cancelable: true }));
    return true;
  }
  const t = document.querySelector('#main');
  if (!t) return false;
  for (const type of ['dragenter', 'dragover', 'drop']) {
    t.dispatchEvent(new DragEvent(type, { dataTransfer: dt, bubbles: true, cancelable: true }));
  }
  return true;
}
"""


# ----------------------- Worker WhatsApp -----------------------
class WAWorker(threading.Thread):
    def __init__(self):
        super().__init__(daemon=True)
        self.cmd_q = queue.Queue()
        self.stop_ev = threading.Event()
        self.status = "Memulai..."
        self._pass_pertama = True   # pesan yang terbaca saat start dianggap lama: tidak dibalas otomatis
        self.seen = self._load_seen()
        self._tunda = {}   # key pesan -> berapa kali ditunda karena gambar belum selesai dimuat

    def sys(self, text, user=""):
        STORE.add(type="SYS", who="", text=text, images=[], user=user)

    def _load_seen(self):
        try:
            with open(SEEN_FILE, "r", encoding="utf-8") as f:
                return set(json.load(f))
        except Exception:
            return set()

    def _save_seen(self):
        try:
            with open(SEEN_FILE, "w", encoding="utf-8") as f:
                json.dump(list(self.seen)[-5000:], f)
        except Exception:
            pass

    def _log_sheet(self, sess, tipe, contact, message, image_path, waktu=None):
        payload = {"action": "log", "type": tipe, "contact": contact,
                   "message": message, "imagePath": image_path}
        if waktu:
            payload["waktu"] = waktu  # jam pesan sebenarnya (WhatsApp)
        try:
            res = sess.call(payload)
            if not res.get("ok"):
                raise RuntimeError(res.get("error", "gagal log"))
        except Exception as e:
            with open(PENDING_FILE, "a", encoding="utf-8") as f:
                f.write(json.dumps(dict(payload, client=sess.username), ensure_ascii=False) + "\n")
            self.sys(f"Gagal simpan ke sheet ({e}); disimpan di pending_log.jsonl")

    def _simpan_gambar(self, sess, sumber, ext, prefix, orig=None):
        """Simpan ke wa_images/, opsional upload ke Drive.
        Return (nama_file_lokal, string_untuk_kolom_ImagePath)."""
        nama = f"{prefix}_{datetime.now():%Y%m%d_%H%M%S}_{uuid.uuid4().hex[:6]}{ext}"
        lokal = os.path.join(IMG_DIR, nama)
        if isinstance(sumber, (bytes, bytearray)):
            with open(lokal, "wb") as f:
                f.write(sumber)
        else:
            shutil.copyfile(sumber, lokal)
        hasil = lokal
        if UPLOAD_KE_DRIVE:
            try:
                with open(lokal, "rb") as f:
                    b64 = base64.b64encode(f.read()).decode()
                mime = mimetypes.guess_type(nama)[0] or "application/octet-stream"
                nama_drive = f"{datetime.now():%Y%m%d_%H%M%S}_{orig or nama}"
                res = sess.call({"action": "upload", "filename": nama_drive, "mime": mime, "data": b64})
                if res.get("ok"):
                    hasil = res["url"]
                else:
                    self.sys(f"Upload Drive gagal: {res.get('error')}", user=sess.username)
            except Exception as e:
                self.sys(f"Upload Drive gagal: {e}", user=sess.username)
        return nama, hasil

    # --- loop utama
    def run(self):
        try:
            with sync_playwright() as pw:
                opsi = dict(user_data_dir=PROFILE_DIR, headless=HEADLESS,
                            args=["--disable-blink-features=AutomationControlled"])
                if HEADLESS:
                    opsi["viewport"] = {"width": 1366, "height": 900}
                else:
                    opsi["no_viewport"] = True
                try:
                    ctx = pw.chromium.launch_persistent_context(channel="chrome", **opsi)
                except Exception as e1:
                    try:
                        ctx = pw.chromium.launch_persistent_context(**opsi)
                    except Exception:
                        raise RuntimeError("Google Chrome tidak bisa dibuka. Pastikan Chrome terpasang dan "
                                           f"tidak ada program ini yang sedang berjalan ganda. Detail: {e1}")
                page = ctx.pages[0] if ctx.pages else ctx.new_page()
                page.goto(WA_URL)
                self._tunggu_login(page)
                try:
                    os.remove(QR_FILE)  # QR login jangan dibiarkan tersimpan
                except OSError:
                    pass
                self.status = "Terhubung"
                self.sys("WhatsApp Web terhubung")
                try:
                    r = SERVER_SESSION._login()
                    if r.get("ok"):
                        self.sys("Akun server OK: INBOX akan dicatat ke spreadsheet")
                    else:
                        self.sys(f"PERINGATAN: login akun server '{SERVER_SESSION.username}' GAGAL ({r.get('error')}). "
                                 f"INBOX tidak masuk spreadsheet. Jalankan ulang server dan login lagi.")
                except Exception as e:
                    self.sys(f"PERINGATAN: tidak bisa menghubungi Apps Script: {e}")

                while not self.stop_ev.is_set():
                    self._scan_inbox(page)
                    self._pass_pertama = False
                    self._cek_jadwal()
                    self._drain_cmds(page)
                    self.stop_ev.wait(POLL_DETIK)
                ctx.close()
        except Exception as e:
            self.status = "Terputus"
            self.sys(f"ERROR worker: {e}")

    # --- inbox
    def _tunggu_login(self, page):
        """Tunggu WhatsApp Web siap. Bila belum login, simpan gambar QR (mode tersembunyi)
        ke wa_qr.png dan tampilkan di halaman /qr (khusus admin)."""
        terakhir, diumumkan = 0, False
        while not self.stop_ev.is_set():
            try:
                page.wait_for_selector("#pane-side", timeout=4000)
                return
            except Exception:
                pass
            if not HEADLESS:
                self.status = "Menunggu scan QR di jendela Chrome..."
                continue
            self.status = f"Scan QR di http://{ip_lokal()}:{PORT}/qr (login sebagai admin)"
            if time.time() - terakhir < 10:
                continue
            try:
                kanvas = page.locator("canvas")
                if kanvas.count():
                    bb = kanvas.first.bounding_box()
                    clip = {"x": max(bb["x"] - 30, 0), "y": max(bb["y"] - 30, 0),
                            "width": bb["width"] + 60, "height": bb["height"] + 60}
                    page.screenshot(path=QR_FILE, clip=clip)
                else:
                    page.screenshot(path=QR_FILE)
                terakhir = time.time()
                if not diumumkan:
                    diumumkan = True
                    self.sys("Belum login WhatsApp. Scan QR di halaman /qr (login admin) atau buka file wa_qr.png.")
            except Exception:
                pass
        raise RuntimeError("dihentikan sebelum login WhatsApp")

    def _scan_inbox(self, page):
        try:
            if page.locator("#main").count():
                self._baca(page, page.evaluate(JS_HEADER), 5)
            for u in page.evaluate(JS_UNREAD):
                if not self._buka_baris(page, u):
                    continue
                time.sleep(1.5)
                self._baca(page, u["title"], min(u["n"] + 3, 50))
        except Exception as e:
            if str(e) != getattr(self, "_last_err", None):
                self._last_err = str(e)
                self.sys(f"scan inbox: {e}")

    def _terbuka(self, page, judul, detik):
        """True bila header chat yang sedang terbuka cocok dengan judul yang dituju."""
        akhir = time.time() + detik
        target = (judul or "").strip().lower()
        while True:
            try:
                h = (page.evaluate(JS_HEADER) or "").strip().lower()
            except Exception:
                h = ""
            if h and target and (h == target or h in target or target in h):
                return True
            if time.time() >= akhir:
                return False
            time.sleep(0.3)

    def _buka_baris(self, page, u):
        """Buka chat dari daftar dan pastikan chat yang benar yang terbuka. Mencoba beberapa cara:
        klik baris berdasarkan urutan, klik berdasarkan judul, lalu klik lewat JavaScript."""
        judul = u["title"]
        langkah = [
            lambda: page.locator(ROW_SEL).nth(u["idx"]).click(timeout=3000),
            lambda: page.locator("#pane-side").get_by_title(judul, exact=True).first.click(timeout=3000, force=True),
            lambda: page.evaluate(JS_KLIK_BARIS, judul),
        ]
        if self._terbuka(page, judul, 0.1):  # sudah terbuka
            return True
        for ambil in langkah:
            try:
                ambil()
            except Exception:
                continue
            if self._terbuka(page, judul, 3.5):
                return True
        try:
            h = page.evaluate(JS_HEADER)
        except Exception:
            h = None
        pesan = f"chat '{judul}' tidak bisa dibuka dari daftar (header yang terbuka: {h!r}); dicoba lagi nanti"
        if pesan != getattr(self, "_last_err2", None):
            self._last_err2 = pesan
            self.sys(pesan)
        return False

    def _baca(self, page, kontak, n):
        items = page.evaluate(JS_READ, {"n": n, "seen": list(self.seen)})
        try:
            grup_hdr = bool(page.evaluate(JS_GRUP))
        except Exception:
            grup_hdr = False
        for it in items:
            key = it["id"] or hashlib.md5((kontak + it["pre"] + it["text"]).encode()).hexdigest()
            if key in self.seen:
                continue
            if not it["images"] and (it.get("imgEls", 0) > 0 or not it["text"]):
                # gambar belum selesai dimuat WhatsApp: jangan ditandai "sudah dibaca", coba lagi
                # di pemindaian berikutnya (maksimal 8 kali, sekitar 25 detik)
                self._tunda[key] = self._tunda.get(key, 0) + 1
                if self._tunda[key] <= 8:
                    continue
            self._tunda.pop(key, None)
            self.seen.add(key)

            m = re.search(r"\]\s*(.*?):\s*$", it["pre"] or "")
            pengirim = m.group(1).strip() if m else ""
            m_id = re.match(r"^(?:true|false)_([^@_]+)@([A-Za-z.]+)", it["id"] or "")
            id_no, id_dom = (m_id.group(1), m_id.group(2)) if m_id else ("", "")
            grup = id_dom == "g.us" or grup_hdr or kontak in GRUP_KNOWN
            if grup:
                grup_catat(kontak)
            if grup:
                pengirim = peserta_nama(peserta_id(it["id"]), pengirim)
            nomor = id_no if (id_dom in ("c.us", "s.whatsapp.net") and id_no.isdigit()) else ""
            if grup:
                who = f"{kontak} ({pengirim})" if pengirim else kontak
            elif nomor:
                who = nomor if re.fullmatch(r"[+\d\s-]+", kontak) else f"{nomor} ({kontak})"
            else:
                who = kontak

            nama_lokal, paths = [], []
            for data in it["images"]:
                try:
                    head, b64 = data.split(",", 1)
                    mime = head.split(";")[0].replace("data:", "")
                    ext = "." + (mime.split("/")[-1].replace("jpeg", "jpg") or "jpg")
                    nm, hasil = self._simpan_gambar(SERVER_SESSION, base64.b64decode(b64), ext, "in")
                    nama_lokal.append(nm)
                    paths.append(hasil)
                except Exception as e:
                    self.sys(f"gagal simpan gambar: {e}")

            teks = it["text"] or ("" if paths else "[pesan non-teks]")
            terima = datetime.now()
            wkt = waktu_pesan(it["pre"], terima)
            self._log_sheet(SERVER_SESSION, "INBOX", who, teks, "; ".join(paths), wkt)
            chat_key = kontak if grup else (nomor or ALIAS.get(kontak) or kontak)
            pertama = not STORE.has_chat(chat_key)
            STORE.add(type="IN", who=who, chat=chat_key, name=kontak,
                      number=("" if grup else (nomor or ALIAS.get(kontak, ""))), group=grup, sender=(pengirim if grup else ""),
                      text=teks, images=nama_lokal,
                      **({"time": wkt, "diterima": terima.strftime("%Y-%m-%d %H:%M:%S")} if wkt else {}))
            if not grup and not self._pass_pertama:
                self._auto_balas(nomor or ALIAS.get(kontak, ""), kontak, chat_key, teks, pertama)
        self._save_seen()

    # --- outbox
    def _auto_balas(self, nomor, kontak, chat_key, teks, pertama):
        """Cocokkan pesan masuk dengan aturan balasan otomatis, lalu antrikan pengiriman."""
        try:
            if kontak in GRUP_KNOWN or chat_key in GRUP_KNOWN:  # grup tidak pernah dibalas otomatis
                return
            sekarang = datetime.now()
            r = AUTO.pilih(chat_key, teks, pertama, sekarang)
            if not r:
                return
            isi = AUTO.render(r.get("balasan_teks", ""), _nama_tampil(kontak, nomor, chat_key), nomor, sekarang)
            tmp, orig, is_img = None, "", True
            lamp = r.get("lampiran")
            if lamp:
                sumber = os.path.join(AUTO_DIR, os.path.basename(lamp["n"]))
                if os.path.isfile(sumber):
                    tmp_dir = os.path.join(TMP_DIR, uuid.uuid4().hex)
                    os.makedirs(tmp_dir, exist_ok=True)
                    orig = lamp["o"]
                    tmp = os.path.join(tmp_dir, orig)
                    shutil.copyfile(sumber, tmp)
                    is_img = bool(lamp.get("gambar"))
            if not isi and not tmp:
                return
            self.cmd_q.put({"no": nomor, "chat": "" if nomor else kontak, "text": isi, "tmp": tmp,
                            "orig": orig, "is_img": is_img, "sess": SERVER_SESSION,
                            "auto": r.get("nama", "otomatis"),
                            "not_before": time.time() + float(r.get("jeda_detik", 3))})
            AUTO.catat(chat_key, r)
        except Exception as e:
            self.sys(f"Balasan otomatis gagal disiapkan: {e}")

    def _cek_jadwal(self):
        """Antrikan pesan terjadwal yang waktunya sudah tiba."""
        try:
            for it in JADWAL.jatuh_tempo(datetime.now()):
                tmp, orig, is_img = None, "", True
                lamp = it.get("lampiran")
                if lamp:
                    sumber = os.path.join(JADWAL_DIR, os.path.basename(lamp["n"]))
                    if os.path.isfile(sumber):
                        tmp_dir = os.path.join(TMP_DIR, uuid.uuid4().hex)
                        os.makedirs(tmp_dir, exist_ok=True)
                        orig = lamp["o"]
                        tmp = os.path.join(tmp_dir, orig)
                        shutil.copyfile(sumber, tmp)
                        is_img = bool(lamp.get("gambar"))
                    elif not it.get("text"):
                        JADWAL.hasil(it["id"], False, "file lampiran tidak ditemukan")
                        continue
                self.cmd_q.put({"no": it.get("no", ""), "chat": it.get("chat", ""), "text": it.get("text", ""),
                                "tmp": tmp, "orig": orig, "is_img": is_img,
                                "sess": SESSIONS.get(it["user"]) or SERVER_SESSION,
                                "user_label": it["user"], "terjadwal": True, "jadwal_id": it["id"]})
        except Exception as e:
            self.sys(f"Pemeriksaan jadwal gagal: {e}")

    def _drain_cmds(self, page):
        tunda = []
        while not self.cmd_q.empty():
            cmd = self.cmd_q.get()
            if cmd.get("diag"):
                self._diag(page)
                continue
            if cmd.get("not_before", 0) > time.time():  # jeda sebelum balasan otomatis
                tunda.append(cmd)
                continue
            sukses, galat = True, ""
            try:
                self._kirim(page, cmd)
            except Exception as e:
                sukses, galat = False, str(e)[:200]
                self.sys(f"Gagal kirim ke {cmd.get('no') or cmd.get('chat')} (oleh {cmd.get('user_label') or cmd['sess'].username}): {e}",
                         user=cmd.get("user_label") or cmd["sess"].username)
            finally:
                if cmd.get("tmp"):
                    shutil.rmtree(os.path.dirname(cmd["tmp"]), ignore_errors=True)
            if cmd.get("jadwal_id"):
                JADWAL.hasil(cmd["jadwal_id"], sukses, galat)
        for c in tunda:
            self.cmd_q.put(c)

    def _buka_chat(self, page, cmd):
        """Buka chat lewat nomor (URL) atau lewat judul chat (klik daftar / pencarian)."""
        judul = (cmd.get("chat") or "").strip()
        if judul:
            if page.locator("#main").count() and (page.evaluate(JS_HEADER) or "").strip() == judul:
                return
            baris = page.locator("#pane-side").get_by_title(judul, exact=True)
            if baris.count():
                baris.first.click()
            else:
                page.keyboard.press("Control+Alt+/")
                time.sleep(0.6)
                page.keyboard.type(judul, delay=20)
                time.sleep(2)
                page.keyboard.press("Enter")
            try:
                page.wait_for_selector("#main footer", timeout=15000)
            except Exception:
                raise RuntimeError(f"chat '{judul}' tidak ditemukan")
        else:
            page.goto(f"{WA_URL}/send?phone={cmd['no']}")
            page.wait_for_selector("#pane-side", timeout=60000)
            try:
                page.wait_for_selector("#main footer", timeout=30000)
            except Exception:
                raise RuntimeError("chat tidak terbuka (nomor tidak terdaftar di WhatsApp?)")

    def _diag(self, page):
        try:
            info = page.evaluate(JS_DIAG)
            info["unread_terdeteksi"] = page.evaluate(JS_UNREAD)
            info["jumlah_seen"] = len(self.seen)
            try:
                if page.locator("#main footer").count():
                    btn = page.locator(ATTACH_SEL).first
                    btn.wait_for(state="visible", timeout=3000)
                    btn.click()
                    time.sleep(1)
                    info["menu_lampiran"] = page.evaluate(JS_MENU)
                    btn.click()
            except Exception as e:
                info["menu_lampiran_galat"] = str(e).splitlines()[0][:150]
            path = os.path.join(BASE_DIR, "diagnosa.txt")
            with open(path, "w", encoding="utf-8") as f:
                json.dump(info, f, indent=2, ensure_ascii=False)
            self.sys(f"Diagnosa tersimpan di {path} | baris chat: {info['rows_listitem']}+{info['rows_row']}, "
                     f"unread terdeteksi: {len(info['unread_terdeteksi'])}, "
                     f"pesan masuk di chat terbuka: {info['pesan_masuk_data_id_false']}")
        except Exception as e:
            self.sys(f"Diagnosa gagal: {e}")

    def _ada_preview(self, page, detik):
        try:
            page.wait_for_selector(PREVIEW_SEL, state="visible", timeout=detik * 1000)
            return True
        except Exception:
            return False

    def _injeksi(self, page, path, orig, mode):
        with open(path, "rb") as f:
            b64 = base64.b64encode(f.read()).decode()
        nama = orig or os.path.basename(path)
        mime = mimetypes.guess_type(nama)[0] or "application/octet-stream"
        if not page.evaluate(JS_LAMPIR, {"name": nama, "mime": mime, "b64": b64, "mode": mode}):
            raise RuntimeError("kolom chat tidak ditemukan")

    def _lampirkan(self, page, path, orig, is_img):
        """Lampirkan file ke chat yang terbuka.
        1) tombol lampiran -> menu 'Foto & video' / 'Dokumen' -> dialog pilih file (bukan 'Stiker')
        2) input file yang sesuai  3) tempel  4) seret"""
        galat = []
        try:
            btn = page.locator(ATTACH_SEL).first
            btn.wait_for(state="visible", timeout=5000)
            btn.click()
            time.sleep(0.8)
            item = page.get_by_text(IMG_MENU_RE if is_img else DOC_MENU_RE).last
            item.wait_for(state="visible", timeout=4000)
            with page.expect_file_chooser(timeout=8000) as fc:
                item.click()
            fc.value.set_files(path)
            if self._ada_preview(page, 15):
                return
            galat.append("menu: pratinjau tidak muncul")
        except Exception as e:
            galat.append("menu: " + str(e).splitlines()[0][:100])
        try:
            if is_img:  # hanya input 'Foto & video' (accept memuat image dan video), BUKAN input stiker
                inp = page.locator('input[type="file"][accept*="image"][accept*="video"]')
            else:
                inp = page.locator('input[type="file"][accept="*"]')
                if inp.count() == 0:
                    inp = page.locator('input[type="file"]:not([accept*="image"]):not([accept*="video"])')
            if inp.count() == 0:
                raise RuntimeError("input file yang sesuai tidak ada")
            inp.first.set_input_files(path, timeout=8000)
            if self._ada_preview(page, 15):
                return
            galat.append("input: pratinjau tidak muncul")
        except Exception as e:
            galat.append("input: " + str(e).splitlines()[0][:100])
        for mode in ("paste", "drop"):
            try:
                self._injeksi(page, path, orig, mode)
                if self._ada_preview(page, 15):
                    return
                galat.append(f"{mode}: pratinjau tidak muncul")
            except Exception as e:
                galat.append(f"{mode}: " + str(e).splitlines()[0][:100])
        raise RuntimeError("Gagal melampirkan file (" + " | ".join(galat) +
                           "). Buka chat lalu klik Diagnosa dan kirim diagnosa.txt")

    def _kirim(self, page, cmd):
        teks, gambar, sess = cmd["text"], cmd.get("tmp"), cmd["sess"]
        self._buka_chat(page, cmd)
        time.sleep(1.5)

        judul = (page.evaluate(JS_HEADER) or "").strip()
        if cmd.get("chat") and judul != cmd["chat"].strip():
            raise RuntimeError(f"chat yang terbuka '{judul}' bukan '{cmd['chat']}', pengiriman dibatalkan")
        target = cmd.get("no") or judul
        chat_key = cmd.get("no") or judul or target

        for i in page.evaluate(JS_VISIBLE_IDS):
            self.seen.add(i)

        path_log, nama_lokal, berkas = "", [], []
        if gambar:
            is_img = cmd.get("is_img", True)
            self._lampirkan(page, gambar, cmd.get("orig"), is_img)
            time.sleep(1)
            if teks:
                self._ketik(page, teks)
            page.keyboard.press("Enter")
            ext = os.path.splitext(gambar)[1] or ".bin"
            nm, path_log = self._simpan_gambar(sess, gambar, ext, "out", cmd.get("orig"))
            if is_img:
                nama_lokal = [nm]
            else:
                berkas = [{"n": nm, "o": cmd.get("orig") or nm}]
        else:
            page.locator('footer div[contenteditable="true"]').first.click()
            self._ketik(page, teks)
            page.keyboard.press("Enter")

        time.sleep(1.5)
        if gambar:  # tunggu unggahan selesai sebelum pindah halaman
            for sel in (PREVIEW_SEL, '#main [data-icon="msg-time"]'):
                try:
                    page.wait_for_selector(sel, state="hidden", timeout=90000)
                except Exception:
                    pass
        isi = teks or (f"[{'gambar' if cmd.get('is_img', True) else 'file'}] {cmd.get('orig') or ''}".strip()
                       if gambar else teks)
        if cmd.get("auto"):
            isi = "[AUTO] " + isi
        elif cmd.get("terjadwal"):
            isi = "[JADWAL] " + isi
        self._log_sheet(sess, "OUTBOX", target, isi, path_log)
        STORE.add(type="OUT", who=target, chat=chat_key, name=judul, number=(cmd.get("no") or ""),
                  text=teks, images=nama_lokal, files=berkas,
                  user=("[otomatis]" if cmd.get("auto") else (cmd.get("user_label") or sess.username)),
                  auto=cmd.get("auto", ""), terjadwal=bool(cmd.get("terjadwal")))
        if cmd.get("no"):
            alias_set(judul, cmd["no"])

    @staticmethod
    def _ketik(page, teks):
        baris = teks.split("\n")
        for i, b in enumerate(baris):
            if b:
                page.keyboard.type(b, delay=5)
            if i < len(baris) - 1:
                page.keyboard.press("Shift+Enter")


WORKER = WAWorker()


# ----------------------- Web (Flask) -----------------------
def load_secret():
    if os.path.exists(KEY_FILE):
        return open(KEY_FILE, "r").read().strip()
    k = secrets.token_hex(32)
    with open(KEY_FILE, "w") as f:
        f.write(k)
    return k


app = Flask(__name__)
app.secret_key = load_secret()
app.config["MAX_CONTENT_LENGTH"] = (MAX_UPLOAD_MB + 1) * 1024 * 1024
app.config["SESSION_COOKIE_HTTPONLY"] = True
app.config["SESSION_COOKIE_SAMESITE"] = "Lax"


def login_required(f):
    @wraps(f)
    def wrap(*a, **k):
        u = session.get("u")
        if not u or u not in SESSIONS:
            if request.path.startswith(("/api/", "/img/")):
                return jsonify(ok=False, error="login"), 401
            return redirect(url_for("login"))
        return f(*a, **k)
    return wrap


LOGIN_HTML = """<!doctype html><html lang="id"><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1"><title>Masuk - {{ t.nama }}</title>
{% if t.logo_url %}<link rel="icon" href="{{ t.logo_url }}">{% endif %}
<style>
:root{--brand:#00a884;--brand-dark:#128c7e;--accent:#25d366;--surface:#ffffff;--panel:#f0f2f5;--page-bg:#d1d7db;--text:#111b21;--muted:#667781;--border:#e4e8eb;--on-brand:#ffffff;--on-header:#ffffff;--radius:8px;--font:system-ui,-apple-system,"Segoe UI",Roboto,Arial,sans-serif}
*{box-sizing:border-box}
body{margin:0;font-family:var(--font);color:var(--text);background:var(--page-bg);min-height:100vh}
.lg{display:flex;min-height:100vh}
.lg-art{flex:1.15;display:flex;align-items:center;justify-content:center;padding:48px;color:var(--on-header);
  background:linear-gradient(135deg,var(--brand-dark),var(--brand));position:relative;overflow:hidden}
.lg-art::before,.lg-art::after{content:"";position:absolute;border-radius:50%;background:rgba(255,255,255,.07)}
.lg-art::before{width:520px;height:520px;right:-180px;top:-160px}
.lg-art::after{width:340px;height:340px;left:-120px;bottom:-120px}
.lg-in{position:relative;z-index:1;max-width:480px}
.lg-logo{max-width:200px;max-height:110px;object-fit:contain;margin-bottom:24px;background:rgba(255,255,255,.94);padding:10px 14px;border-radius:14px;box-shadow:0 8px 24px rgba(0,0,0,.2)}
.lg-mark{width:72px;height:72px;border-radius:20px;background:rgba(255,255,255,.18);display:flex;align-items:center;justify-content:center;margin-bottom:24px}
.lg-mark svg{width:38px;height:38px;stroke:currentColor;fill:none;stroke-width:1.8;stroke-linecap:round;stroke-linejoin:round}
.lg-art h1{margin:0 0 10px;font-size:34px;line-height:1.15;letter-spacing:-.5px}
.lg-art p{margin:0 0 28px;font-size:17px;opacity:.9;line-height:1.5}
.lg-feat{list-style:none;margin:0;padding:0;display:grid;gap:12px;font-size:15px}
.lg-feat li{display:flex;gap:10px;align-items:center}
.lg-feat li::before{content:"";width:22px;height:22px;border-radius:50%;flex:none;background:rgba(255,255,255,.2) url("data:image/svg+xml;utf8,<svg xmlns='http://www.w3.org/2000/svg' viewBox='0 0 24 24' fill='none' stroke='white' stroke-width='3' stroke-linecap='round' stroke-linejoin='round'><path d='M5 12l5 5 9-10'/></svg>") center/12px no-repeat}
.lg-form{flex:1;display:flex;flex-direction:column;align-items:center;justify-content:center;padding:32px;background:var(--panel)}
.card{background:var(--surface);width:100%;max-width:400px;padding:34px 32px;border-radius:calc(var(--radius) * 2);box-shadow:0 10px 40px rgba(11,20,26,.14)}
.card h2{margin:0 0 4px;font-size:24px}
.sub{margin:0 0 22px;color:var(--muted);font-size:14px}
label{display:block;font-size:13px;font-weight:600;margin:14px 0 6px}
input{width:100%;padding:12px 14px;border:1px solid var(--border);border-radius:var(--radius);font:inherit;background:var(--surface);color:var(--text);outline:0;transition:border-color .15s,box-shadow .15s}
input:focus{border-color:var(--brand);box-shadow:0 0 0 3px rgba(0,168,132,.18)}
button{width:100%;margin-top:22px;padding:13px;border:0;border-radius:var(--radius);background:var(--brand);color:var(--on-brand);font:inherit;font-weight:700;font-size:15px;cursor:pointer;transition:filter .15s,transform .1s}
button:hover{filter:brightness(1.07)}button:active{transform:scale(.99)}
.err{background:#fde8e8;color:#9b1c1c;border:1px solid #f8b4b4;padding:10px 12px;border-radius:var(--radius);font-size:14px;margin-bottom:6px}
.foot{margin-top:22px;color:var(--muted);font-size:12.5px}
@media(max-width:860px){
 .lg{flex-direction:column}.lg-art{flex:none;padding:28px 24px}.lg-art h1{font-size:26px}
 .lg-art p{margin-bottom:0;font-size:15px}.lg-feat{display:none}.lg-form{padding:24px 16px}
}
</style>
<link rel="stylesheet" href="/tema.css?v={{ t.ver }}">
</head><body>
<div class="lg">
 <section class="lg-art"><div class="lg-in">
  {% if t.logo_url %}<img class="lg-logo" src="{{ t.logo_url }}" alt="">
  {% else %}<div class="lg-mark"><svg viewBox="0 0 24 24"><path d="M21 11.5a8.4 8.4 0 0 1-12.2 7.5L3 20.5l1.6-5.5A8.4 8.4 0 1 1 21 11.5z"/></svg></div>{% endif %}
  <h1>{{ t.nama }}</h1>
  <p>{{ t.tagline }}</p>
  <ul class="lg-feat"><li>Satu layanan WhatsApp untuk seluruh tim</li><li>Riwayat, rekap, dan laporan terpusat</li><li>Balasan otomatis dan pesan terjadwal</li></ul>
 </div></section>
 <main class="lg-form">
  <form method="post" class="card">
   <h2>Masuk</h2>
   <p class="sub">Gunakan akun yang diberikan administrator.</p>
   {% if error %}<div class="err">{{ error }}</div>{% endif %}
   <label for="u">Username</label><input id="u" name="username" autofocus required autocomplete="username">
   <label for="p">Password</label><input id="p" name="password" type="password" required autocomplete="current-password">
   <button>Masuk</button>
  </form>
  <div class="foot">&copy; {{ t.nama }}</div>
 </main>
</div>
</body></html>"""


MAIN_HTML = """<!doctype html><html lang="id"><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1"><title>{{ t.nama }}</title>{% if t.logo_url %}<link rel="icon" href="{{ t.logo_url }}">{% endif %}
<style>
:root{--brand:#00a884;--brand-dark:#128c7e;--accent:#25d366;--out-bg:#d9fdd3;--in-bg:#ffffff;--chat-bg:#efeae2;--surface:#ffffff;--panel:#f0f2f5;--page-bg:#d1d7db;--text:#111b21;--muted:#667781;--border:#e4e8eb;--hover:#f5f6f6;--on-brand:#ffffff;--on-header:#ffffff;--radius:8px;--font:system-ui,-apple-system,"Segoe UI",Roboto,Arial,sans-serif;--fsm:1;--shadow:0 1px 2px rgba(11,20,26,.16)}
*{box-sizing:border-box}
html,body{height:100%}
body{margin:0;font-family:var(--font);color:var(--text);background-color:var(--page-bg);display:flex;justify-content:center;height:100vh;height:100dvh;
  background-image:linear-gradient(var(--brand-dark),var(--brand-dark));background-repeat:no-repeat;background-size:100% 128px}
button,input,select,textarea{font-family:inherit}
::-webkit-scrollbar{width:8px;height:8px}::-webkit-scrollbar-thumb{background:var(--border);border-radius:8px}::-webkit-scrollbar-thumb:hover{background:var(--muted)}
#app{display:flex;width:100%;max-width:1480px;height:calc(100% - 40px);margin:20px auto;background:var(--surface);border-radius:14px;overflow:hidden;box-shadow:0 8px 30px rgba(11,20,26,.28)}
@media(max-width:1100px){body{background-image:none}#app{height:100%;margin:0;border-radius:0}}

/* ---- sidebar ---- */
#side{width:400px;min-width:320px;display:flex;flex-direction:column;border-right:1px solid var(--border);min-height:0;background:var(--surface)}
#brand{display:flex;align-items:center;gap:12px;padding:14px 18px;color:var(--on-header);background:linear-gradient(135deg,var(--brand-dark),var(--brand))}
#brand img{width:42px;height:42px;border-radius:11px;object-fit:contain;background:rgba(255,255,255,.94);padding:3px;flex:none}
#brand .bm{width:42px;height:42px;border-radius:11px;background:rgba(255,255,255,.18);display:flex;align-items:center;justify-content:center;flex:none}
#brand .bm svg{width:22px;height:22px;stroke:currentColor;fill:none;stroke-width:1.9;stroke-linecap:round;stroke-linejoin:round}
#brand .bn{font-weight:700;font-size:16px;line-height:1.2;white-space:nowrap;overflow:hidden;text-overflow:ellipsis}
#brand .bt{font-size:12px;opacity:.85;white-space:nowrap;overflow:hidden;text-overflow:ellipsis}
#brand>div:last-child{min-width:0}
#sh0{background:var(--panel);padding:10px 14px;display:flex;align-items:center;gap:8px;min-height:62px;border-bottom:1px solid var(--border)}
#sh0 .me{flex:1;min-width:0}
#me1{font-weight:600;font-size:14.5px;white-space:nowrap;overflow:hidden;text-overflow:ellipsis}
#me1[data-role]::after{content:attr(data-role);margin-left:7px;font-size:10px;font-weight:700;background:var(--brand);color:var(--on-brand);padding:2px 8px;border-radius:999px;vertical-align:1px;letter-spacing:.3px}
#st{font-size:12px;color:var(--muted);display:flex;align-items:center;gap:6px;white-space:nowrap;overflow:hidden;text-overflow:ellipsis}
#st::before{content:"";width:8px;height:8px;border-radius:50%;background:var(--muted);flex:none}
#st.ok::before{background:#22c55e;box-shadow:0 0 0 3px rgba(34,197,94,.2)}
.ib{border:0;background:none;cursor:pointer;color:var(--muted);padding:7px;border-radius:50%;display:inline-flex;align-items:center;justify-content:center;transition:background .15s,color .15s;text-decoration:none;flex:none}
.ib:hover{background:var(--hover);color:var(--brand)}
.ib svg{width:20px;height:20px;stroke:currentColor;fill:none;stroke-width:2;stroke-linecap:round;stroke-linejoin:round}
label.ib{display:inline-flex}
#sh{padding:10px 14px;background:var(--surface)}
#flt{width:100%;padding:10px 14px 10px 40px;border:1px solid transparent;border-radius:10px;background:var(--panel) url("data:image/svg+xml;utf8,<svg xmlns='http://www.w3.org/2000/svg' viewBox='0 0 24 24' fill='none' stroke='%238696a0' stroke-width='2' stroke-linecap='round'><circle cx='11' cy='11' r='7'/><path d='M21 21l-4.3-4.3'/></svg>") no-repeat 12px center/18px;color:var(--text);font-size:14px;outline:0;transition:border-color .15s,background-color .15s}
#flt:focus{border-color:var(--brand);background-color:var(--surface)}
#clist{flex:1;overflow-y:auto}
.noc{padding:32px 24px;color:var(--muted);text-align:center;font-size:14px;line-height:1.6}
.av{width:48px;height:48px;border-radius:50%;color:#fff;display:flex;align-items:center;justify-content:center;font-weight:600;font-size:18px;flex:none}
.ci{display:flex;gap:13px;padding:0 16px;cursor:pointer;align-items:center;transition:background .12s}
.ci:hover{background:var(--hover)}.ci.act{background:var(--panel)}
.cm{flex:1;min-width:0;border-bottom:1px solid var(--border);padding:13px 0}
.cr1{display:flex;gap:8px;align-items:baseline}
.cn{flex:1;font-weight:500;font-size:calc(16px * var(--fsm));white-space:nowrap;overflow:hidden;text-overflow:ellipsis}
.ct{font-size:12px;color:var(--muted)}.ct.u{color:var(--brand);font-weight:600}
.cr2{display:flex;gap:8px;margin-top:3px;align-items:center}
.cs{flex:1;font-size:calc(13.5px * var(--fsm));color:var(--muted);white-space:nowrap;overflow:hidden;text-overflow:ellipsis}
.cb{background:var(--brand);color:var(--on-brand);font-size:11.5px;font-weight:700;border-radius:999px;min-width:21px;text-align:center;padding:2px 7px}
.ow{color:var(--brand);font-size:12px;font-weight:500}

/* ---- panel chat ---- */
#main{flex:1;display:flex;flex-direction:column;min-width:0;min-height:0;background-color:var(--chat-bg)}
#chead{background:var(--panel);padding:8px 16px;display:none;align-items:center;gap:12px;min-height:62px;border-bottom:1px solid var(--border);box-shadow:var(--shadow);position:relative;z-index:2}
#chead .av{width:42px;height:42px;font-size:16px}
#back{display:none}
.ch{flex:1;min-width:0}
#cname{font-weight:600;font-size:calc(16px * var(--fsm));white-space:nowrap;overflow:hidden;text-overflow:ellipsis}
#csub{font-size:12.5px;color:var(--muted);white-space:nowrap;overflow:hidden;text-overflow:ellipsis}
#asg{display:none;font-size:13px;padding:7px 14px;border-radius:999px;border:1px solid var(--border);background:var(--surface);color:var(--text);cursor:pointer;transition:border-color .15s,color .15s}
#asg:hover{border-color:var(--brand);color:var(--brand)}
#newno{display:none;padding:9px 14px;border:1px solid var(--border);border-radius:10px;flex:1;max-width:340px;font-size:14px;background:var(--surface);color:var(--text);outline:0}
#newno:focus{border-color:var(--brand)}
#sys{display:none;background:#fff3cd;color:#664d03;font-size:13px;padding:7px 16px;border-bottom:1px solid rgba(0,0,0,.06)}
#empty{margin:auto;text-align:center;color:var(--muted);padding:32px;max-width:440px;line-height:1.6}
#empty img{max-width:200px;max-height:130px;object-fit:contain;margin-bottom:14px}
#empty .em{width:84px;height:84px;margin:0 auto 16px;border-radius:24px;background:var(--surface);display:flex;align-items:center;justify-content:center;color:var(--brand);box-shadow:var(--shadow)}
#empty .em svg{width:42px;height:42px;stroke:currentColor;fill:none;stroke-width:1.7;stroke-linecap:round;stroke-linejoin:round}
#empty h2{margin:0 0 4px;color:var(--text);font-size:24px}
#empty p{margin:0 0 12px}
#empty small{display:inline-block;background:var(--surface);padding:8px 18px;border-radius:14px;box-shadow:var(--shadow)}
#log{flex:1;overflow-y:auto;padding:18px 7%;display:none;flex-direction:column;gap:3px}
.dsep{align-self:center;background:var(--surface);color:var(--muted);font-size:12px;padding:4px 14px;border-radius:999px;margin:10px 0;box-shadow:var(--shadow)}
.m{max-width:68%;padding:7px 10px 5px 11px;font-size:calc(14.2px * var(--fsm));box-shadow:var(--shadow);word-wrap:break-word;white-space:pre-wrap;border-radius:var(--radius);line-height:1.4;color:var(--text)}
.in{background:var(--in-bg);align-self:flex-start;border-top-left-radius:0}
.out{background:var(--out-bg);align-self:flex-end;border-top-right-radius:0}
.m.sys{background:#fff3cd;color:#664d03;align-self:center;font-size:13px;border-radius:var(--radius)}
.w{font-size:12.5px;font-weight:600;margin-bottom:2px}
.t{font-size:11px;color:var(--muted);text-align:right;margin-top:2px;white-space:nowrap}
.t b{font-weight:400;margin-left:3px}
.m img{max-width:280px;max-height:300px;border-radius:calc(var(--radius) - 2px);display:block;margin:2px 0 4px;cursor:pointer}
.fc{display:flex;gap:10px;align-items:center;background:rgba(127,127,127,.12);border-radius:var(--radius);padding:9px 11px;margin:2px 0 4px;color:inherit;text-decoration:none;max-width:300px;transition:background .15s}
.fc:hover{background:rgba(127,127,127,.2)}
.fc span{font-size:26px}.fc div{font-size:13.5px;word-break:break-all}
.pend{opacity:.75}
#chip{display:none;background:var(--panel);padding:6px 16px;font-size:13px;color:var(--muted);align-items:center;gap:8px;border-top:1px solid var(--border)}
#f{display:none;background:var(--panel);padding:10px 14px;gap:6px;align-items:flex-end;border-top:1px solid var(--border)}
#tx{flex:1;resize:none;max-height:120px;height:44px;padding:11px 17px;border:1px solid transparent;border-radius:24px;font-size:calc(15px * var(--fsm));background:var(--surface);color:var(--text);outline:0;box-shadow:var(--shadow);transition:border-color .15s}
#tx:focus{border-color:var(--brand)}
#bt{width:46px;height:46px;border:0;border-radius:50%;background:var(--brand);color:var(--on-brand);cursor:pointer;display:flex;align-items:center;justify-content:center;flex:none;transition:filter .15s,transform .1s}
#bt:hover{filter:brightness(1.08)}#bt:active{transform:scale(.93)}#bt:disabled{opacity:.5}
#bt svg{width:20px;height:20px;stroke:currentColor;fill:none;stroke-width:2;stroke-linecap:round;stroke-linejoin:round;margin-left:-2px}

/* ---- jendela dialog ---- */
#modal,#smodal,#lmodal{display:none;position:fixed;inset:0;background:rgba(11,20,26,.5);align-items:center;justify-content:center;z-index:9;backdrop-filter:blur(2px)}
#modal .box,.box2{background:var(--surface);color:var(--text);border-radius:16px;padding:24px;width:360px;max-width:94vw;max-height:90vh;overflow:auto;box-shadow:0 20px 50px rgba(0,0,0,.35)}
#modal h3,.box2 h3{margin:0 0 10px;font-size:18px}
#modal select,#modal input,.box2 input,.box2 select{width:100%;padding:10px 12px;border:1px solid var(--border);border-radius:10px;font-size:14px;background:var(--surface);color:var(--text);outline:0}
#modal select{margin:10px 0}
#modal select:focus,#modal input:focus,.box2 input:focus,.box2 select:focus{border-color:var(--brand)}
.box2 label{display:block;font-size:13px;font-weight:600;margin:10px 0 4px}
#modal .r,.box2 .r{display:flex;gap:8px;justify-content:flex-end;margin-top:16px}
#modal button,.box2 button{padding:9px 18px;border:1px solid var(--border);border-radius:10px;cursor:pointer;font-size:14px;background:var(--surface);color:var(--text)}
#modal button:hover,.box2 button:hover{border-color:var(--brand)}
#msave,#s_simpan{background:var(--brand)!important;color:var(--on-brand)!important;border-color:transparent!important;font-weight:600}
.jt{width:100%;border-collapse:collapse;font-size:13px}.jt td,.jt th{padding:8px 8px;border-bottom:1px solid var(--border);text-align:left}
.jt th{color:var(--muted);font-weight:600;font-size:12px}

/* ---- rekap cepat ---- */
#rekap{display:none;flex:1;overflow:auto;padding:22px 26px;background:var(--panel)}
#rekap h3{margin:0 0 12px}
.rf{display:flex;gap:10px;align-items:center;flex-wrap:wrap;margin-bottom:16px;font-size:14px}
.rf input{padding:7px 10px;border:1px solid var(--border);border-radius:8px;background:var(--surface);color:var(--text)}
.rf button,.rbk{padding:8px 16px;background:var(--brand);color:var(--on-brand);border:0;border-radius:8px;cursor:pointer}
.rt{width:100%;border-collapse:collapse;background:var(--surface);font-size:14px;box-shadow:var(--shadow);border-radius:10px;overflow:hidden}
.rt th{background:var(--panel);text-align:left;padding:10px 12px;font-weight:600;color:var(--muted);font-size:12.5px}
.rt td{padding:10px 12px;border-top:1px solid var(--border);max-width:260px;overflow:hidden;text-overflow:ellipsis;white-space:nowrap}
.rt td.n,.rt th.n{text-align:right}
.rt tr.rk{cursor:pointer}.rt tr.rk:hover{background:var(--hover)}
.rt tr.tot td{font-weight:700;background:var(--panel)}
.rhint{color:var(--muted);font-size:13px;margin-top:12px}

@media(max-width:760px){
 #side{width:100%;min-width:0}#main{display:none}
 #app.open #side{display:none}#app.open #main{display:flex}
 #back{display:inline-flex}#log{padding:12px 10px}.m{max-width:86%}
}
</style>
<link rel="stylesheet" href="/tema.css?v={{ t.ver }}">
</head><body data-u="{{ user }}">
<div id="app">
<aside id="side">
 <div id="brand">{% if t.logo_url %}<img src="{{ t.logo_url }}" alt="">{% else %}<div class="bm"><svg viewBox="0 0 24 24"><path d="M21 11.5a8.4 8.4 0 0 1-12.2 7.5L3 20.5l1.6-5.5A8.4 8.4 0 1 1 21 11.5z"/></svg></div>{% endif %}<div><div class="bn">{{ t.nama }}</div><div class="bt">{{ t.tagline }}</div></div></div>
 <div id="sh0"><div class="av" id="meav" style="background:#00a884"></div>
  <div class="me"><div id="me1"></div><div id="st">...</div></div>
  <button class="ib" id="rk" title="Rekap cepat (admin)" style="display:none"><svg viewBox="0 0 24 24"><path d="M4 20V10M10 20V4M16 20v-7M22 20H2"/></svg></button>
  <a class="ib" id="adm" href="/admin" target="_blank" title="Rekap, laporan &amp; tampilan (admin)" style="display:none"><svg viewBox="0 0 24 24"><path d="M14 3H6a2 2 0 0 0-2 2v14a2 2 0 0 0 2 2h12a2 2 0 0 0 2-2V9z"/><path d="M14 3v6h6M8 13h8M8 17h5"/></svg></a>
  <button class="ib" id="jl" title="Pesan terjadwal"><svg viewBox="0 0 24 24"><circle cx="12" cy="12" r="9"/><path d="M12 7v5l3 2"/></svg></button>
  <button class="ib" id="nb" title="Pesan baru"><svg viewBox="0 0 24 24"><path d="M12 20h9"/><path d="M16.5 3.5a2.1 2.1 0 0 1 3 3L7 19l-4 1 1-4z"/></svg></button>
  <a class="ib" href="/logout" title="Keluar"><svg viewBox="0 0 24 24"><path d="M9 21H5a2 2 0 0 1-2-2V5a2 2 0 0 1 2-2h4"/><path d="M16 17l5-5-5-5M21 12H9"/></svg></a></div>
 <div id="sh"><input id="flt" placeholder="Cari nama, nomor, atau pesan"></div>
 <div id="clist"></div>
</aside>
<main id="main">
 <div id="chead"><button class="ib" id="back" title="Kembali"><svg viewBox="0 0 24 24"><path d="M19 12H5M12 19l-7-7 7-7"/></svg></button><div id="hav"></div>
  <div class="ch"><div id="cname"></div><div id="csub"></div></div>
  <button id="asg" type="button">&#8618; Lempar chat</button>
  <input id="newno" placeholder="Nomor tujuan (0812... / 62812...)"></div>
 <div id="sys"></div>
 <div id="rekap">
  <h3>Rekap per Username</h3>
  <div class="rf">Dari <input type="date" id="rdari"> Sampai <input type="date" id="rsampai">
   <button id="rgo" type="button">Tampilkan</button></div>
  <div id="rbody"></div>
 </div>
 <div id="empty">{% if t.logo_url %}<img src="{{ t.logo_url }}" alt="">{% else %}<div class="em"><svg viewBox="0 0 24 24"><path d="M21 11.5a8.4 8.4 0 0 1-12.2 7.5L3 20.5l1.6-5.5A8.4 8.4 0 1 1 21 11.5z"/></svg></div>{% endif %}<h2>{{ t.nama }}</h2><p>{{ t.tagline }}</p><small>Pilih chat di sebelah kiri atau klik tombol pensil untuk pesan baru</small></div>
 <div id="log"></div>
 <div id="chip"><span id="chipn"></span><button class="ib" id="chipx" type="button">&#10005;</button></div>
 <form id="f">
  <label class="ib" for="im" title="Lampirkan gambar / file"><svg viewBox="0 0 24 24"><path d="M21 11.5l-8.6 8.6a5.5 5.5 0 0 1-7.8-7.8l9-9a3.7 3.7 0 0 1 5.2 5.2l-9 9a1.8 1.8 0 0 1-2.6-2.6l8.3-8.3"/></svg></label>
  <input id="im" type="file" hidden
   accept=".jpg,.jpeg,.png,.webp,.gif,.pdf,.doc,.docx,.xls,.xlsx,.ppt,.pptx,.txt,.csv,.zip,.rar,.7z">
  <button class="ib" id="sch" type="button" title="Jadwalkan pesan ini"><svg viewBox="0 0 24 24"><circle cx="12" cy="12" r="9"/><path d="M12 7v5l3 2"/></svg></button>
  <textarea id="tx" placeholder="Ketik pesan" rows="1"></textarea>
  <button id="bt" title="Kirim"><svg viewBox="0 0 24 24"><path d="M22 2L11 13"/><path d="M22 2l-7 20-4-9-9-4z"/></svg></button>
 </form>
</main>
</div>
<div id="modal"><div class="box">
 <h3>Lempar chat ke</h3><div id="mchat" style="color:var(--muted)"></div>
 <select id="msel"></select>
 <input id="mnote" placeholder="Catatan untuk penerima (opsional)" maxlength="200" style="margin-bottom:6px">
 <div class="r"><button id="mcancel" type="button">Batal</button><button id="msave" type="button">Simpan</button></div>
</div></div>
<div id="smodal"><div class="box2">
 <h3>&#9200; Jadwalkan pesan</h3>
 <div id="s_tujuan" style="color:var(--muted);margin-bottom:8px"></div>
 <div id="s_isi" style="background:var(--panel);border-radius:10px;padding:10px;white-space:pre-wrap;max-height:90px;overflow:auto"></div>
 <label>Tanggal</label><input type="date" id="s_tgl">
 <label>Jam</label><input type="time" id="s_jam">
 <label>Ulangi</label><select id="s_ulang"><option value="sekali">Sekali saja</option><option value="harian">Setiap hari</option><option value="mingguan">Setiap minggu</option><option value="bulanan">Setiap bulan</option></select>
 <div id="s_sw" style="display:none"><label>Sampai tanggal (opsional)</label><input type="date" id="s_sampai"></div>
 <div class="r"><button id="s_batal" type="button">Batal</button><button id="s_simpan" type="button">Jadwalkan</button></div>
</div></div>
<div id="lmodal"><div class="box2" style="width:640px">
 <h3>&#9200; Pesan terjadwal</h3><div id="lbody"></div>
 <div class="r"><button id="l_tutup" type="button">Tutup</button></div>
</div></div>
<script>
const $=id=>document.getElementById(id);
const SYSK='\\u2699 Sistem';
const USER=document.body.dataset.u||'';
const MAXMB=20;
let last=0, chats=new Map(), all=[], cur=null, firstLoad=true, lastDate='', lastShown='', pend=[], sysTimer=null;
let admin=false, IZ=new Set(), owners={}, epoch=null, users=[], ownKey='', ids=new Set(), rekapUser=null;

function digitsOnly(s){return /^[0-9]{8,15}$/.test(s||'');}
function numLike(s){return /^[+0-9 -]+$/.test(s||'');}
function fmtNo(n){
  if(!n)return '';
  if(n.indexOf('62')===0){return '+62 '+n.slice(2).replace(/^([0-9]{3})([0-9]{3,4})([0-9]+)$/,'$1-$2-$3');}
  return '+'+n;
}
function key(e){return e.type==='SYS'?SYSK:(e.chat||e.who||'');}
const BADN=/info kontak|contact info|click here|klik di sini/i;
function dispName(c){
  if(c.k===SYSK)return c.k;
  if(c.name&&!numLike(c.name)&&!BADN.test(c.name))return c.name;
  if(c.number)return fmtNo(c.number);
  if(digitsOnly(c.k))return fmtNo(c.k);
  if(BADN.test(c.name||c.k))return 'Chat lama';
  return c.name||c.k;
}
function subtitle(c){
  if(c.k===SYSK)return 'Log sistem server';
  const n=c.number||(digitsOnly(c.k)?c.k:'');
  let s='';
  if(n&&dispName(c)!==fmtNo(n))s=fmtNo(n);
  else if(c.group)s='Grup';
  if(admin)s+=(s?' \\u00B7 ':'')+'Pemilik: '+(owners[c.k]||'belum ditetapkan');
  return s;
}
function colorOf(s){let h=0;for(let i=0;i<s.length;i++)h=(h*31+s.charCodeAt(i))%360;return 'hsl('+h+',45%,42%)';}
function avatar(c){
  const d=document.createElement('div');d.className='av';
  const n=dispName(c);
  d.style.background=c.k===SYSK?'#667781':colorOf(n);
  d.textContent=c.k===SYSK?'\\u2699':(c.group?'\\uD83D\\uDC65':((n.replace(/[^A-Za-z0-9]/g,'')[0]||'#').toUpperCase()));
  return d;
}
function p2(n){return String(n).padStart(2,'0');}
function ymd(d){return d.getFullYear()+'-'+p2(d.getMonth()+1)+'-'+p2(d.getDate());}
function dayLabel(ds){
  const t=new Date();
  if(ds===ymd(t))return 'Hari ini';
  if(ds===ymd(new Date(t.getTime()-86400000)))return 'Kemarin';
  return ds.slice(8,10)+'/'+ds.slice(5,7)+'/'+ds.slice(0,4);
}
function hhmm(t){return (t||'').slice(11,16);}
function listTime(t){const ds=(t||'').slice(0,10);return ds===ymd(new Date())?hhmm(t):ds.slice(8,10)+'/'+ds.slice(5,7)+'/'+ds.slice(2,4);}
function nearBottom(){const l=$('log');return l.scrollHeight-l.scrollTop-l.clientHeight<140;}
function toBottom(){const l=$('log');l.scrollTop=l.scrollHeight;}
function showSys(t){
  const s=$('sys');s.textContent=t;s.style.display='block';
  clearTimeout(sysTimer);sysTimer=setTimeout(()=>{s.style.display='none';},30000);
}
function isImg(name){return /[.](jpg|jpeg|png|webp|gif)$/i.test(name||'');}

function bubble(e){
  const d=document.createElement('div');
  d.className='m '+(e.type==='IN'?'in':e.type==='OUT'?'out':'sys');
  let lbl='';
  if(e.type==='IN'){
    if(e.sender)lbl=e.sender;
    else if(!e.name&&e.who&&e.who!==key(e))lbl=e.who;
  }
  if(lbl){
    const w=document.createElement('div');w.className='w';w.textContent=lbl;w.style.color=colorOf(lbl);d.appendChild(w);
  }
  (e.images||[]).forEach(n=>{
    const a=document.createElement('a');a.href='/img/'+encodeURIComponent(n);a.target='_blank';
    const i=document.createElement('img');i.src='/img/'+encodeURIComponent(n);
    a.appendChild(i);d.appendChild(a);
  });
  (e.files||[]).forEach(f=>{
    const a=document.createElement('a');a.className='fc';a.href='/img/'+encodeURIComponent(f.n);a.target='_blank';
    const ic=document.createElement('span');ic.textContent='\\uD83D\\uDCC4';
    const nm=document.createElement('div');nm.textContent=f.o||f.n;
    a.appendChild(ic);a.appendChild(nm);d.appendChild(a);
  });
  if(e.text){const p=document.createElement('div');p.textContent=e.text;d.appendChild(p);}
  if(e.type!=='SYS'){
    const t=document.createElement('div');t.className='t';
    let s=hhmm(e.time);
    if(e.type==='OUT'&&e.auto)s='🤖 '+e.auto+' \\u00B7 '+s;
    else if(e.type==='OUT'&&e.user)s=(e.terjadwal?'⏰ ':'')+e.user+' \\u00B7 '+s;
    t.textContent=s;
    if(e.type==='OUT'){const b=document.createElement('b');b.style.color='#53bdeb';b.textContent=' \\u2713';t.appendChild(b);}
    d.appendChild(t);
  }
  return d;
}

function appendMsg(e){
  const l=$('log');
  const ds=(e.time||'').slice(0,10);
  if(ds&&ds!==lastDate){
    lastDate=ds;
    const s=document.createElement('div');s.className='dsep';s.textContent=dayLabel(ds);l.appendChild(s);
  }
  l.appendChild(bubble(e));
  if(e.type!=='SYS')lastShown=e.time||'';
}

function dropPending(k,text,hasFile){
  const i=pend.findIndex(p=>p.chat===k&&p.text===text&&p.hasFile===hasFile);
  if(i>=0){pend[i].el.remove();clearTimeout(pend[i].tm);pend.splice(i,1);}
}

function cmpMsg(a,b){return a.time<b.time?-1:(a.time>b.time?1:a.id-b.id);}
function redrawChat(k){
  const l=$('log');l.textContent='';lastDate='';lastShown='';
  all.filter(e=>key(e)===k).sort(cmpMsg).forEach(appendMsg);
  pend.filter(p=>p.chat===k).forEach(p=>l.appendChild(p.el));
}
function snipFull(e){
  const s=snippet(e);
  if(e.type==='IN'&&e.group&&e.sender)return e.sender+': '+s;
  if(e.type==='OUT')return '\\u2713 '+s;
  return s;
}
function snippet(e){
  if(e.text)return e.text;
  if(e.images&&e.images.length)return '\\uD83D\\uDCF7 Foto';
  if(e.files&&e.files.length)return '\\uD83D\\uDCC4 '+(e.files[0].o||'File');
  return '';
}

function addItem(e){
  if(ids.has(e.id))return;
  ids.add(e.id);
  all.push(e);
  if(e.type==='SYS'&&!firstLoad)showSys(e.text);
  const k=key(e);
  let c=chats.get(k);
  if(!c){c={k:k,last:0,time:'',snip:'',unread:0,name:'',number:'',group:false};chats.set(k,c);}
  c.last=Math.max(c.last,e.id);
  const terbaru=!c.time||e.time>=c.time;
  if(terbaru)c.time=e.time;
  if(e.type!=='SYS'){
    if(e.name)c.name=e.name;
    if(e.number)c.number=e.number;
    if(e.group)c.group=true;
  }
  if(terbaru)c.snip=snipFull(e);
  if(e.type==='IN'&&!firstLoad&&k!==cur)c.unread++;
  if(e.type==='OUT')dropPending(k,e.text,!!((e.images&&e.images.length)||(e.files&&e.files.length)));
  if(k===cur){
    const nb=nearBottom();
    if(lastShown&&e.type!=='SYS'&&e.time<lastShown)redrawChat(k);else appendMsg(e);
    if(nb||e.type==='OUT')toBottom();
  }
}

function renderList(){
  const q=$('flt').value.trim().toLowerCase();
  const arr=[...chats.values()].filter(c=>{
    if(!q)return true;
    return (dispName(c)+' '+(c.number||'')+' '+c.k+' '+c.snip).toLowerCase().includes(q);
  }).sort((a,b)=>b.time>a.time?1:(b.time<a.time?-1:b.last-a.last));
  const box=$('clist');box.textContent='';
  if(!arr.length){
    const n=document.createElement('div');n.className='noc';
    n.textContent=q?'Tidak ada chat yang cocok.':(admin?'Belum ada chat.':'Belum ada chat milik Anda. Klik \\u270E untuk mengirim pesan ke nomor baru.');
    box.appendChild(n);return;
  }
  arr.forEach(c=>{
    const d=document.createElement('div');d.className='ci'+(c.k===cur?' act':'');
    d.appendChild(avatar(c));
    const m=document.createElement('div');m.className='cm';
    const r1=document.createElement('div');r1.className='cr1';
    const n=document.createElement('div');n.className='cn';n.textContent=dispName(c);
    const t=document.createElement('div');t.className='ct'+(c.unread?' u':'');t.textContent=listTime(c.time);
    r1.appendChild(n);r1.appendChild(t);
    const r2=document.createElement('div');r2.className='cr2';
    const s=document.createElement('div');s.className='cs';
    if((admin||IZ.has('tetapkan'))&&c.k!==SYSK){
      const o=document.createElement('span');o.className='ow';
      o.textContent=owners[c.k]?('\\uD83D\\uDC64'+owners[c.k]+' \\u00B7 '):'';
      s.appendChild(o);
    }
    s.appendChild(document.createTextNode(c.snip));
    r2.appendChild(s);
    if(c.unread){const b=document.createElement('div');b.className='cb';b.textContent=c.unread;r2.appendChild(b);}
    m.appendChild(r1);m.appendChild(r2);d.appendChild(m);
    d.onclick=()=>openChat(c.k);
    box.appendChild(d);
  });
}

function showPane(on){
  $('rekap').style.display='none';
  $('chead').style.display=on?'flex':'none';
  $('empty').style.display=on?'none':'block';
  $('log').style.display=on?'flex':'none';
  $('f').style.display=(on&&IZ.has('kirim'))?'flex':'none';
}
function setHead(c,title,sub){
  const h=$('hav');h.textContent='';
  if(c)h.appendChild(avatar(c));
  $('cname').textContent=title;$('csub').textContent=sub||'';
}
function refreshHead(){
  if(!cur||cur==='__new__')return;
  const c=chats.get(cur);if(!c)return;
  setHead(c,dispName(c),subtitle(c));
  $('asg').style.display=(cur!==SYSK)?'block':'none';
}

function openChat(k){
  cur=k;
  const c=chats.get(k);if(c)c.unread=0;
  $('app').classList.add('open');
  $('newno').style.display='none';$('cname').style.display='block';$('csub').style.display='block';
  refreshHead();
  redrawChat(k);
  showPane(true);
  if(k===SYSK)$('f').style.display='none';
  toBottom();renderList();
  if(k!==SYSK)$('tx').focus();
}

function newChat(){
  cur='__new__';
  $('app').classList.add('open');
  setHead(null,'Pesan baru','');
  $('asg').style.display='none';
  $('newno').style.display='block';$('cname').style.display='none';$('csub').style.display='none';
  $('log').textContent='';lastDate='';
  showPane(true);renderList();$('newno').focus();
}

function normNo(n){
  let d=(n||'').replace(/[^0-9]/g,'');
  if(d.indexOf('0')===0)d='62'+d.slice(1);
  return d;
}

function pendBubble(k,text,file){
  const d=document.createElement('div');d.className='m out pend';
  if(file){const p=document.createElement('div');p.textContent=(isImg(file.name)?'\\uD83D\\uDCF7 ':'\\uD83D\\uDCC4 ')+file.name;d.appendChild(p);}
  if(text){const p=document.createElement('div');p.textContent=text;d.appendChild(p);}
  const t=document.createElement('div');t.className='t';
  const now=new Date();t.textContent=p2(now.getHours())+':'+p2(now.getMinutes())+' \\uD83D\\uDD53';
  d.appendChild(t);
  const o={chat:k,text:text,hasFile:!!file,el:d,tm:setTimeout(()=>{t.textContent=t.textContent.replace('\\uD83D\\uDD53','\\u26A0 belum terkirim');},120000)};
  pend.push(o);
  if(cur===k){$('log').appendChild(d);toBottom();}
}

async function poll(){
  try{
    const r=await fetch('/api/messages?after='+last);
    if(r.status===401){location='/login';return;}
    const j=await r.json();
    if(epoch!==null&&j.epoch!==epoch){location.reload();return;}
    epoch=j.epoch;
    admin=!!j.admin;IZ=new Set(j.izin||[]);
    $('me1').textContent=USER;$('me1').dataset.role=j.peran||'';
    $('rk').style.display=IZ.has('rekap')?'inline-flex':'none';
    $('adm').style.display=(IZ.has('rekap')||IZ.has('auto')||IZ.has('tema')||IZ.has('peran'))?'inline-flex':'none';
    $('nb').style.display=IZ.has('kirim')?'':'none';
    $('jl').style.display=IZ.has('jadwal')?'':'none';
    $('st').textContent=j.status;$('st').className=(j.status==='Terhubung')?'ok':'';
    const ok=JSON.stringify(j.owners||{});
    owners=j.owners||{};
    j.items.forEach(e=>{last=Math.max(last,e.id);addItem(e);});
    if(j.items.length||ok!==ownKey){ownKey=ok;renderList();refreshHead();}
    if(firstLoad)renderList();
    firstLoad=false;
  }catch(e){}
}

function td(t,cls){const c=document.createElement('td');c.textContent=t;if(cls)c.className=cls;return c;}
function th(t,cls){const c=document.createElement('th');c.textContent=t;if(cls)c.className=cls;return c;}
function fmtTime(t){return t?(t.slice(8,10)+'/'+t.slice(5,7)+'/'+t.slice(2,4)+' '+hhmm(t)):'-';}
function tabel(heads){
  const t=document.createElement('table');t.className='rt';
  const hd=document.createElement('tr');
  heads.forEach((h,i)=>hd.appendChild(th(h,(i>0&&i<5)?'n':'')));
  t.appendChild(hd);return t;
}

function addHistory(e){
  if(ids.has(e.id))return;
  ids.add(e.id);all.push(e);
  if(e.type==='SYS')return;
  const k=key(e);
  let c=chats.get(k);
  if(!c){c={k:k,last:0,time:'',snip:'',unread:0,name:'',number:'',group:false};chats.set(k,c);}
  if(e.name)c.name=e.name;
  if(e.number)c.number=e.number;
  if(e.group)c.group=true;
  if(e.id>c.last)c.last=e.id;
  if(!c.time||e.time>=c.time){c.time=e.time;c.snip=snipFull(e);}
}

async function openHistoryChat(k){
  try{
    const r=await fetch('/api/chat?chat='+encodeURIComponent(k));
    const j=await r.json();
    if(!j.ok){alert(j.error||'Gagal memuat chat');return;}
    j.items.forEach(addHistory);
  }catch(e){alert('Gagal terhubung ke server');return;}
  if(!chats.has(k))chats.set(k,{k:k,last:0,time:'',snip:'',unread:0,name:'',number:'',group:false});
  openChat(k);
}

function openRekap(){
  if(!admin)return;
  cur=null;
  $('app').classList.add('open');
  showPane(false);
  $('chead').style.display='flex';
  $('empty').style.display='none';$('rekap').style.display='block';
  $('newno').style.display='none';$('cname').style.display='block';$('csub').style.display='block';
  $('asg').style.display='none';
  setHead(null,'Rekap per Username','Khusus admin');
  renderList();
  loadRekap();
}

async function loadRekap(user){
  rekapUser=(user===undefined)?null:user;
  const q=new URLSearchParams();
  if($('rdari').value)q.set('dari',$('rdari').value);
  if($('rsampai').value)q.set('sampai',$('rsampai').value);
  if(rekapUser!==null)q.set('user',rekapUser);
  const b=$('rbody');b.textContent='Memuat...';
  try{
    const r=await fetch('/api/rekap?'+q.toString());
    const j=await r.json();
    if(!j.ok){b.textContent=j.error||'Gagal memuat rekap';return;}
    if(rekapUser===null)renderRekapUsers(j.rows);else renderRekapChats(j.rows,rekapUser);
  }catch(e){b.textContent='Gagal terhubung ke server';}
}

function renderRekapUsers(rows){
  const b=$('rbody');b.textContent='';
  if(!rows.length){b.textContent='Tidak ada data pada rentang tanggal ini.';return;}
  const t=tabel(['Username','Chat','Terkirim','Diterima','File/gambar terkirim','Aktivitas terakhir']);
  const tot={chats:0,out:0,inn:0,files:0};
  rows.forEach(r=>{
    const tr=document.createElement('tr');tr.className='rk';
    tr.appendChild(td(r.user||'(belum ditetapkan)'));
    tr.appendChild(td(r.chats,'n'));tr.appendChild(td(r.out,'n'));
    tr.appendChild(td(r.inn,'n'));tr.appendChild(td(r.files,'n'));
    tr.appendChild(td(fmtTime(r.last)));
    tr.onclick=()=>loadRekap(r.user);
    tot.chats+=r.chats;tot.out+=r.out;tot.inn+=r.inn;tot.files+=r.files;
    t.appendChild(tr);
  });
  const tr=document.createElement('tr');tr.className='tot';
  tr.appendChild(td('Total'));
  tr.appendChild(td(tot.chats,'n'));tr.appendChild(td(tot.out,'n'));
  tr.appendChild(td(tot.inn,'n'));tr.appendChild(td(tot.files,'n'));tr.appendChild(td(''));
  t.appendChild(tr);
  b.appendChild(t);
  const h=document.createElement('div');h.className='rhint';
  h.textContent='Klik username untuk melihat daftar chat-nya, lalu klik chat untuk membuka percakapan.';
  b.appendChild(h);
}

function renderRekapChats(rows,user){
  const b=$('rbody');b.textContent='';
  const bk=document.createElement('button');bk.className='rbk';bk.type='button';
  bk.textContent='\\u2190 Semua username';bk.onclick=()=>loadRekap();
  b.appendChild(bk);
  const ttl=document.createElement('div');ttl.style.cssText='margin:12px 0;font-weight:600';
  ttl.textContent='Chat milik '+(user||'(belum ditetapkan)')+' \\u00B7 '+rows.length+' chat';
  b.appendChild(ttl);
  if(!rows.length){b.appendChild(document.createTextNode('Tidak ada chat pada rentang tanggal ini.'));return;}
  const t=tabel(['Chat','Masuk','Keluar','File/gambar','Terakhir','Pesan terakhir']);
  rows.forEach(r=>{
    const tr=document.createElement('tr');tr.className='rk';
    const c={k:r.chat,name:r.name,number:r.number,group:r.group};
    let nm=dispName(c);const sb=subtitleNoOwner(c);
    tr.appendChild(td(sb?nm+' ('+sb+')':nm));
    tr.appendChild(td(r.inn,'n'));tr.appendChild(td(r.out,'n'));tr.appendChild(td(r.files,'n'));
    tr.appendChild(td(fmtTime(r.last)));
    tr.appendChild(td(r.snip||''));
    tr.onclick=()=>openHistoryChat(r.chat);
    t.appendChild(tr);
  });
  b.appendChild(t);
}

function subtitleNoOwner(c){
  const n=c.number||(digitsOnly(c.k)?c.k:'');
  if(n&&dispName(c)!==fmtNo(n))return fmtNo(n);
  return '';
}

const STAT={menunggu:'Menunggu',diproses:'Mengirim...',terkirim:'Terkirim',gagal:'Gagal',terlewat:'Terlewat',selesai:'Selesai'};
const ULANG={sekali:'Sekali',harian:'Harian',mingguan:'Mingguan',bulanan:'Bulanan'};

function bukaJadwal(){
  if(!cur||cur===SYSK){alert('Buka sebuah chat dulu, tulis pesannya, lalu klik jam.');return;}
  const text=$('tx').value.trim(), file=$('im').files[0];
  if(!text&&!file){alert('Tulis pesan atau pilih gambar/file dulu, lalu klik jam.');return;}
  let tujuan;
  if(cur==='__new__'){
    const n=normNo($('newno').value);
    if(n.length<8||n.length>15){alert('Isi nomor tujuan dulu.');return;}
    tujuan=fmtNo(n);
  }else tujuan=dispName(chats.get(cur));
  $('s_tujuan').textContent='Tujuan: '+tujuan;
  const baris=file?((isImg(file.name)?'📷 ':'📄 ')+file.name+String.fromCharCode(10)):'';
  $('s_isi').textContent=baris+text;
  const d=new Date(Date.now()+10*60000);
  $('s_tgl').value=ymd(d);$('s_jam').value=p2(d.getHours())+':'+p2(d.getMinutes());
  $('s_ulang').value='sekali';$('s_sampai').value='';$('s_sw').style.display='none';
  $('smodal').style.display='flex';
}

async function simpanJadwal(){
  const text=$('tx').value.trim(), file=$('im').files[0];
  const data={tanggal:$('s_tgl').value,jam:$('s_jam').value,ulang:$('s_ulang').value,sampai:$('s_sampai').value,text:text};
  if(cur==='__new__')data.tujuan_no=$('newno').value;else data.tujuan_chat=cur;
  const fd=new FormData();fd.append('data',JSON.stringify(data));
  if(file)fd.append('lampiran',file);
  const bt=$('s_simpan');bt.disabled=true;
  try{
    const r=await fetch('/api/jadwal',{method:'POST',body:fd});const j=await r.json();
    if(!j.ok){alert(j.error||'Gagal menjadwalkan');bt.disabled=false;return;}
    $('smodal').style.display='none';
    $('tx').value='';$('im').value='';$('chip').style.display='none';
    showSys('Pesan dijadwalkan pada '+$('s_tgl').value+' '+$('s_jam').value+(data.ulang!=='sekali'?' ('+ULANG[data.ulang].toLowerCase()+')':''));
  }catch(e){alert('Gagal terhubung ke server');}
  bt.disabled=false;
}

async function bukaDaftar(){
  $('lmodal').style.display='flex';
  const b=$('lbody');b.textContent='Memuat...';
  try{
    const r=await fetch('/api/jadwal');const j=await r.json();
    b.textContent='';
    if(!j.items.length){b.textContent='Belum ada pesan terjadwal.';return;}
    const t=document.createElement('table');t.className='jt';
    const hd=document.createElement('tr');
    ['Waktu','Tujuan','Pesan','Ulang','Status',''].concat(j.admin?['Oleh']:[]).forEach(x=>{
      const th=document.createElement('th');th.textContent=x;hd.appendChild(th);});
    t.appendChild(hd);
    j.items.forEach(it=>{
      const tr=document.createElement('tr');
      const w=it.waktu;
      const pesan=(it.lampiran?((it.lampiran.gambar?'📷 ':'📄 ')+it.lampiran.o+' '):'')+(it.text||'');
      const st=STAT[it.status]||it.status;
      const cells=[w.slice(8,10)+'/'+w.slice(5,7)+' '+w.slice(11,16),it.label||it.no||it.chat,
        pesan.length>60?pesan.slice(0,60)+'...':pesan,
        ULANG[it.ulang]+(it.sampai?' s/d '+it.sampai:''),st];
      cells.forEach((x,i)=>{
        const td=document.createElement('td');td.textContent=x;
        if(i===4&&it.hasil)td.title=it.hasil;
        tr.appendChild(td);
      });
      const tdb=document.createElement('td');
      const bb=document.createElement('button');bb.textContent=it.status==='menunggu'?'Batalkan':'Hapus';
      bb.onclick=async()=>{
        const rr=await fetch('/api/jadwal/batal',{method:'POST',headers:{'Content-Type':'application/json'},body:JSON.stringify({id:it.id})});
        const jj=await rr.json();if(!jj.ok)alert(jj.error||'Gagal');bukaDaftar();
      };
      tdb.appendChild(bb);tr.appendChild(tdb);
      if(j.admin){const td=document.createElement('td');td.textContent=it.user;tr.appendChild(td);}
      t.appendChild(tr);
    });
    b.appendChild(t);
    const h=document.createElement('div');h.style.cssText='color:#667781;font-size:12px;margin-top:8px';
    h.textContent='Pesan dikirim saat server berjalan. Jika server mati lebih dari 1 jam dari waktu kirim, jadwal itu dilewati.';
    b.appendChild(h);
  }catch(e){b.textContent='Gagal memuat daftar.';}
}
async function openAssign(){
  if(!cur||cur===SYSK||cur==='__new__')return;
  if(!users.length){
    try{
      const r=await fetch('/api/users');const j=await r.json();
      if(j.ok)users=j.users;else{alert(j.error||'Gagal memuat daftar user');return;}
    }catch(e){alert('Gagal memuat daftar user');return;}
  }
  const sel=$('msel');sel.textContent='';
  if(admin){const o0=document.createElement('option');o0.value='';o0.textContent='(belum ditetapkan - hanya admin)';sel.appendChild(o0);}
  users.filter(u=>admin||u!==USER).forEach(u=>{
    const o=document.createElement('option');o.value=u;o.textContent=u+(u===USER?' (saya)':'');sel.appendChild(o);
  });
  sel.value=admin?(owners[cur]||''):(sel.options[0]?sel.options[0].value:'');
  $('mnote').value='';
  $('mchat').textContent=dispName(chats.get(cur));
  $('modal').style.display='flex';
}
async function saveAssign(){
  if(!admin&&!$('msel').value){alert('Pilih user tujuan');return;}
  try{
    const r=await fetch('/api/transfer',{method:'POST',headers:{'Content-Type':'application/json'},
      body:JSON.stringify({chat:cur,to:$('msel').value,note:$('mnote').value})});
    const j=await r.json();
    if(!j.ok){alert(j.error||'Gagal');return;}
    $('modal').style.display='none';
    location.reload();
  }catch(e){alert('Gagal terhubung ke server');}
}

$('me1').textContent=USER;
{const mc={k:USER,name:USER,number:'',group:false};const a=avatar(mc);$('meav').textContent=a.textContent;$('meav').style.background=a.style.background;}
$('flt').addEventListener('input',renderList);
$('nb').addEventListener('click',newChat);
$('asg').addEventListener('click',openAssign);
$('sch').addEventListener('click',bukaJadwal);
$('jl').addEventListener('click',bukaDaftar);
$('s_batal').addEventListener('click',()=>{$('smodal').style.display='none';});
$('s_simpan').addEventListener('click',simpanJadwal);
$('l_tutup').addEventListener('click',()=>{$('lmodal').style.display='none';});
$('s_ulang').addEventListener('change',()=>{$('s_sw').style.display=$('s_ulang').value==='sekali'?'none':'block';});
$('rk').addEventListener('click',openRekap);
$('rgo').addEventListener('click',()=>loadRekap(rekapUser===null?undefined:rekapUser));
$('mcancel').addEventListener('click',()=>{$('modal').style.display='none';});
$('msave').addEventListener('click',saveAssign);
$('back').addEventListener('click',()=>{$('app').classList.remove('open');cur=null;showPane(false);renderList();});
$('im').addEventListener('change',()=>{
  const f=$('im').files[0];
  if(f&&f.size>MAXMB*1024*1024){alert('Ukuran file maksimal '+MAXMB+' MB');$('im').value='';return;}
  $('chip').style.display=f?'flex':'none';
  $('chipn').textContent=f?((isImg(f.name)?'\\uD83D\\uDCF7 ':'\\uD83D\\uDCC4 ')+f.name):'';
});
$('chipx').addEventListener('click',()=>{$('im').value='';$('chip').style.display='none';});
$('tx').addEventListener('keydown',ev=>{
  if(ev.key==='Enter'&&!ev.shiftKey){ev.preventDefault();$('f').requestSubmit();}
});

$('f').addEventListener('submit',async ev=>{
  ev.preventDefault();
  if(!cur||cur===SYSK)return;
  const text=$('tx').value.trim();
  const file=$('im').files[0];
  if(!text&&!file)return;
  const fd=new FormData();
  let target=cur;
  if(cur==='__new__'){
    const n=normNo($('newno').value);
    if(n.length<8||n.length>15){alert('Nomor tidak valid');return;}
    fd.append('no',n);target=n;
  }else{fd.append('chat',cur);}
  fd.append('text',text);
  if(file)fd.append('file',file);
  const bt=$('bt');bt.disabled=true;
  try{
    const r=await fetch('/api/send',{method:'POST',body:fd});
    const j=await r.json();
    if(j.ok){
      $('tx').value='';$('im').value='';$('chip').style.display='none';
      if(cur==='__new__'){
        if(!chats.has(target))chats.set(target,{k:target,last:last+0.5,time:'',snip:'',unread:0,name:'',number:target,group:false});
        pendBubble(target,text,file);openChat(target);
      }else{pendBubble(target,text,file);}
    }else alert(j.error||'Gagal');
  }catch(e){alert('Gagal terhubung ke server');}
  bt.disabled=false;
});

poll();setInterval(poll,2500);
</script></body></html>"""


ADMIN_HTML = """<!doctype html><html lang="id"><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1"><title>Admin - __NAMA__</title>__ICON__
<style>
:root{--brand:#00a884;--brand-dark:#128c7e;--accent:#25d366;--out-bg:#d9fdd3;--in-bg:#ffffff;--chat-bg:#efeae2;--surface:#ffffff;--panel:#f0f2f5;--page-bg:#d1d7db;--text:#111b21;--muted:#667781;--border:#e4e8eb;--hover:#f5f6f6;--on-brand:#ffffff;--on-header:#ffffff;--radius:8px;--font:system-ui,-apple-system,"Segoe UI",Roboto,Arial,sans-serif;--fsm:1;--shadow:0 1px 2px rgba(11,20,26,.16)}
*{box-sizing:border-box}
body{margin:0;font-family:var(--font);background:var(--page-bg);color:var(--text);height:100vh;display:flex;flex-direction:column;font-size:14px}
button,input,select,textarea{font-family:inherit;font-size:inherit}
::-webkit-scrollbar{width:8px;height:8px}::-webkit-scrollbar-thumb{background:var(--border);border-radius:8px}
header{background:linear-gradient(135deg,var(--brand-dark),var(--brand));color:var(--on-header);padding:10px 22px;display:flex;gap:16px;align-items:center;flex-wrap:wrap;box-shadow:0 2px 10px rgba(0,0,0,.22);position:relative;z-index:3}
.hb{display:flex;align-items:center;gap:11px;font-weight:700;font-size:16px}
.hb img{width:36px;height:36px;border-radius:9px;object-fit:contain;background:rgba(255,255,255,.94);padding:2px}
.hb small{display:block;font-weight:400;font-size:11.5px;opacity:.85}
header a{color:inherit;text-decoration:none;background:rgba(255,255,255,.16);padding:6px 14px;border-radius:999px;transition:background .15s}
header a:hover{background:rgba(255,255,255,.28)}
.tabs{display:flex;gap:6px;flex-wrap:wrap}
.tabs button{border:0;background:rgba(255,255,255,.14);color:inherit;padding:8px 18px;border-radius:999px;cursor:pointer;transition:background .15s}
.tabs button:hover{background:rgba(255,255,255,.26)}
.tabs button.on{background:var(--surface);color:var(--brand-dark);font-weight:600}
.flt{display:flex;gap:8px;align-items:center;margin-left:auto}
.flt input{padding:6px 9px;border:0;border-radius:8px;background:var(--surface);color:var(--text)}
.flt button{padding:7px 16px;border:0;border-radius:8px;background:var(--surface);color:var(--brand-dark);cursor:pointer;font-weight:600}
#wrap{flex:1;min-height:0;display:flex}
.pane{background:var(--surface);overflow-y:auto;border-right:1px solid var(--border)}
#pu{width:240px;flex:none}#pn{width:320px;flex:none}
#pc{flex:1;min-width:0;display:flex;flex-direction:column;background-color:var(--chat-bg)}
.ph{padding:11px 14px;background:var(--panel);font-weight:600;border-bottom:1px solid var(--border);display:flex;gap:8px;align-items:center}
.ph a,.ph button{font-weight:400;font-size:12px;padding:5px 11px;border-radius:999px;border:1px solid var(--border);background:var(--surface);color:var(--text);text-decoration:none;cursor:pointer}
.ph a:hover,.ph button:hover{border-color:var(--brand);color:var(--brand)}
.it{padding:11px 14px;border-bottom:1px solid var(--border);cursor:pointer;transition:background .12s;border-left:3px solid transparent}
.it:hover{background:var(--hover)}.it.on{background:var(--panel);border-left-color:var(--brand)}
.it .a{font-weight:600;white-space:nowrap;overflow:hidden;text-overflow:ellipsis}
.it .b{font-size:12px;color:var(--muted);margin-top:2px;white-space:nowrap;overflow:hidden;text-overflow:ellipsis}
.emp{padding:28px 20px;color:var(--muted);text-align:center}
#cv{flex:1;overflow-y:auto;padding:16px 6%;display:flex;flex-direction:column;gap:3px}
.dsep{align-self:center;background:var(--surface);color:var(--muted);font-size:12px;padding:4px 14px;border-radius:999px;margin:10px 0;box-shadow:var(--shadow)}
.m{max-width:70%;padding:7px 10px 5px 11px;box-shadow:var(--shadow);word-wrap:break-word;white-space:pre-wrap;border-radius:var(--radius);line-height:1.4;color:var(--text)}
.in{background:var(--in-bg);align-self:flex-start;border-top-left-radius:0}
.out{background:var(--out-bg);align-self:flex-end;border-top-right-radius:0}
.note{background:#fff3cd;color:#664d03;align-self:center;font-size:13px}
.w{font-size:12.5px;font-weight:600;margin-bottom:2px}
.t{font-size:11px;color:var(--muted);text-align:right;margin-top:2px}
.m img{max-width:280px;max-height:300px;border-radius:calc(var(--radius) - 2px);display:block;margin:2px 0 4px}
.fc{display:flex;gap:10px;align-items:center;background:rgba(127,127,127,.12);border-radius:var(--radius);padding:8px 10px;margin:2px 0 4px;color:inherit;text-decoration:none;word-break:break-all}
#lap,#auto,#tema,#peran{display:none;flex:1;overflow:auto;padding:22px 26px}
.cards{display:flex;gap:14px;flex-wrap:wrap;margin-bottom:18px}
.card{background:var(--surface);border-radius:14px;padding:16px 22px;box-shadow:var(--shadow);min-width:150px;border-top:4px solid var(--brand)}
.card b{display:block;font-size:28px;color:var(--brand)}.card span{color:var(--muted);font-size:12.5px}
h3{margin:24px 0 10px;font-size:17px}
table{width:100%;border-collapse:collapse;background:var(--surface);box-shadow:var(--shadow);border-radius:12px;overflow:hidden}
th{background:var(--panel);text-align:left;padding:10px 12px;color:var(--muted);font-size:12.5px}
td{padding:10px 12px;border-top:1px solid var(--border)}
tr:hover td{background:var(--hover)}
td.n,th.n{text-align:right}
.tools{display:flex;gap:8px;margin-bottom:12px}
.tools a,.tools button,.bar button{padding:9px 18px;border-radius:10px;border:0;background:var(--brand);color:var(--on-brand);cursor:pointer;text-decoration:none;font-weight:600}
#ptitle{display:none}
.hint{color:var(--muted);font-size:12.5px;margin-bottom:12px}
.rule{background:var(--surface);border-radius:14px;padding:14px 18px;margin-bottom:12px;box-shadow:var(--shadow);border-left:4px solid var(--brand)}
.rule.off{opacity:.55;border-left-color:var(--muted)}
.rule h4{margin:0 0 6px;display:flex;gap:8px;align-items:center;flex-wrap:wrap}
.bd{font-size:11px;font-weight:500;background:var(--panel);color:var(--brand);padding:3px 10px;border-radius:999px}
.rule .rb{color:var(--muted);font-size:13px;margin:3px 0;white-space:pre-wrap}
.rule .ra{display:flex;gap:6px;margin-top:10px;align-items:center;flex-wrap:wrap}
.rule .ra button{padding:6px 12px;border:1px solid var(--border);background:var(--surface);color:var(--text);border-radius:8px;cursor:pointer}
.rule .ra button:hover{border-color:var(--brand);color:var(--brand)}
.bar{display:flex;gap:14px;align-items:center;margin-bottom:12px;flex-wrap:wrap}
#rm{display:none;position:fixed;inset:0;background:rgba(11,20,26,.5);align-items:center;justify-content:center;z-index:9;backdrop-filter:blur(2px)}
.rbox{background:var(--surface);color:var(--text);border-radius:16px;padding:24px;width:520px;max-width:94vw;max-height:92vh;overflow:auto;box-shadow:0 20px 50px rgba(0,0,0,.35)}
.rbox label{display:block;margin:12px 0 4px;font-weight:600;font-size:13px}
.rbox input[type=text],.rbox input[type=time],.rbox input[type=number],.rbox select,.rbox textarea{width:100%;padding:9px 11px;border:1px solid var(--border);border-radius:10px;background:var(--surface);color:var(--text)}
.rbox .r{display:flex;gap:8px;justify-content:flex-end;margin-top:16px}
.rbox .r button{padding:9px 18px;border:1px solid var(--border);border-radius:10px;cursor:pointer;background:var(--surface);color:var(--text)}
.hr{display:flex;gap:10px;flex-wrap:wrap;font-size:13px;font-weight:400}

/* ---- editor tampilan ---- */
.tm{display:grid;grid-template-columns:minmax(0,1.15fr) minmax(0,.85fr);gap:22px;align-items:start}
.tm-box{background:var(--surface);border-radius:14px;padding:6px 22px 22px;box-shadow:var(--shadow)}
.tm-box h3:first-child{margin-top:16px}
.tm label{display:block;font-size:13px;font-weight:600;margin:12px 0 5px}
.tm input[type=text],.tm select{width:100%;padding:9px 11px;border:1px solid var(--border);border-radius:10px;background:var(--surface);color:var(--text)}
.tm input[type=range]{width:100%}
.presets{display:grid;grid-template-columns:repeat(auto-fill,minmax(130px,1fr));gap:10px}
.preset{border:2px solid var(--border);border-radius:12px;padding:10px;cursor:pointer;transition:border-color .15s,transform .1s;background:var(--surface)}
.preset:hover{transform:translateY(-1px)}.preset.on{border-color:var(--brand);box-shadow:0 0 0 3px rgba(127,127,127,.15)}
.preset .sw{display:flex;height:22px;border-radius:6px;overflow:hidden;margin-bottom:7px}
.preset .sw i{flex:1}.preset span{font-size:12.5px;font-weight:600}
.cols{display:grid;grid-template-columns:repeat(3,minmax(0,1fr));gap:10px}
.cols label{margin:8px 0 0;font-weight:500;font-size:12.5px;color:var(--muted)}
.cols input[type=color]{width:100%;height:38px;border:1px solid var(--border);border-radius:8px;padding:2px;background:var(--surface);cursor:pointer;margin-top:4px}
.chk{display:flex!important;align-items:center;gap:8px;font-weight:500!important}
.imgbox{border:1px dashed var(--border);border-radius:12px;padding:12px;margin-top:10px;display:flex;gap:14px;align-items:center}
.imgbox .th{width:96px;height:72px;border-radius:8px;background:var(--panel) center/contain no-repeat;border:1px solid var(--border);flex:none}
.imgbox .in2{flex:1;min-width:0}.imgbox b{display:block;margin-bottom:2px}.imgbox small{color:var(--muted);display:block;margin-bottom:6px}
.imgbox input[type=file]{max-width:100%;font-size:12.5px}
.tm-act{display:flex;gap:10px;margin-top:20px;flex-wrap:wrap}
.tm-act button{padding:10px 22px;border-radius:10px;border:0;background:var(--brand);color:var(--on-brand);font-weight:600;cursor:pointer}
.tm-act button.gh{background:var(--surface);color:var(--text);border:1px solid var(--border);font-weight:500}
.pv{border-radius:14px;overflow:hidden;box-shadow:var(--shadow);background:var(--surface);margin-bottom:16px;border:1px solid var(--border)}
.pv-top{display:flex;align-items:center;gap:10px;padding:11px 14px;background:linear-gradient(135deg,var(--brand-dark),var(--brand));color:var(--on-header)}
.pv-top img{width:30px;height:30px;border-radius:8px;object-fit:contain;background:rgba(255,255,255,.94);padding:2px}
.pv-top b{display:block;font-size:14px}.pv-top small{font-size:11px;opacity:.85}
.pv-body{padding:14px;display:flex;flex-direction:column;gap:6px;background-color:var(--chat-bg);background-size:cover;background-position:center;min-height:170px}
.pv-m{max-width:78%;padding:6px 10px;font-size:calc(13px * var(--fsm));border-radius:var(--radius);box-shadow:var(--shadow);color:var(--text)}
.pv-m.in{background:var(--in-bg);border-top-left-radius:0;align-self:flex-start}
.pv-m.out{background:var(--out-bg);border-top-right-radius:0;align-self:flex-end}
.pv-bar{display:flex;gap:8px;padding:9px 12px;background:var(--panel);align-items:center}
.pv-bar span{flex:1;background:var(--surface);color:var(--muted);padding:8px 14px;border-radius:999px;font-size:12.5px}
.pv-bar i{width:32px;height:32px;border-radius:50%;background:var(--brand);display:block}
.pv-login{height:160px;display:flex;flex-direction:column;justify-content:center;padding:20px 24px;color:var(--on-header);background:linear-gradient(135deg,var(--brand-dark),var(--brand)) center/cover}
.pv-login b{font-size:19px}.pv-login small{opacity:.9;margin-top:4px}
.pv-login img{max-height:44px;max-width:130px;object-fit:contain;margin-bottom:10px;align-self:flex-start;background:rgba(255,255,255,.94);padding:4px 8px;border-radius:8px}
@media print{
 header,.tools,#pu,#pn,.ph a,.ph button{display:none !important}
 body{height:auto;background:#fff}#wrap,#pc,#cv,#lap{display:block !important;overflow:visible !important;height:auto !important}
 #ptitle{display:block;font-size:18px;font-weight:700;margin-bottom:10px}
}
@media(max-width:900px){#wrap{flex-direction:column}#pu,#pn{width:100%;max-height:30vh}.tm{grid-template-columns:1fr}}
</style>
<link rel="stylesheet" href="/tema.css?v=__VER__">
</head><body>
<header><div class="hb">__LOGO__<div>__NAMA__<small>Rekap, laporan &amp; pengaturan (Admin)</small></div></div>
 <span class="tabs"><button id="t1" class="on">Rekap Percakapan</button> <button id="t2">Laporan</button> <button id="t3">Balasan Otomatis</button> <button id="t4">Tampilan</button> <button id="t5">Peran &amp; Izin</button></span>
 <span class="flt">Dari <input type="date" id="dari"> Sampai <input type="date" id="sampai"> <button id="go">Terapkan</button></span>
 <a href="/">&larr; Kembali ke Chat</a> <span>__USER__</span></header>
<div id="wrap">
 <div class="pane" id="pu"><div class="emp">Memuat...</div></div>
 <div class="pane" id="pn"><div class="emp">Pilih username di kiri</div></div>
 <div id="pc">
  <div class="ph"><span id="chn" style="flex:1">Percakapan</span>
   <a id="dl" href="#" style="display:none">&#11015; Transkrip HTML</a>
   <button id="pr" style="display:none">&#128424; Cetak</button></div>
  <div id="cv"><div class="emp">Pilih nomor/chat untuk melihat percakapan</div></div>
 </div>
</div>
<div id="lap"></div>
<div id="auto"></div>
<div id="peran"></div>
<div id="tema"><div class="tm">
 <div class="tm-box">
  <h3>Identitas aplikasi</h3>
  <label>Nama aplikasi</label><input type="text" id="tm_nama" maxlength="60">
  <label>Tagline (kalimat pendek di halaman login)</label><input type="text" id="tm_tag" maxlength="120">
  <h3>Tema warna</h3>
  <div id="tm_presets" class="presets"></div>
  <div class="cols">
   <label>Warna utama<input type="color" id="tm_brand"></label>
   <label>Warna header<input type="color" id="tm_brand_dark"></label>
   <label>Warna aksen<input type="color" id="tm_aksen"></label>
   <label>Gelembung keluar<input type="color" id="tm_out"></label>
   <label>Gelembung masuk<input type="color" id="tm_in"></label>
   <label>Latar percakapan<input type="color" id="tm_chat"></label>
  </div>
  <label class="chk"><input type="checkbox" id="tm_gelap"> Mode gelap (latar, panel, dan teks)</label>
  <h3>Huruf dan bentuk</h3>
  <label>Jenis huruf</label><select id="tm_font"></select>
  <label>Ukuran teks</label><select id="tm_ukuran"><option value="kecil">Kecil</option><option value="normal">Normal</option><option value="besar">Besar</option></select>
  <label>Kebulatan sudut: <b id="tm_rv">8</b> px</label><input type="range" id="tm_radius" min="0" max="20">
  <h3>Gambar</h3>
  <div class="imgbox"><div class="th" id="th_logo"></div><div class="in2"><b>Logo</b><small>PNG, JPG, WEBP, atau GIF, maksimal 2 MB. Tampil di halaman login, kepala menu, dan ikon tab browser. Latar transparan paling baik.</small><input type="file" id="tm_logo" accept="image/png,image/jpeg,image/webp,image/gif"><label class="chk"><input type="checkbox" id="del_logo"> Hapus logo</label></div></div>
  <div class="imgbox"><div class="th" id="th_login_bg"></div><div class="in2"><b>Gambar latar halaman login</b><small>Maksimal 5 MB. Disarankan foto mendatar (minimal 1280 px) yang tidak terlalu ramai.</small><input type="file" id="tm_login_bg" accept="image/png,image/jpeg,image/webp,image/gif"><label class="chk"><input type="checkbox" id="del_login_bg"> Hapus gambar latar</label></div></div>
  <div class="imgbox"><div class="th" id="th_wallpaper"></div><div class="in2"><b>Wallpaper percakapan</b><small>Maksimal 5 MB. Tampil di belakang gelembung chat.</small><input type="file" id="tm_wallpaper" accept="image/png,image/jpeg,image/webp,image/gif"><label class="chk"><input type="checkbox" id="del_wallpaper"> Hapus wallpaper</label>
   <label>Kejelasan gambar: <b id="tm_wv">60</b>%</label><input type="range" id="tm_wallvis" min="0" max="100"></div></div>
  <div class="tm-act"><button id="tm_simpan" type="button">Simpan tampilan</button><button id="tm_reset" type="button" class="gh">Kembalikan ke bawaan</button></div>
 </div>
 <div>
  <div class="pv"><div class="pv-top"><img id="pv_logo" hidden alt=""><div><b id="pv_nama"></b><small id="pv_tag"></small></div></div>
   <div class="pv-body" id="pv_body"><div class="pv-m in">Selamat pagi, ada yang bisa kami bantu?</div><div class="pv-m out">Saya ingin menanyakan jadwal layanan.</div><div class="pv-m in">Layanan dibuka Senin sampai Jumat pukul 08.00-15.00.</div></div>
   <div class="pv-bar"><span>Ketik pesan</span><i></i></div></div>
  <div class="pv pv-login" id="pv_login"><img id="pv_logo2" hidden alt=""><b id="pv_nama2"></b><small id="pv_tag2"></small></div>
  <div class="hint">Pratinjau memperbarui tampilan halaman ini seketika. Perubahan baru berlaku untuk semua pengguna setelah menekan Simpan.</div>
 </div>
</div></div>
<div id="rm"><div class="rbox">
 <h3 id="rmt" style="margin:0">Aturan balasan</h3>
 <label>Nama aturan</label><input type="text" id="f_nama" maxlength="60">
 <label style="font-weight:400"><input type="checkbox" id="f_aktif" checked> Aktif</label>
 <label>Pemicu</label><select id="f_pemicu"><option value="kata_kunci">Kata kunci ada di pesan</option><option value="pertama">Pesan pertama dari kontak baru</option><option value="semua">Semua pesan (cadangan)</option></select>
 <div id="f_kata_w"><label>Kata kunci (pisahkan dengan koma atau baris baru)</label><textarea id="f_kata" rows="2"></textarea></div>
 <label>Jadwal aturan</label><select id="f_jadwal"><option value="selalu">Sepanjang waktu</option><option value="dalam">Hanya pada jam tertentu</option><option value="luar">Hanya di luar jam tertentu</option></select>
 <div id="f_jam_w" style="display:none">
  <div class="hr" style="margin-top:6px">Mulai <input type="time" id="f_mulai" value="08:00" style="width:auto"> Selesai <input type="time" id="f_selesai" value="16:00" style="width:auto"></div>
  <div class="hr" style="margin-top:8px">Hari (kosong = semua):
   <label style="font-weight:400;margin:0"><input type="checkbox" class="f_h" value="0"> Sen</label>
   <label style="font-weight:400;margin:0"><input type="checkbox" class="f_h" value="1"> Sel</label>
   <label style="font-weight:400;margin:0"><input type="checkbox" class="f_h" value="2"> Rab</label>
   <label style="font-weight:400;margin:0"><input type="checkbox" class="f_h" value="3"> Kam</label>
   <label style="font-weight:400;margin:0"><input type="checkbox" class="f_h" value="4"> Jum</label>
   <label style="font-weight:400;margin:0"><input type="checkbox" class="f_h" value="5"> Sab</label>
   <label style="font-weight:400;margin:0"><input type="checkbox" class="f_h" value="6"> Min</label></div>
 </div>
 <label>Teks balasan (boleh {nama} {nomor} {jam} {tanggal})</label><textarea id="f_teks" rows="4"></textarea>
 <label>Lampiran gambar / file (opsional)</label><input type="file" id="f_file" accept=".jpg,.jpeg,.png,.webp,.gif,.pdf,.doc,.docx,.xls,.xlsx,.ppt,.pptx,.txt,.csv,.zip,.rar,.7z">
 <div id="f_lamp" style="font-size:13px;color:var(--muted);margin-top:4px"></div>
 <label id="f_hapusw" style="font-weight:400;display:none"><input type="checkbox" id="f_hapusl"> Hapus lampiran saat ini</label>
 <div class="hr" style="margin-top:10px">Jeda sebelum membalas (detik) <input type="number" id="f_jeda" min="0" max="120" value="3" style="width:80px">
  Jangan balas kontak yang sama lagi selama (menit) <input type="number" id="f_cd" min="0" max="10080" value="60" style="width:90px"></div>
 <div class="r"><button id="f_batal" type="button">Batal</button><button id="f_simpan" type="button" style="background:var(--brand);color:var(--on-brand);border-color:transparent">Simpan</button></div>
</div></div>
<script>
const $=id=>document.getElementById(id);
let tab='rekap', selUser=null, selChat=null;
const BADN=/info kontak|contact info|click here|klik di sini/i;
function numLike(s){return /^[+0-9 -]+$/.test(s||'');}
function digitsOnly(s){return /^[0-9]{8,15}$/.test(s||'');}
function fmtNo(n){
  if(!n)return '';
  if(n.indexOf('62')===0)return '+62 '+n.slice(2).replace(/^([0-9]{3})([0-9]{3,4})([0-9]+)$/,'$1-$2-$3');
  return '+'+n;
}
function nm(name,number,k){
  if(name&&!numLike(name)&&!BADN.test(name))return name;
  const n=number||(digitsOnly(k)?k:'');
  if(n)return fmtNo(n);
  return BADN.test(name||k||'')?'Chat lama':(name||k||'');
}
function colorOf(s){let h=0;for(let i=0;i<s.length;i++)h=(h*31+s.charCodeAt(i))%360;return 'hsl('+h+',45%,38%)';}
function hhmm(t){return (t||'').slice(11,16);}
function tgl(t){return t?(t.slice(8,10)+'/'+t.slice(5,7)+'/'+t.slice(0,4)):'-';}
function tglw(t){return t?(tgl(t)+' '+hhmm(t)):'-';}
function qs(){
  const p=new URLSearchParams();
  if($('dari').value)p.set('dari',$('dari').value);
  if($('sampai').value)p.set('sampai',$('sampai').value);
  return p.toString();
}
function el(tag,cls,text){const e=document.createElement(tag);if(cls)e.className=cls;if(text!==undefined)e.textContent=text;return e;}
function item(a,b,onclick){
  const d=el('div','it');d.appendChild(el('div','a',a));d.appendChild(el('div','b',b));
  d.onclick=()=>{[...d.parentNode.children].forEach(c=>c.classList.remove('on'));d.classList.add('on');onclick();};
  return d;
}

async function getJson(u){
  const r=await fetch(u);
  if(r.status===401){location='/login';throw new Error('login');}
  if(r.status===403){location='/';throw new Error('akses');}
  return r.json();
}

async function loadUsers(){
  const box=$('pu');box.textContent='Memuat...';
  const j=await getJson('/api/rekap?'+qs());
  box.textContent='';
  if(!j.rows.length){box.appendChild(el('div','emp','Tidak ada data.'));return;}
  j.rows.forEach(r=>{
    box.appendChild(item('\\uD83D\\uDC64 '+(r.user||'(belum ditetapkan)'),
      r.chats+' chat \\u00B7 '+r.out+' kirim \\u00B7 '+r.inn+' terima',()=>loadChats(r.user)));
  });
}

async function loadChats(u){
  selUser=u;
  const box=$('pn');box.textContent='Memuat...';
  const j=await getJson('/api/rekap?user='+encodeURIComponent(u)+'&'+qs());
  box.textContent='';
  const ph=el('div','ph');ph.appendChild(el('span',null,(u||'(belum ditetapkan)')));
  ph.lastChild.style.flex='1';
  const a=el('a',null,'\\u2B07 Semua chat');a.href='/admin/transkrip?user='+encodeURIComponent(u)+'&'+qs();
  ph.appendChild(a);box.appendChild(ph);
  if(!j.rows.length){box.appendChild(el('div','emp','Tidak ada chat pada rentang ini.'));return;}
  j.rows.forEach(r=>{
    const name=nm(r.name,r.number,r.chat);
    const no=r.number||(digitsOnly(r.chat)?r.chat:'');
    const sub=(no&&fmtNo(no)!==name?fmtNo(no)+' \\u00B7 ':'')+r.inn+' masuk \\u00B7 '+r.out+' keluar';
    box.appendChild(item((r.group?'\\uD83D\\uDC65 ':'')+name,sub,()=>openConv(r.chat,name,no,u)));
  });
}

function inRange(e){
  const d=(e.time||'').slice(0,10);
  return (!$('dari').value||d>=$('dari').value)&&(!$('sampai').value||d<=$('sampai').value);
}

async function openConv(chat,name,no,owner){
  selChat=chat;
  $('chn').textContent=name+(no&&fmtNo(no)!==name?'  ('+fmtNo(no)+')':'')+(owner?'  \\u00B7 pemilik: '+owner:'');
  const cv=$('cv');cv.textContent='Memuat...';
  const j=await getJson('/api/chat?chat='+encodeURIComponent(chat));
  cv.textContent='';
  const items=j.items.filter(inRange);
  if(!items.length){cv.appendChild(el('div','emp','Tidak ada pesan pada rentang tanggal ini.'));}
  let last='';
  items.forEach(e=>{
    const ds=(e.time||'').slice(0,10);
    if(ds!==last){last=ds;cv.appendChild(el('div','dsep',tgl(ds)));}
    const d=el('div','m '+(e.type==='IN'?'in':e.type==='OUT'?'out':'note'));
    if(e.type==='IN'&&e.sender){const w=el('div','w',e.sender);w.style.color=colorOf(e.sender);d.appendChild(w);}
    if(e.type==='OUT'&&e.user){const w=el('div','w',e.auto?('🤖 '+e.auto):((e.terjadwal?'⏰ ':'')+'\\u2192 '+e.user));w.style.color=colorOf(e.user);d.appendChild(w);}
    (e.images||[]).forEach(n=>{
      const a=el('a');a.href='/img/'+encodeURIComponent(n);a.target='_blank';
      const i=el('img');i.src='/img/'+encodeURIComponent(n);a.appendChild(i);d.appendChild(a);
    });
    (e.files||[]).forEach(f=>{
      const a=el('a','fc');a.href='/img/'+encodeURIComponent(f.n);a.target='_blank';
      a.appendChild(el('span',null,'\\uD83D\\uDCC4'));a.appendChild(el('div',null,f.o||f.n));d.appendChild(a);
    });
    if(e.text)d.appendChild(el('div',null,e.text));
    if(e.type!=='NOTE')d.appendChild(el('div','t',hhmm(e.time)));
    cv.appendChild(d);
  });
  cv.scrollTop=cv.scrollHeight;
  $('dl').style.display='inline-block';$('pr').style.display='inline-block';
  $('dl').href='/admin/transkrip?chat='+encodeURIComponent(chat)+'&'+qs();
}

function tbl(heads,rows,numCols){
  const t=el('table');const h=el('tr');
  heads.forEach((x,i)=>h.appendChild(el('th',numCols.includes(i)?'n':'',x)));t.appendChild(h);
  if(!rows.length){const r=el('tr');const c=el('td',null,'Tidak ada data');c.colSpan=heads.length;r.appendChild(c);t.appendChild(r);}
  rows.forEach(rw=>{const r=el('tr');rw.forEach((x,i)=>r.appendChild(el('td',numCols.includes(i)?'n':'',String(x))));t.appendChild(r);});
  return t;
}

async function loadLaporan(){
  const box=$('lap');box.textContent='Memuat...';
  const j=await getJson('/api/admin/laporan?'+qs());
  box.textContent='';
  const rg=($('dari').value||'awal')+' s/d '+($('sampai').value||'sekarang');
  box.appendChild(el('div',null,'')).id='ptitle';
  $('ptitle').textContent='Laporan WhatsApp Client \\u2014 '+rg;
  const tools=el('div','tools');
  const pr=el('button',null,'\\uD83D\\uDDA8 Cetak / Simpan PDF');pr.onclick=()=>window.print();
  const cs=el('a',null,'\\u2B07 Unduh CSV pesan');cs.href='/admin/csv?'+qs();
  tools.appendChild(pr);tools.appendChild(cs);box.appendChild(tools);
  const r=j.ringkasan;
  const cards=el('div','cards');
  [['Pesan masuk',r.masuk],['Pesan keluar',r.keluar],['File/gambar terkirim',r.lampiran_keluar],
   ['File/gambar diterima',r.lampiran_masuk],['Chat aktif',r.chat_aktif],['User aktif',r.user_aktif],
   ['Chat dilempar',r.pelemparan],['Balasan otomatis',r.otomatis||0]].forEach(c=>{
    const d=el('div','card');d.appendChild(el('b',null,c[1]));d.appendChild(el('span',null,c[0]));cards.appendChild(d);
  });
  box.appendChild(cards);
  box.appendChild(el('h3',null,'Per Username'));
  box.appendChild(tbl(['Username','Chat','Terkirim','Diterima','File terkirim','Terakhir'],
    j.per_user.map(u=>[u.user||'(belum ditetapkan)',u.chats,u.out,u.inn,u.files,tglw(u.last)]),[1,2,3,4]));
  box.appendChild(el('h3',null,'Per Hari'));
  box.appendChild(tbl(['Tanggal','Masuk','Keluar','File terkirim'],
    j.per_hari.map(h=>[tgl(h.tanggal),h.masuk,h.keluar,h.file]),[1,2,3]));
  box.appendChild(el('h3',null,'Per Nomor / Chat'));
  box.appendChild(tbl(['Nama','Nomor','Pemilik','Masuk','Keluar','File','Terakhir'],
    j.per_nomor.map(n=>[n.nama,n.nomor,n.pemilik||'(belum ditetapkan)',n.masuk,n.keluar,n.file,tglw(n.last)]),[3,4,5]));
  box.appendChild(el('h3',null,'Pelemparan Chat'));
  box.appendChild(tbl(['Waktu','Chat','Dari','Ke','Oleh','Catatan'],
    j.transfer.map(t=>[tglw(t.time),t.chat,t.dari,t.ke,t.oleh,t.catatan||'']),[]));
}

function showTab(t){
  tab=t;
  [['t1','rekap'],['t2','lap'],['t3','auto'],['t4','tema'],['t5','peran']].forEach(p=>$(p[0]).classList.toggle('on',t===p[1]));
  $('wrap').style.display=t==='rekap'?'flex':'none';
  $('lap').style.display=t==='lap'?'block':'none';
  $('auto').style.display=t==='auto'?'block':'none';
  $('tema').style.display=t==='tema'?'block':'none';
  $('peran').style.display=t==='peran'?'block':'none';
  document.querySelector('.flt').style.display=(t==='rekap'||t==='lap')?'flex':'none';
  refresh();
}
function refresh(){
  if(tab==='rekap'){loadUsers();if(selUser!==null)loadChats(selUser);}
  else if(tab==='lap')loadLaporan();
  else if(tab==='auto')loadAuto();
  else if(tab==='peran')loadPeran();
  else loadTema();
}
$('t1').onclick=()=>showTab('rekap');
$('t2').onclick=()=>showTab('lap');
$('t3').onclick=()=>showTab('auto');
$('t4').onclick=()=>showTab('tema');
$('t5').onclick=()=>showTab('peran');
const IZIN_ADM=__IZIN__;
[['t1','rekap'],['t2','rekap'],['t3','auto'],['t4','tema'],['t5','peran']].forEach(p=>{if(!IZIN_ADM.includes(p[1]))$(p[0]).style.display='none';});

/* ---------- Peran & izin ---------- */
async function loadPeran(){
  const box=$('peran');box.innerHTML='';box.appendChild(el('div','emp','Memuat...'));
  let j;try{j=await getJson('/api/admin/peran');}catch(e){return;}
  box.innerHTML='';
  if(!j.ok){box.appendChild(el('div','emp',j.error||'Gagal memuat'));return;}
  box.appendChild(el('h3',null,'Daftar peran'));
  box.appendChild(el('div','sub','Admin dari Apps Script selalu berperan Admin. User yang belum diberi peran otomatis menjadi Operator.'));
  const ids=Object.keys(j.peran);
  ids.forEach(id=>{
    const pr=j.peran[id],terkunci=id==='admin';
    const card=el('div','card');card.style.cssText='margin:10px 0;display:block;border-top-width:4px';
    const nm=el('input');nm.type='text';nm.value=pr.nama;nm.maxLength=30;nm.disabled=terkunci;nm.style.cssText='font-weight:700;font-size:15px;margin-bottom:8px;width:220px';
    card.appendChild(nm);
    const g=el('div');g.style.cssText='display:grid;grid-template-columns:repeat(auto-fill,minmax(280px,1fr));gap:4px 16px';
    const cbs={};
    Object.keys(j.izin).forEach(k=>{
      const l=el('label');l.style.cssText='display:flex;gap:7px;align-items:center;font-size:13px;color:inherit';
      const c=el('input');c.type='checkbox';c.checked=pr.izin.includes(k);c.disabled=terkunci;cbs[k]=c;
      l.appendChild(c);l.appendChild(document.createTextNode(j.izin[k]));g.appendChild(l);
    });
    card.appendChild(g);
    const bar=el('div');bar.style.cssText='margin-top:10px;display:flex;gap:8px;align-items:center';
    if(!terkunci){
      const sv=el('button',null,'Simpan');sv.onclick=async()=>{
        const r=await post('/api/admin/peran/simpan',{id,nama:nm.value,izin:Object.keys(cbs).filter(k=>cbs[k].checked)});
        if(!r.ok)alert(r.error);else loadPeran();};
      bar.appendChild(sv);
      if(!j.tetap.includes(id)){const dl=el('button',null,'Hapus');dl.onclick=async()=>{
        if(!confirm('Hapus peran "'+pr.nama+'"? User dengan peran ini kembali menjadi Operator.'))return;
        const r=await post('/api/admin/peran/hapus',{id});if(!r.ok)alert(r.error);else loadPeran();};bar.appendChild(dl);}
    }else bar.appendChild(el('span','sub','Peran bawaan, selalu punya semua izin.'));
    card.appendChild(bar);box.appendChild(card);
  });
  const nb=el('div');nb.style.cssText='margin:14px 0;display:flex;gap:8px';
  const ni=el('input');ni.type='text';ni.placeholder='Nama peran baru, mis. Kasir';ni.maxLength=30;
  const nbtn=el('button',null,'+ Tambah peran');nbtn.onclick=async()=>{
    if(!ni.value.trim()){alert('Isi nama peran');return;}
    const r=await post('/api/admin/peran/simpan',{nama:ni.value,izin:['kirim']});if(!r.ok)alert(r.error);else loadPeran();};
  nb.appendChild(ni);nb.appendChild(nbtn);box.appendChild(nb);

  box.appendChild(el('h3',null,'Peran tiap user'));
  const t=el('table');const h=el('tr');['User','Peran'].forEach(x=>h.appendChild(el('th',null,x)));t.appendChild(h);
  Object.keys(j.user).forEach(u=>{
    const r=el('tr');r.appendChild(el('td',null,u));
    const td=el('td');const sel=el('select');
    ids.forEach(id=>{const o=el('option',null,j.peran[id].nama);o.value=id;sel.appendChild(o);});
    sel.value=j.user[u];
    if(j.admin_apps[u]){sel.disabled=true;td.appendChild(sel);td.appendChild(document.createTextNode(' (admin Apps Script)'));}
    else{sel.onchange=async()=>{const r2=await post('/api/admin/peran/user',{user:u,peran:sel.value});if(!r2.ok){alert(r2.error);loadPeran();}};td.appendChild(sel);}
    r.appendChild(td);t.appendChild(r);
  });
  box.appendChild(t);
}

/* ---------- Tampilan & tema ---------- */
const FONTLBL={sistem:'Sistem (disarankan)',segoe:'Segoe UI',arial:'Arial',tahoma:'Tahoma',verdana:'Verdana',georgia:'Georgia (berkait)'};
const KIND=['logo','login_bg','wallpaper'];
let TM=null, TMF={}, TMURL={};
function lum(h){
  const c=v=>{v/=255;return v<=0.03928?v/12.92:Math.pow((v+0.055)/1.055,2.4);};
  return 0.2126*c(parseInt(h.slice(1,3),16))+0.7152*c(parseInt(h.slice(3,5),16))+0.0722*c(parseInt(h.slice(5,7),16));
}
function onCol(h){return lum(h)<0.4?'#ffffff':'#111b21';}
function rgbOf(h){return [parseInt(h.slice(1,3),16),parseInt(h.slice(3,5),16),parseInt(h.slice(5,7),16)];}
function urlTema(k){return TMF[k]?URL.createObjectURL(TMF[k]):(($('del_'+k).checked)?'':TMURL[k]);}

function formTema(){
  return {nama:$('tm_nama').value,tagline:$('tm_tag').value,preset:TM.pilih||'kustom',gelap:$('tm_gelap').checked,
    brand:$('tm_brand').value,brand_dark:$('tm_brand_dark').value,aksen:$('tm_aksen').value,
    out_bg:$('tm_out').value,in_bg:$('tm_in').value,chat_bg:$('tm_chat').value,
    font:$('tm_font').value,ukuran:$('tm_ukuran').value,radius:Number($('tm_radius').value),wall_vis:Number($('tm_wallvis').value)};
}
function terapkanTema(){
  if(!TM)return;
  const f=formTema(), base=TM.dasar[f.gelap?'gelap':'terang'], r=document.documentElement.style;
  const set=(k,v)=>r.setProperty('--'+k,v);
  Object.keys(base).forEach(k=>set(k,base[k]));
  set('brand',f.brand);set('brand-dark',f.brand_dark);set('accent',f.aksen);
  set('out-bg',f.out_bg);set('in-bg',f.in_bg);set('chat-bg',f.chat_bg);
  set('on-brand',onCol(f.brand));set('on-header',onCol(f.brand_dark));
  set('radius',f.radius+'px');set('font',TM.font[f.font]);set('fsm',{kecil:0.92,normal:1,besar:1.12}[f.ukuran]);
  $('tm_rv').textContent=f.radius;$('tm_wv').textContent=f.wall_vis;
  ['pv_nama','pv_nama2'].forEach(i=>$(i).textContent=f.nama||'Nama aplikasi');
  ['pv_tag','pv_tag2'].forEach(i=>$(i).textContent=f.tagline);
  const lg=urlTema('logo'), lb=urlTema('login_bg'), wp=urlTema('wallpaper');
  [['pv_logo',lg],['pv_logo2',lg]].forEach(p=>{$(p[0]).hidden=!p[1];if(p[1])$(p[0]).src=p[1];});
  const thumb={logo:lg,login_bg:lb,wallpaper:wp};
  KIND.forEach(k=>{$('th_'+k).style.backgroundImage=thumb[k]?'url('+thumb[k]+')':'none';});
  const [R,G,B]=rgbOf(f.chat_bg), a=(1-f.wall_vis/100).toFixed(2);
  $('pv_body').style.backgroundImage=wp?'linear-gradient(rgba('+R+','+G+','+B+','+a+'),rgba('+R+','+G+','+B+','+a+')),url('+wp+')':'none';
  const [r1,g1,b1]=rgbOf(f.brand_dark), [r2,g2,b2]=rgbOf(f.brand);
  $('pv_login').style.backgroundImage=lb?'linear-gradient(135deg,rgba('+r1+','+g1+','+b1+',.78),rgba('+r2+','+g2+','+b2+',.45)),url('+lb+')':'';
  document.querySelectorAll('.preset').forEach(p=>p.classList.toggle('on',p.dataset.k===TM.pilih));
}

function isiPreset(k){
  const p=TM.preset[k];TM.pilih=k;
  $('tm_brand').value=p.brand;$('tm_brand_dark').value=p.brand_dark;$('tm_aksen').value=p.aksen;
  $('tm_out').value=p.out_bg;$('tm_in').value=p.in_bg;$('tm_chat').value=p.chat_bg;$('tm_gelap').checked=!!p.gelap;
  terapkanTema();
}

async function loadTema(){
  const j=await getJson('/api/admin/tema');
  TM=j;TM.pilih=j.tema.preset;TMF={};
  const t=j.tema;
  $('tm_nama').value=t.nama;$('tm_tag').value=t.tagline;
  $('tm_brand').value=t.brand;$('tm_brand_dark').value=t.brand_dark;$('tm_aksen').value=t.aksen;
  $('tm_out').value=t.out_bg;$('tm_in').value=t.in_bg;$('tm_chat').value=t.chat_bg;$('tm_gelap').checked=t.gelap;
  const fs=$('tm_font');fs.textContent='';
  Object.keys(j.font).forEach(k=>{const o=el('option',null,FONTLBL[k]||k);o.value=k;fs.appendChild(o);});
  fs.value=t.font;$('tm_ukuran').value=t.ukuran;$('tm_radius').value=t.radius;$('tm_wallvis').value=t.wall_vis;
  TMURL={logo:t.logo?'/tema/'+t.logo:'',login_bg:t.login_bg?'/tema/'+t.login_bg:'',wallpaper:t.wallpaper?'/tema/'+t.wallpaper:''};
  KIND.forEach(k=>{$('del_'+k).checked=false;$('tm_'+k).value='';});
  const box=$('tm_presets');box.textContent='';
  Object.keys(j.preset).forEach(k=>{
    const p=j.preset[k];
    const d=el('div','preset');d.dataset.k=k;
    const sw=el('div','sw');[p.brand_dark,p.brand,p.out_bg,p.chat_bg].forEach(c=>{const i=el('i');i.style.background=c;sw.appendChild(i);});
    d.appendChild(sw);d.appendChild(el('span',null,p.nama));
    d.onclick=()=>isiPreset(k);box.appendChild(d);
  });
  terapkanTema();
}

async function simpanTema(){
  const f=formTema();
  f.hapus=KIND.filter(k=>$('del_'+k).checked&&!TMF[k]);
  const fd=new FormData();fd.append('data',JSON.stringify(f));
  KIND.forEach(k=>{if(TMF[k])fd.append(k,TMF[k]);});
  const bt=$('tm_simpan');bt.disabled=true;
  try{
    const r=await fetch('/api/admin/tema',{method:'POST',body:fd});const j=await r.json();
    if(!j.ok){alert(j.error||'Gagal menyimpan');bt.disabled=false;return;}
    location.reload();
  }catch(e){alert('Gagal terhubung ke server');bt.disabled=false;}
}
async function resetTema(){
  if(!confirm('Kembalikan semua tampilan ke bawaan? Logo dan gambar yang diunggah akan dihapus.'))return;
  const j=await post('/api/admin/tema/reset',{});
  if(j.ok)location.reload();
}
['tm_nama','tm_tag','tm_brand','tm_brand_dark','tm_aksen','tm_out','tm_in','tm_chat','tm_gelap','tm_font','tm_ukuran','tm_radius','tm_wallvis'].forEach(i=>{
  $(i).addEventListener('input',()=>{if(i.indexOf('tm_')===0&&['tm_brand','tm_brand_dark','tm_aksen','tm_out','tm_in','tm_chat','tm_gelap'].includes(i)&&TM)TM.pilih='kustom';terapkanTema();});
  $(i).addEventListener('change',terapkanTema);
});
KIND.forEach(k=>{
  $('tm_'+k).addEventListener('change',()=>{
    const f=$('tm_'+k).files[0];
    if(f&&f.size>TM.batas_mb[k]*1024*1024){alert('Ukuran maksimal '+TM.batas_mb[k]+' MB');$('tm_'+k).value='';return;}
    TMF[k]=f||null;if(f)$('del_'+k).checked=false;terapkanTema();
  });
  $('del_'+k).addEventListener('change',()=>{if($('del_'+k).checked){TMF[k]=null;$('tm_'+k).value='';}terapkanTema();});
});
$('tm_simpan').onclick=simpanTema;
$('tm_reset').onclick=resetTema;

const HARI=['Sen','Sel','Rab','Kam','Jum','Sab','Min'];
const PEMICU={kata_kunci:'Kata kunci',pertama:'Pesan pertama dari kontak baru',semua:'Semua pesan (cadangan)'};
let ruleEdit=null;
async function post(u,obj){
  const r=await fetch(u,{method:'POST',headers:{'Content-Type':'application/json'},body:JSON.stringify(obj)});
  return r.json();
}
function jadwalText(r){
  if(r.jadwal==='selalu')return 'Sepanjang waktu';
  const h=(r.hari&&r.hari.length)?r.hari.map(i=>HARI[i]).join(', ')+' ':'';
  return (r.jadwal==='dalam'?'Hanya ':'Di luar ')+h+r.mulai+'-'+r.selesai;
}

async function loadAuto(){
  const box=$('auto');box.textContent='Memuat...';
  const j=await getJson('/api/admin/auto');
  box.textContent='';
  const bar=el('div','bar');
  const lbl=el('label');const cb=el('input');cb.type='checkbox';cb.checked=!!j.aktif;
  cb.onchange=async()=>{await post('/api/admin/auto/aktif',{aktif:cb.checked});loadAuto();};
  lbl.appendChild(cb);lbl.appendChild(document.createTextNode(' Balasan otomatis aktif'));
  lbl.style.fontWeight='600';bar.appendChild(lbl);
  const nb=el('button',null,'+ Tambah aturan');nb.onclick=()=>openRule(null);bar.appendChild(nb);
  bar.appendChild(el('span',null,j.aktif?'Server membalas pesan masuk sesuai aturan di bawah.':'Nonaktif: tidak ada balasan otomatis yang dikirim.'));
  box.appendChild(bar);
  box.appendChild(el('div','hint','Aturan dicek dari atas ke bawah; yang pertama cocok dipakai. Grup tidak dibalas. Maksimal 5 balasan otomatis per kontak per jam. Teks boleh memakai {nama} {nomor} {jam} {tanggal}.'));
  if(!j.rules.length)box.appendChild(el('div','emp','Belum ada aturan. Klik "+ Tambah aturan".'));
  j.rules.forEach((r,i)=>{
    const c=el('div','rule'+(r.aktif?'':' off'));
    const h=el('h4');h.appendChild(document.createTextNode((i+1)+'. '+r.nama));
    h.appendChild(el('span','bd',PEMICU[r.pemicu]));h.appendChild(el('span','bd',jadwalText(r)));c.appendChild(h);
    if(r.pemicu==='kata_kunci')c.appendChild(el('div','rb','Kata kunci: '+r.kata.split(String.fromCharCode(10)).join(', ')));
    if(r.balasan_teks)c.appendChild(el('div','rb','Balasan: '+r.balasan_teks));
    if(r.lampiran){
      const d=el('div','rb','Lampiran: ');
      const a=el('a',null,(r.lampiran.gambar?'🖼 ':'📄 ')+r.lampiran.o);a.href='/admin/auto/lampiran/'+r.id;a.target='_blank';
      d.appendChild(a);c.appendChild(d);
    }
    c.appendChild(el('div','rb','Jeda '+r.jeda_detik+' detik · tidak membalas kontak yang sama lagi selama '+r.cooldown_menit+' menit'));
    const ra=el('div','ra');
    const t=el('label');const tc=el('input');tc.type='checkbox';tc.checked=!!r.aktif;
    tc.onchange=async()=>{await post('/api/admin/auto/toggle',{id:r.id,aktif:tc.checked});loadAuto();};
    t.appendChild(tc);t.appendChild(document.createTextNode(' Aktif'));ra.appendChild(t);
    const up=el('button',null,'↑');up.onclick=async()=>{await post('/api/admin/auto/geser',{id:r.id,arah:'naik'});loadAuto();};
    const dn=el('button',null,'↓');dn.onclick=async()=>{await post('/api/admin/auto/geser',{id:r.id,arah:'turun'});loadAuto();};
    const ed=el('button',null,'Ubah');ed.onclick=()=>openRule(r);
    const del=el('button',null,'Hapus');
    del.onclick=async()=>{if(confirm('Hapus aturan "'+r.nama+'"?')){await post('/api/admin/auto/hapus',{id:r.id});loadAuto();}};
    [up,dn,ed,del].forEach(b=>ra.appendChild(b));
    c.appendChild(ra);box.appendChild(c);
  });
}

function togForm(){
  $('f_kata_w').style.display=$('f_pemicu').value==='kata_kunci'?'block':'none';
  $('f_jam_w').style.display=$('f_jadwal').value==='selalu'?'none':'block';
}
function openRule(r){
  ruleEdit=r;
  $('rmt').textContent=r?'Ubah aturan':'Aturan balasan baru';
  $('f_nama').value=r?r.nama:'';
  $('f_aktif').checked=r?!!r.aktif:true;
  $('f_pemicu').value=r?r.pemicu:'kata_kunci';
  $('f_kata').value=r?r.kata:'';
  $('f_jadwal').value=r?r.jadwal:'selalu';
  $('f_mulai').value=r?r.mulai:'08:00';$('f_selesai').value=r?r.selesai:'16:00';
  document.querySelectorAll('.f_h').forEach(cb=>{cb.checked=!!(r&&r.hari&&r.hari.includes(Number(cb.value)));});
  $('f_teks').value=r?r.balasan_teks:'';
  $('f_file').value='';$('f_hapusl').checked=false;
  $('f_lamp').textContent=(r&&r.lampiran)?('Lampiran saat ini: '+r.lampiran.o):'';
  $('f_hapusw').style.display=(r&&r.lampiran)?'block':'none';
  $('f_jeda').value=r?r.jeda_detik:3;$('f_cd').value=r?r.cooldown_menit:60;
  togForm();
  $('rm').style.display='flex';
}
async function saveRule(){
  const data={id:ruleEdit?ruleEdit.id:'',nama:$('f_nama').value,aktif:$('f_aktif').checked,
    pemicu:$('f_pemicu').value,kata:$('f_kata').value,jadwal:$('f_jadwal').value,
    mulai:$('f_mulai').value,selesai:$('f_selesai').value,
    hari:[...document.querySelectorAll('.f_h')].filter(c=>c.checked).map(c=>Number(c.value)),
    balasan_teks:$('f_teks').value,cooldown_menit:Number($('f_cd').value),jeda_detik:Number($('f_jeda').value),
    hapus_lampiran:$('f_hapusl').checked};
  const fd=new FormData();fd.append('data',JSON.stringify(data));
  const f=$('f_file').files[0];if(f)fd.append('lampiran',f);
  try{
    const r=await fetch('/api/admin/auto/rule',{method:'POST',body:fd});const j=await r.json();
    if(!j.ok){alert(j.error||'Gagal menyimpan');return;}
    $('rm').style.display='none';loadAuto();
  }catch(e){alert('Gagal terhubung ke server');}
}
$('f_pemicu').onchange=togForm;$('f_jadwal').onchange=togForm;
$('f_batal').onclick=()=>{$('rm').style.display='none';};
$('f_simpan').onclick=saveRule;
$('go').onclick=refresh;
$('pr').onclick=()=>window.print();
loadUsers();
</script></body></html>"""


@app.route("/login", methods=["GET", "POST"])
def login():
    error = None
    if request.method == "POST":
        u = request.form.get("username", "").strip()
        p = request.form.get("password", "")
        try:
            res = api({"action": "login", "username": u, "password": p})
        except Exception as e:
            res = {"ok": False, "error": f"Gagal terhubung ke Apps Script: {e}"}
        if res.get("ok"):
            SESSIONS[res["username"]] = Session(res["username"], p, res["token"], bool(res.get("admin")))
            session["u"] = res["username"]
            return redirect(url_for("index"))
        error = res.get("error", "Login gagal")
    return render_template_string(LOGIN_HTML, error=error, t=TEMA.publik())


@app.route("/logout")
def logout():
    u = session.pop("u", None)
    if u:
        SESSIONS.pop(u, None)
    return redirect(url_for("login"))


@app.route("/")
@login_required
def index():
    return render_template_string(MAIN_HTML, user=session["u"], t=TEMA.publik())


@app.route("/api/messages")
@login_required
def api_messages():
    try:
        after = int(request.args.get("after", 0))
    except ValueError:
        after = 0
    user = session["u"]
    items = visible_items(user, STORE.after(after))
    if after == 0:
        items = items[-500:]
    izin = sorted(PERAN.izin_user(user))
    resp = {"ok": True, "items": items, "status": WORKER.status,
            "admin": "lihat_semua" in izin, "izin": izin, "peran": PERAN.nama_peran(user),
            "epoch": EPOCH.get(user, 0)}
    if "lihat_semua" in izin or "tetapkan" in izin:
        resp["owners"] = OWN.all()
    return jsonify(resp)


@app.route("/api/send", methods=["POST"])
@login_required
def api_send():
    if not punya(session["u"], "kirim"):
        return jsonify(ok=False, error="Peran Anda tidak boleh mengirim pesan"), 403
    if WORKER.status != "Terhubung":
        return jsonify(ok=False, error="WhatsApp server belum terhubung"), 503

    chat = request.form.get("chat", "").strip()[:200]
    no = ""
    if re.fullmatch(r"\d{8,15}", chat):
        no, chat = chat, ""
    elif not chat:
        no = re.sub(r"\D", "", request.form.get("no", ""))
        if no.startswith("0"):
            no = KODE_NEGARA + no[1:]
        if not (8 <= len(no) <= 15):
            return jsonify(ok=False, error="Nomor tidak valid"), 400

    user = session["u"]
    sess = SESSIONS[user]
    key = no or chat
    if not punya(user, "lihat_semua"):
        owner = OWN.get(key)
        if owner and owner != user:
            return jsonify(ok=False, error="Chat ini milik user lain"), 403
        if not owner and chat:
            return jsonify(ok=False, error="Chat ini belum ditetapkan ke Anda"), 403

    teks = request.form.get("text", "").strip()
    f = request.files.get("file") or request.files.get("image")
    tmp, orig, is_img = None, "", True
    if f and f.filename:
        ext = os.path.splitext(f.filename)[1].lower()
        if ext not in FILE_EXT:
            return jsonify(ok=False, error="Tipe file tidak diizinkan. Boleh: gambar, pdf, doc/docx, "
                                           "xls/xlsx, ppt/pptx, txt, csv, zip, rar, 7z"), 400
        is_img = ext in IMG_EXT
        orig = secure_filename(f.filename)
        if not orig.lower().endswith(ext):
            orig = "berkas" + ext
        tmp_dir = os.path.join(TMP_DIR, uuid.uuid4().hex)  # folder unik, nama file tetap asli
        os.makedirs(tmp_dir, exist_ok=True)
        tmp = os.path.join(tmp_dir, orig)
        f.save(tmp)
    if not teks and not tmp:
        return jsonify(ok=False, error="Isi pesan atau pilih gambar/file"), 400

    if not punya(user, "lihat_semua") and not OWN.get(key):
        had = STORE.has_chat(key)
        OWN.set(key, user)
        if had:
            bump(user)

    WORKER.cmd_q.put({"no": no, "chat": chat, "text": teks, "tmp": tmp, "orig": orig,
                      "is_img": is_img, "sess": sess})
    return jsonify(ok=True)


@app.route("/img/<path:name>")
@login_required
def img(name):
    name = os.path.basename(name)
    chat = STORE.file_chat.get(name)
    if chat is None or not os.path.isfile(os.path.join(IMG_DIR, name)):
        abort(404)
    if not can_see(session["u"], chat):
        abort(403)
    ext = os.path.splitext(name)[1].lower()
    inline = ext in IMG_EXT or ext == ".pdf"
    resp = send_from_directory(IMG_DIR, name, as_attachment=not inline,
                               download_name=STORE.file_orig.get(name, name))
    resp.headers["X-Content-Type-Options"] = "nosniff"
    return resp


def izin_required(*izin):
    def deco(f):
        @wraps(f)
        def wrap(*a, **k):
            u = session.get("u")
            if not any(punya(u, i) for i in izin):
                return jsonify(ok=False, error="Peran Anda tidak punya izin untuk tindakan ini"), 403
            return f(*a, **k)
        return login_required(wrap)
    return deco


def admin_required(f):
    @wraps(f)
    def wrap(*a, **k):
        if not is_admin(session.get("u")):
            return jsonify(ok=False, error="Hanya admin"), 403
        return f(*a, **k)
    return login_required(wrap)


def _semua_pesan():
    rows = []
    try:
        with open(MSG_FILE, "r", encoding="utf-8") as f:
            for x in f:
                x = x.strip()
                if x:
                    try:
                        rows.append(json.loads(x))
                    except Exception:
                        pass
    except FileNotFoundError:
        pass
    rows.sort(key=lambda e: (e.get("time") or "", e.get("id") or 0))
    return rows


def _lampiran(e):
    return len(e.get("images") or []) + len(e.get("files") or [])


def _ringkas(e):
    if e.get("text"):
        isi = e["text"][:80]
    elif e.get("images"):
        isi = "[gambar]"
    elif e.get("files"):
        isi = "[file] " + (e["files"][0].get("o") or "")
    else:
        isi = ""
    if e.get("type") == "IN" and e.get("group") and e.get("sender"):
        return f"{e['sender']}: {isi}"
    return isi


@app.route("/api/rekap")
@izin_required("rekap")
def api_rekap():
    dari = request.args.get("dari", "")
    sampai = request.args.get("sampai", "")
    rows = [e for e in _semua_pesan()
            if e.get("type") in ("IN", "OUT")
            and (not dari or e["time"][:10] >= dari)
            and (not sampai or e["time"][:10] <= sampai)]

    def kunci(e):
        return e.get("chat") or e.get("who") or ""

    if "user" in request.args:  # rincian chat milik satu username ("" = belum ditetapkan)
        target = request.args.get("user", "")
        per = {}
        for e in rows:
            k = kunci(e)
            if (OWN.get(k) or "") != target:
                continue
            c = per.setdefault(k, {"chat": k, "name": "", "number": "", "group": False,
                                   "inn": 0, "out": 0, "files": 0, "last": "", "snip": ""})
            c["inn" if e["type"] == "IN" else "out"] += 1
            c["files"] += _lampiran(e)
            if e.get("name"):
                c["name"] = e["name"]
            if e.get("number"):
                c["number"] = e["number"]
            if e.get("group"):
                c["group"] = True
            c["last"], c["snip"] = e["time"], _ringkas(e)
        return jsonify(ok=True, rows=sorted(per.values(), key=lambda c: c["last"], reverse=True))

    users = {}

    def U(n):
        return users.setdefault(n, {"user": n, "chats": set(), "out": 0, "inn": 0, "files": 0, "last": ""})

    for e in rows:
        k = kunci(e)
        pemilik = U(OWN.get(k) or "")
        pemilik["chats"].add(k)
        pemilik["last"] = max(pemilik["last"], e["time"])
        if e["type"] == "IN":
            pemilik["inn"] += 1
        else:
            if not (e.get("user") or "").startswith("["):  # balasan otomatis tidak dihitung sebagai user
                pengirim = U(e.get("user") or "")
                pengirim["out"] += 1
                pengirim["files"] += _lampiran(e)
                pengirim["last"] = max(pengirim["last"], e["time"])
    hasil = []
    for u in sorted(users.values(), key=lambda x: (x["user"] == "", x["user"].lower())):
        u["chats"] = len(u["chats"])
        hasil.append(u)
    return jsonify(ok=True, rows=hasil)


@app.route("/api/chat")
@login_required
def api_chat():
    chat = request.args.get("chat", "")
    if not chat or not can_see(session["u"], chat):
        return jsonify(ok=False, error="Tidak ada akses ke chat ini"), 403
    rows = [e for e in _semua_pesan()
            if e.get("type") in ("IN", "OUT", "NOTE") and (e.get("chat") or e.get("who") or "") == chat]
    return jsonify(ok=True, items=rows[-500:])


BAD_NAMA = re.compile(r"info kontak|contact info|click here|klik di sini", re.I)


def _fmt_no(n):
    if not n:
        return ""
    if n.startswith("62"):
        m = re.fullmatch(r"(\d{3})(\d{3,4})(\d+)", n[2:])
        return "+62 " + ("-".join(m.groups()) if m else n[2:])
    return "+" + n


def _nama_tampil(name, number, chat):
    if name and not BAD_NAMA.search(name) and not re.fullmatch(r"[+\d\s-]+", name):
        return name
    n = number or (chat if re.fullmatch(r"\d{8,15}", chat or "") else "")
    if n:
        return _fmt_no(n)
    return "Chat lama" if BAD_NAMA.search(name or chat or "") else (name or chat or "")


def _chat_key(e):
    return e.get("chat") or e.get("who") or ""


def _dalam_rentang(e, dari, sampai):
    d = (e.get("time") or "")[:10]
    return (not dari or d >= dari) and (not sampai or d <= sampai)


def _info_chat(rows):
    """chat -> {name, number, group} dari entri terbaru."""
    info = {}
    for e in rows:
        if e.get("type") not in ("IN", "OUT"):
            continue
        c = info.setdefault(_chat_key(e), {"name": "", "number": "", "group": False})
        if e.get("name"):
            c["name"] = e["name"]
        if e.get("number"):
            c["number"] = e["number"]
        if e.get("group"):
            c["group"] = True
    return info


def _nomor_chat(k, info):
    n = (info.get(k) or {}).get("number") or (k if re.fullmatch(r"\d{8,15}", k or "") else "")
    return _fmt_no(n) if n else ""


# ----------------------- Lempar chat ke client lain / admin -----------------------
@app.route("/api/transfer", methods=["POST"])
@login_required
def api_transfer():
    user = session["u"]
    sess = SESSIONS[user]
    if not punya(user, "lempar"):
        return jsonify(ok=False, error="Peran Anda tidak boleh melempar chat"), 403
    adm = punya(user, "tetapkan")
    d = request.get_json(silent=True) or {}
    chat = str(d.get("chat", "")).strip()[:200]
    tujuan = str(d.get("to", "")).strip()
    catatan = str(d.get("note", "")).strip()[:200]
    if not chat or not STORE.has_chat(chat):
        return jsonify(ok=False, error="Chat tidak dikenal"), 400
    lama = OWN.get(chat) or ""
    if not adm and lama != user:
        return jsonify(ok=False, error="Hanya pemilik chat atau peran dengan izin menetapkan yang bisa melempar chat"), 403
    if not tujuan and not adm:
        return jsonify(ok=False, error="Pilih user tujuan"), 400
    if tujuan == lama:
        return jsonify(ok=False, error="Chat sudah menjadi milik user tersebut"), 400
    if tujuan:
        try:
            if tujuan not in users_list(sess):
                return jsonify(ok=False, error="User tujuan tidak ada di USER_CLIENT"), 400
        except Exception as e:
            return jsonify(ok=False, error=str(e)), 502

    OWN.set(chat, tujuan)
    bump(lama)
    bump(tujuan)
    info = _info_chat(_semua_pesan()).get(chat, {"name": "", "number": "", "group": False})
    teks = (f"Chat dilempar dari {lama or '(belum ditetapkan)'} ke {tujuan or '(belum ditetapkan)'} "
            f"oleh {user}" + (f". Catatan: {catatan}" if catatan else ""))
    STORE.add(type="NOTE", who=chat, chat=chat, name=info["name"], number=info["number"],
              text=teks, images=[],
              transfer={"dari": lama, "ke": tujuan, "oleh": user, "catatan": catatan})
    return jsonify(ok=True)


# ----------------------- Halaman & laporan admin -----------------------
@app.route("/admin")
@login_required
def admin_page():
    izin = sorted(PERAN.izin_user(session["u"]))
    if not set(izin) & {"rekap", "auto", "tema", "peran"}:
        return redirect(url_for("index"))
    t = TEMA.publik()
    logo = f'<img src="{esc(t["logo_url"])}" alt="">' if t["logo_url"] else ""
    icon = f'<link rel="icon" href="{esc(t["logo_url"])}">' if t["logo_url"] else ""
    h = (ADMIN_HTML.replace("__USER__", esc(session["u"])).replace("__NAMA__", esc(t["nama"]))
         .replace("__LOGO__", logo).replace("__ICON__", icon).replace("__VER__", str(t["ver"]))
         .replace("__IZIN__", json.dumps(izin)))
    return Response(h, mimetype="text/html")


@app.route("/api/admin/laporan")
@izin_required("rekap")
def api_admin_laporan():
    dari = request.args.get("dari", "")
    sampai = request.args.get("sampai", "")
    semua = _semua_pesan()
    info = _info_chat(semua)
    rows = [e for e in semua if e.get("type") in ("IN", "OUT") and _dalam_rentang(e, dari, sampai)]
    notes = [e for e in semua if e.get("type") == "NOTE" and e.get("transfer") and _dalam_rentang(e, dari, sampai)]

    ring = {"masuk": 0, "keluar": 0, "lampiran_keluar": 0, "lampiran_masuk": 0, "otomatis": 0}
    users, hari, nomor = {}, {}, {}

    def U(n):
        return users.setdefault(n, {"user": n, "chats": set(), "out": 0, "inn": 0, "files": 0, "last": ""})

    for e in rows:
        k = _chat_key(e)
        lamp = _lampiran(e)
        tgl = e["time"][:10]
        h = hari.setdefault(tgl, {"tanggal": tgl, "masuk": 0, "keluar": 0, "file": 0})
        n = nomor.setdefault(k, {"chat": k, "masuk": 0, "keluar": 0, "file": 0, "last": ""})
        n["last"] = max(n["last"], e["time"])
        pemilik = U(OWN.get(k) or "")
        pemilik["chats"].add(k)
        pemilik["last"] = max(pemilik["last"], e["time"])
        if e["type"] == "IN":
            ring["masuk"] += 1
            ring["lampiran_masuk"] += lamp
            h["masuk"] += 1
            n["masuk"] += 1
            pemilik["inn"] += 1
        else:
            ring["keluar"] += 1
            if e.get("auto"):
                ring["otomatis"] += 1
            ring["lampiran_keluar"] += lamp
            h["keluar"] += 1
            h["file"] += lamp
            n["keluar"] += 1
            n["file"] += lamp
            u = U(e.get("user") or "")
            u["out"] += 1
            u["files"] += lamp
            u["last"] = max(u["last"], e["time"])

    per_user = []
    for u in sorted(users.values(), key=lambda x: (x["user"] == "", x["user"].lower())):
        u["chats"] = len(u["chats"])
        per_user.append(u)
    per_nomor = []
    for k, n in nomor.items():
        c = info.get(k, {"name": "", "number": "", "group": False})
        n["nama"] = _nama_tampil(c["name"], c["number"], k)
        n["nomor"] = _nomor_chat(k, info)
        n["pemilik"] = OWN.get(k) or ""
        per_nomor.append(n)
    per_nomor.sort(key=lambda x: x["last"], reverse=True)
    transfer = []
    for e in sorted(notes, key=lambda x: x["time"], reverse=True):
        k = _chat_key(e)
        c = info.get(k, {"name": "", "number": "", "group": False})
        t = e["transfer"]
        transfer.append({"time": e["time"], "chat": _nama_tampil(c["name"], c["number"], k),
                         "dari": t.get("dari") or "(belum ditetapkan)", "ke": t.get("ke") or "(belum ditetapkan)",
                         "oleh": t.get("oleh", ""), "catatan": t.get("catatan", "")})
    ring["chat_aktif"] = len(nomor)
    ring["user_aktif"] = len([x for x in users.values() if x["user"] and not x["user"].startswith("[") and x["out"]])
    ring["pelemparan"] = len(notes)
    return jsonify(ok=True, ringkasan=ring, per_user=per_user,
                   per_hari=sorted(hari.values(), key=lambda x: x["tanggal"], reverse=True),
                   per_nomor=per_nomor, transfer=transfer)


def _aman_csv(v):
    v = "" if v is None else str(v)
    return "'" + v if v[:1] in ("=", "+", "-", "@") else v


@app.route("/admin/csv")
@izin_required("rekap")
def admin_csv():
    dari = request.args.get("dari", "")
    sampai = request.args.get("sampai", "")
    semua = _semua_pesan()
    info = _info_chat(semua)
    buf = io.StringIO()
    w = csv.writer(buf)
    w.writerow(["Waktu", "Jenis", "Pemilik chat", "Nama", "Nomor", "Pengirim", "Pesan", "Lampiran"])
    jenis = {"IN": "Masuk", "OUT": "Keluar", "NOTE": "Catatan"}
    for e in semua:
        if e.get("type") not in jenis or not _dalam_rentang(e, dari, sampai):
            continue
        k = _chat_key(e)
        c = info.get(k, {"name": "", "number": "", "group": False})
        lamp = "; ".join(list(e.get("images") or []) + [f.get("o") or f.get("n") for f in (e.get("files") or [])])
        w.writerow([_aman_csv(x) for x in (
            e["time"], jenis[e["type"]], OWN.get(k) or "", _nama_tampil(c["name"], c["number"], k),
            _nomor_chat(k, info), e.get("user") or e.get("sender") or "", e.get("text", ""), lamp)])
    nama = f"pesan_{dari or 'awal'}_{sampai or 'akhir'}.csv"
    return Response("\ufeff" + buf.getvalue(), mimetype="text/csv",
                    headers={"Content-Disposition": f'attachment; filename="{nama}"'})


def _transkrip_html(judul, bagian, info):
    css = ("body{font-family:Segoe UI,Arial,sans-serif;background:#efeae2;margin:0;padding:20px}"
           "h1{font-size:18px}h2{font-size:16px;background:#128c7e;color:#fff;padding:8px 12px;border-radius:8px;margin-top:28px}"
           ".m{max-width:70%;padding:6px 9px;margin:4px 0;border-radius:8px;box-shadow:0 1px 1px #0003;white-space:pre-wrap;word-wrap:break-word}"
           ".in{background:#fff;margin-right:auto}.out{background:#d9fdd3;margin-left:auto}"
           ".note{background:#fff3cd;margin:6px auto;text-align:center;font-size:13px}"
           ".w{font-size:12px;font-weight:700;color:#128c7e}.t{font-size:11px;color:#667781;text-align:right}"
           ".d{text-align:center;color:#54656f;font-size:12px;margin:12px 0}img{max-width:260px;display:block;margin:4px 0}"
           "@media print{body{background:#fff}}")
    out = [f"<!doctype html><html lang='id'><head><meta charset='utf-8'><title>{esc(judul)}</title>"
           f"<style>{css}</style></head><body><h1>{esc(judul)}</h1>"
           f"<div style='color:#667781;font-size:12px'>Dibuat {datetime.now():%d/%m/%Y %H:%M}</div>"]
    for k, items in bagian:
        c = info.get(k, {"name": "", "number": "", "group": False})
        nm = _nama_tampil(c["name"], c["number"], k)
        no = _nomor_chat(k, info)
        out.append(f"<h2>{esc(nm)}{' (' + esc(no) + ')' if no and no != nm else ''}"
                   f" &middot; pemilik: {esc(OWN.get(k) or '-')}</h2>")
        last = ""
        for e in items:
            tgl = e["time"][:10]
            if tgl != last:
                last = tgl
                out.append(f"<div class='d'>{tgl[8:10]}/{tgl[5:7]}/{tgl[:4]}</div>")
            cls = {"IN": "in", "OUT": "out"}.get(e["type"], "note")
            h = [f"<div class='m {cls}'>"]
            if e["type"] == "OUT" and e.get("user"):
                h.append(f"<div class='w'>&rarr; {esc(e['user'])}</div>")
            if e["type"] == "IN" and e.get("sender"):
                h.append(f"<div class='w'>{esc(e['sender'])}</div>")
            for n in e.get("images") or []:
                p = os.path.join(IMG_DIR, os.path.basename(n))
                try:
                    if os.path.getsize(p) <= 600 * 1024:
                        mt = mimetypes.guess_type(p)[0] or "image/jpeg"
                        with open(p, "rb") as f:
                            h.append(f"<img src='data:{mt};base64,{base64.b64encode(f.read()).decode()}'>")
                        continue
                except OSError:
                    pass
                h.append(f"<div>[gambar: {esc(n)}]</div>")
            for fl in e.get("files") or []:
                h.append(f"<div>&#128196; {esc(fl.get('o') or fl.get('n'))}</div>")
            if e.get("text"):
                h.append(f"<div>{esc(e['text'])}</div>")
            if e["type"] != "NOTE":
                h.append(f"<div class='t'>{e['time'][11:16]}</div>")
            h.append("</div>")
            out.append("".join(h))
    out.append("</body></html>")
    return "\n".join(out)


@app.route("/admin/transkrip")
@izin_required("rekap")
def admin_transkrip():
    dari = request.args.get("dari", "")
    sampai = request.args.get("sampai", "")
    semua = _semua_pesan()
    info = _info_chat(semua)
    per = {}
    for e in semua:
        if e.get("type") in ("IN", "OUT", "NOTE") and _dalam_rentang(e, dari, sampai):
            per.setdefault(_chat_key(e), []).append(e)
    if "chat" in request.args:
        k = request.args["chat"]
        bagian = [(k, per.get(k, []))]
        judul = "Transkrip chat"
    elif "user" in request.args:
        u = request.args["user"]
        bagian = [(k, v) for k, v in per.items() if (OWN.get(k) or "") == u]
        bagian.sort(key=lambda b: b[1][-1]["time"], reverse=True)
        judul = f"Transkrip chat milik {u or '(belum ditetapkan)'}"
    else:
        abort(400)
    if dari or sampai:
        judul += f" ({dari or 'awal'} s/d {sampai or 'sekarang'})"
    nama = re.sub(r"[^A-Za-z0-9_-]+", "_", judul)[:60] or "transkrip"
    return Response(_transkrip_html(judul, bagian, info), mimetype="text/html",
                    headers={"Content-Disposition": f'attachment; filename="{nama}.html"'})


def _terima_lampiran(f, folder, rid):
    """Validasi & simpan unggahan (gambar/file). Return dict lampiran atau raise ValueError."""
    ext = os.path.splitext(f.filename)[1].lower()
    if ext not in FILE_EXT:
        raise ValueError("Tipe file tidak diizinkan. Boleh: gambar, pdf, doc/docx, xls/xlsx, "
                         "ppt/pptx, txt, csv, zip, rar, 7z")
    orig = secure_filename(f.filename)
    if not orig.lower().endswith(ext):
        orig = "berkas" + ext
    stored = f"{rid}_{orig}"
    f.save(os.path.join(folder, stored))
    return {"n": stored, "o": orig, "gambar": ext in IMG_EXT}


def _int_batas(v, lo, hi, default):
    try:
        return max(lo, min(hi, int(v)))
    except (TypeError, ValueError):
        return default


# ----------------------- Balasan otomatis (admin) -----------------------
def _bersihkan_aturan(d):
    nama = str(d.get("nama", "")).strip()[:60]
    if not nama:
        raise ValueError("Nama aturan wajib diisi")
    pemicu = d.get("pemicu", "kata_kunci")
    if pemicu not in ("kata_kunci", "pertama", "semua"):
        raise ValueError("Pemicu tidak valid")
    kata = str(d.get("kata", ""))[:500]
    if pemicu == "kata_kunci" and not re.sub(r"[,\s]", "", kata):
        raise ValueError("Isi minimal satu kata kunci")
    jadwal = d.get("jadwal", "selalu")
    if jadwal not in ("selalu", "dalam", "luar"):
        raise ValueError("Jadwal tidak valid")
    mulai, selesai = str(d.get("mulai", "08:00")), str(d.get("selesai", "16:00"))
    if jadwal != "selalu" and not (re.fullmatch(r"([01]\d|2[0-3]):[0-5]\d", mulai)
                                   and re.fullmatch(r"([01]\d|2[0-3]):[0-5]\d", selesai)):
        raise ValueError("Format jam harus HH:MM")
    hari = sorted({int(x) for x in (d.get("hari") or []) if str(x).isdigit() and 0 <= int(x) <= 6})
    return {"nama": nama, "aktif": bool(d.get("aktif", True)), "pemicu": pemicu, "kata": kata,
            "jadwal": jadwal, "mulai": mulai, "selesai": selesai, "hari": hari,
            "balasan_teks": str(d.get("balasan_teks", "")).strip()[:1500],
            "cooldown_menit": _int_batas(d.get("cooldown_menit"), 0, 10080, 60),
            "jeda_detik": _int_batas(d.get("jeda_detik"), 0, 120, 3)}


@app.route("/api/admin/auto")
@izin_required("auto")
def api_auto_get():
    return jsonify(ok=True, **AUTO.snapshot())


@app.route("/api/admin/auto/aktif", methods=["POST"])
@izin_required("auto")
def api_auto_aktif():
    AUTO.set_aktif((request.get_json(silent=True) or {}).get("aktif"))
    return jsonify(ok=True)


@app.route("/api/admin/auto/rule", methods=["POST"])
@izin_required("auto")
def api_auto_rule():
    try:
        d = json.loads(request.form.get("data", "{}"))
        rule = _bersihkan_aturan(d)
    except ValueError as e:
        return jsonify(ok=False, error=str(e)), 400
    except Exception:
        return jsonify(ok=False, error="Data tidak valid"), 400
    lama = AUTO.get(str(d.get("id", ""))) if d.get("id") else None
    rid = lama["id"] if lama else uuid.uuid4().hex[:8]
    lamp = (lama or {}).get("lampiran")
    f = request.files.get("lampiran")
    try:
        if f and f.filename:
            baru = _terima_lampiran(f, AUTO_DIR, rid)
            if lamp and lamp["n"] != baru["n"]:
                AutoReply.hapus_berkas(lamp)
            lamp = baru
        elif d.get("hapus_lampiran") and lamp:
            AutoReply.hapus_berkas(lamp)
            lamp = None
    except ValueError as e:
        return jsonify(ok=False, error=str(e)), 400
    if not rule["balasan_teks"] and not lamp:
        return jsonify(ok=False, error="Isi teks balasan atau pilih lampiran (gambar/file)"), 400
    rule["id"], rule["lampiran"] = rid, lamp
    AUTO.simpan(rule)
    return jsonify(ok=True, id=rid)


@app.route("/api/admin/auto/toggle", methods=["POST"])
@izin_required("auto")
def api_auto_toggle():
    d = request.get_json(silent=True) or {}
    return jsonify(ok=AUTO.toggle(str(d.get("id", "")), d.get("aktif")))


@app.route("/api/admin/auto/hapus", methods=["POST"])
@izin_required("auto")
def api_auto_hapus():
    return jsonify(ok=AUTO.hapus(str((request.get_json(silent=True) or {}).get("id", ""))))


@app.route("/api/admin/auto/geser", methods=["POST"])
@izin_required("auto")
def api_auto_geser():
    d = request.get_json(silent=True) or {}
    return jsonify(ok=AUTO.geser(str(d.get("id", "")), -1 if d.get("arah") == "naik" else 1))


@app.route("/admin/auto/lampiran/<rid>")
@izin_required("auto")
def admin_auto_lampiran(rid):
    r = AUTO.get(rid)
    l = (r or {}).get("lampiran")
    if not l or not os.path.isfile(os.path.join(AUTO_DIR, l["n"])):
        abort(404)
    inline = l.get("gambar") or l["n"].lower().endswith(".pdf")
    resp = send_from_directory(AUTO_DIR, l["n"], as_attachment=not inline, download_name=l["o"])
    resp.headers["X-Content-Type-Options"] = "nosniff"
    return resp


# ----------------------- Pesan terjadwal -----------------------
@app.route("/api/jadwal", methods=["GET", "POST"])
@login_required
def api_jadwal():
    user = session["u"]
    sess = SESSIONS[user]
    semua = punya(user, "lihat_semua")
    if not punya(user, "jadwal"):
        return jsonify(ok=False, error="Peran Anda tidak boleh memakai pesan terjadwal"), 403
    if request.method == "GET":
        return jsonify(ok=True, admin=semua, items=JADWAL.snapshot(user, semua))
    try:
        d = json.loads(request.form.get("data", "{}"))
    except Exception:
        return jsonify(ok=False, error="Data tidak valid"), 400

    chat = str(d.get("tujuan_chat", "")).strip()[:200]
    no = ""
    if re.fullmatch(r"\d{8,15}", chat):
        no, chat = chat, ""
    elif not chat:
        no = re.sub(r"\D", "", str(d.get("tujuan_no", "")))
        if no.startswith("0"):
            no = KODE_NEGARA + no[1:]
        if not (8 <= len(no) <= 15):
            return jsonify(ok=False, error="Nomor tujuan tidak valid"), 400
    key = no or chat
    if not punya(user, "lihat_semua"):
        owner = OWN.get(key)
        if owner and owner != user:
            return jsonify(ok=False, error="Chat ini milik user lain"), 403
        if not owner and chat:
            return jsonify(ok=False, error="Chat ini belum ditetapkan ke Anda"), 403

    try:
        w = datetime.strptime(f"{d.get('tanggal', '')} {d.get('jam', '')}", "%Y-%m-%d %H:%M")
    except ValueError:
        return jsonify(ok=False, error="Tanggal / jam tidak valid"), 400
    if w < datetime.now() - timedelta(minutes=1):
        return jsonify(ok=False, error="Waktu pengiriman sudah lewat"), 400
    ulang = d.get("ulang", "sekali")
    if ulang not in ("sekali", "harian", "mingguan", "bulanan"):
        return jsonify(ok=False, error="Pengulangan tidak valid"), 400
    sampai = str(d.get("sampai", "") or "")
    if ulang != "sekali" and sampai:
        if not re.fullmatch(r"\d{4}-\d{2}-\d{2}", sampai) or sampai < w.strftime("%Y-%m-%d"):
            return jsonify(ok=False, error="Tanggal 'sampai' tidak valid"), 400
    else:
        sampai = ""
    teks = str(d.get("text", "")).strip()[:1500]
    if JADWAL.hitung_aktif(user) >= 100:
        return jsonify(ok=False, error="Maksimal 100 jadwal aktif per user"), 400

    rid = uuid.uuid4().hex[:8]
    lamp = None
    f = request.files.get("lampiran")
    try:
        if f and f.filename:
            lamp = _terima_lampiran(f, JADWAL_DIR, rid)
    except ValueError as e:
        return jsonify(ok=False, error=str(e)), 400
    if not teks and not lamp:
        return jsonify(ok=False, error="Isi pesan atau pilih gambar/file"), 400

    info = _info_chat(_semua_pesan()).get(key, {"name": "", "number": ""})
    label = _nama_tampil(info["name"], info["number"] or no, key)
    if not punya(user, "lihat_semua") and not OWN.get(key):
        had = STORE.has_chat(key)
        OWN.set(key, user)
        if had:
            bump(user)
    JADWAL.tambah({"id": rid, "user": user, "no": no, "chat": chat, "label": label, "text": teks,
                   "lampiran": lamp, "waktu": w.strftime("%Y-%m-%d %H:%M"), "ulang": ulang,
                   "sampai": sampai, "status": "menunggu", "dibuat": datetime.now().strftime("%Y-%m-%d %H:%M"),
                   "terakhir": "", "hasil": ""})
    return jsonify(ok=True, id=rid)


@app.route("/api/jadwal/batal", methods=["POST"])
@login_required
def api_jadwal_batal():
    user = session["u"]
    ok_, err = JADWAL.batal(str((request.get_json(silent=True) or {}).get("id", "")), user, punya(user, "lihat_semua"))
    return (jsonify(ok=True) if ok_ else (jsonify(ok=False, error=err), 400))


@app.route("/qr")
@izin_required("wa")
def qr_page():
    return Response("""<!doctype html><html lang="id"><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1"><title>Scan QR WhatsApp</title>
<link rel="stylesheet" href="/tema.css"></head>
<body style="font-family:var(--font,Segoe UI,Arial,sans-serif);color:var(--text,#111);background:var(--page-bg,#fff);text-align:center;padding:24px">
<h2>Scan QR WhatsApp</h2>
<p>Di HP: WhatsApp &rarr; Perangkat tertaut &rarr; Tautkan perangkat, lalu pindai kode ini.</p>
<img id="q" src="/qr.png" alt="QR" style="width:340px;max-width:92%;border:1px solid #ccc;background:#fff">
<p id="s" style="color:#667781"></p>
<script>
async function t(){
  try{
    const r=await fetch('/api/messages?after=999999999');const j=await r.json();
    document.getElementById('s').textContent=j.status;
    if(j.status==='Terhubung'){document.getElementById('q').style.display='none';document.getElementById('s').textContent='Terhubung. Halaman ini boleh ditutup.';}
    else document.getElementById('q').src='/qr.png?t='+Date.now();
  }catch(e){}
}
setInterval(t,4000);t();
</script></body></html>""", mimetype="text/html")


@app.route("/qr.png")
@izin_required("wa")
def qr_png():
    if not os.path.isfile(QR_FILE):
        abort(404)
    resp = send_from_directory(BASE_DIR, os.path.basename(QR_FILE), mimetype="image/png")
    resp.headers["Cache-Control"] = "no-store"
    return resp


@app.route("/tema.css")
def tema_css():
    return Response(TEMA.css(), mimetype="text/css", headers={"Cache-Control": "no-cache"})


@app.route("/tema/<name>")
def tema_file(name):
    name = os.path.basename(name)
    if name not in TEMA.nama_berkas() or not os.path.isfile(os.path.join(TEMA_DIR, name)):
        abort(404)
    resp = send_from_directory(TEMA_DIR, name)
    resp.headers["Cache-Control"] = "public, max-age=86400"  # nama berkas unik per unggahan
    resp.headers["X-Content-Type-Options"] = "nosniff"
    return resp


@app.route("/api/admin/tema", methods=["GET", "POST"])
@izin_required("tema")
def api_admin_tema():
    if request.method == "GET":
        return jsonify(ok=True, tema=TEMA.get(), preset=TEMA_PRESET, font=TEMA_FONT, ukuran=list(TEMA_UKURAN),
                       dasar=TEMA_DASAR, batas_mb=TEMA_BATAS_MB)
    try:
        d = json.loads(request.form.get("data", "{}"))
        hapus = [k for k in (d.get("hapus") or []) if k in ("logo", "login_bg", "wallpaper")]
        gambar = {}
        for jenis in ("logo", "login_bg", "wallpaper"):
            f = request.files.get(jenis)
            if f and f.filename:
                gambar[jenis] = f.read()
        TEMA.perbarui(d, hapus, gambar)
    except ValueError as e:
        return jsonify(ok=False, error=str(e)), 400
    except Exception:
        return jsonify(ok=False, error="Data tidak valid"), 400
    return jsonify(ok=True)


@app.route("/api/admin/tema/reset", methods=["POST"])
@izin_required("tema")
def api_admin_tema_reset():
    TEMA.reset()
    return jsonify(ok=True)


@app.route("/api/users")
@login_required
def api_users():
    sess = SESSIONS[session["u"]]
    try:
        return jsonify(ok=True, users=users_list(sess))
    except Exception as e:
        return jsonify(ok=False, error=str(e)), 502


@app.route("/api/admin/peran")
@izin_required("peran")
def api_peran():
    sess = SESSIONS[session["u"]]
    try:
        users = users_list(sess)
    except Exception as e:
        return jsonify(ok=False, error=str(e)), 502
    snap = PERAN.snapshot()
    efektif = {u: PERAN.peran_user(u) for u in users}
    return jsonify(ok=True, izin=IZIN, peran=snap["peran"], user=efektif, tetap=list(PERAN_TETAP),
                   admin_apps={u: True for u in users if SESSIONS.get(u) and SESSIONS[u].admin})


@app.route("/api/admin/peran/simpan", methods=["POST"])
@izin_required("peran")
def api_peran_simpan():
    d = request.get_json(silent=True) or {}
    nama = re.sub(r"\s+", " ", str(d.get("nama", ""))).strip()[:30]
    pid = re.sub(r"[^a-z0-9_]+", "_", str(d.get("id") or nama).lower()).strip("_")[:30]
    if not nama or not pid:
        return jsonify(ok=False, error="Nama peran wajib diisi"), 400
    izin = [i for i in (d.get("izin") or []) if i in IZIN]
    ok_, err = PERAN.simpan_peran(pid, nama, izin)
    if not ok_:
        return jsonify(ok=False, error=err), 400
    for u in PERAN.user_dengan(pid) + (list(SESSIONS) if pid == "operator" else []):
        bump(u)
    return jsonify(ok=True, id=pid)


@app.route("/api/admin/peran/hapus", methods=["POST"])
@izin_required("peran")
def api_peran_hapus():
    pid = str((request.get_json(silent=True) or {}).get("id", ""))
    terdampak = PERAN.user_dengan(pid)
    ok_, err = PERAN.hapus_peran(pid)
    if not ok_:
        return jsonify(ok=False, error=err), 400
    for u in terdampak:
        bump(u)
    return jsonify(ok=True)


@app.route("/api/admin/peran/user", methods=["POST"])
@izin_required("peran")
def api_peran_user():
    d = request.get_json(silent=True) or {}
    u = str(d.get("user", "")).strip()
    pid = str(d.get("peran", "")).strip()
    sess = SESSIONS[session["u"]]
    try:
        if u not in users_list(sess):
            return jsonify(ok=False, error="User tidak ada di USER_CLIENT"), 400
    except Exception as e:
        return jsonify(ok=False, error=str(e)), 502
    if u == session["u"] and not is_admin(u) and "peran" not in PERAN.snapshot()["peran"].get(pid, {}).get("izin", []):
        return jsonify(ok=False, error="Anda tidak bisa mencabut izin kelola peran dari akun sendiri"), 400
    if not PERAN.set_user(u, pid):
        return jsonify(ok=False, error="Peran tidak dikenal"), 400
    bump(u)
    return jsonify(ok=True)


@app.route("/api/assign", methods=["POST"])
@login_required
def api_assign():
    sess = SESSIONS[session["u"]]
    if not punya(session["u"], "tetapkan"):
        return jsonify(ok=False, error="Peran Anda tidak boleh menetapkan pemilik chat"), 403
    d = request.get_json(silent=True) or {}
    chat = str(d.get("chat", "")).strip()[:200]
    target = str(d.get("user", "")).strip()
    if not chat or not STORE.has_chat(chat):
        return jsonify(ok=False, error="Chat tidak dikenal"), 400
    if target:
        try:
            if target not in users_list(sess):
                return jsonify(ok=False, error="User tidak ada di USER_CLIENT"), 400
        except Exception as e:
            return jsonify(ok=False, error=str(e)), 502
    lama = OWN.get(chat)
    OWN.set(chat, target)
    bump(lama)
    bump(target)
    return jsonify(ok=True)


def ip_lokal():
    sk = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
    try:
        sk.connect(("10.255.255.255", 1))
        return sk.getsockname()[0]
    except Exception:
        return "127.0.0.1"
    finally:
        sk.close()


def minta_login():
    """Jendela login server. Return Session bila berhasil, None bila dibatalkan."""
    import tkinter as tk
    from tkinter import messagebox

    hasil = {}
    win = tk.Tk()
    win.title("Login WhatsApp Server")
    win.geometry("320x240")
    win.resizable(False, False)
    try:
        with open(LAST_USER_FILE, "r", encoding="utf-8") as f:
            last = f.read().strip()
    except Exception:
        last = ""

    tk.Label(win, text="Login Server", font=("Segoe UI", 13, "bold")).pack(pady=(14, 2))
    tk.Label(win, text="Akun ini dipakai untuk mencatat pesan masuk (INBOX)",
             fg="#555", wraplength=280).pack()
    tk.Label(win, text="Username").pack(anchor="w", padx=30, pady=(10, 0))
    eu = tk.Entry(win)
    eu.pack(fill="x", padx=30)
    eu.insert(0, last)
    tk.Label(win, text="Password").pack(anchor="w", padx=30, pady=(6, 0))
    ep = tk.Entry(win, show="*")
    ep.pack(fill="x", padx=30)

    def masuk(event=None):
        u, p = eu.get().strip(), ep.get()
        if not u or not p:
            return
        btn.config(state="disabled", text="Memeriksa...")
        win.update_idletasks()
        try:
            res = api({"action": "login", "username": u, "password": p})
        except Exception as e:
            res = {"ok": False, "error": f"Gagal terhubung ke Apps Script: {e}"}
        btn.config(state="normal", text="Masuk")
        if not res.get("ok"):
            messagebox.showerror("Login gagal", res.get("error", "Tidak diketahui"), parent=win)
            return
        try:
            with open(LAST_USER_FILE, "w", encoding="utf-8") as f:
                f.write(res["username"])
        except Exception:
            pass
        hasil["s"] = Session(res["username"], p, res["token"])
        win.destroy()

    btn = tk.Button(win, text="Masuk", command=masuk)
    btn.pack(pady=14, fill="x", padx=30)
    ep.bind("<Return>", masuk)
    eu.bind("<Return>", lambda e: ep.focus())
    (ep if last else eu).focus()
    win.mainloop()
    return hasil.get("s")


def main():
    global SERVER_SESSION, WEB_APP_URL
    import tkinter as tk
    import webbrowser
    from tkinter import messagebox, simpledialog
    from werkzeug.serving import make_server

    if not WEB_APP_URL.startswith("https://script.google.com/"):
        r0 = tk.Tk()
        r0.withdraw()
        url = (simpledialog.askstring(
            "Konfigurasi pertama kali",
            "Tempel URL Web App Apps Script (berakhiran /exec):", parent=r0) or "").strip()
        if not url.startswith("https://script.google.com/"):
            if url:
                messagebox.showerror("Konfigurasi", "URL tidak valid. Harus diawali "
                                     "https://script.google.com/ dan berakhiran /exec", parent=r0)
            r0.destroy()
            return
        r0.destroy()
        WEB_APP_URL = url
        simpan_config(WEB_APP_URL=url)

    sess = minta_login()
    if not sess:
        return
    SERVER_SESSION = sess

    root = tk.Tk()
    root.title("WhatsApp Server")
    root.geometry("460x230")
    root.resizable(False, False)

    try:
        srv = make_server(HOST, PORT, app, threaded=True)
    except OSError as e:
        messagebox.showerror("Port dipakai", f"Port {PORT} tidak bisa dipakai:\n{e}\n"
                             "Mungkin server sudah berjalan.")
        return

    WORKER.start()
    threading.Thread(target=srv.serve_forever, daemon=True).start()

    url_lokal = f"http://localhost:{PORT}"
    url_lan = f"http://{ip_lokal()}:{PORT}"

    tk.Label(root, text="WhatsApp Server berjalan", font=("Segoe UI", 12, "bold")).pack(pady=(12, 0))
    tk.Label(root, text=f"Login: {sess.username}", fg="#555").pack(pady=(0, 4))
    lbl = tk.Label(root, text="Status WhatsApp: ...", fg="#555")
    lbl.pack()
    tk.Label(root, text="Alamat untuk client lain (satu jaringan):").pack(pady=(10, 0))
    e = tk.Entry(root, justify="center", font=("Consolas", 11))
    e.insert(0, url_lan)
    e.config(state="readonly")
    e.pack(fill="x", padx=30)

    fr = tk.Frame(root)
    fr.pack(pady=12)

    def salin():
        root.clipboard_clear()
        root.clipboard_append(url_lan)

    def hentikan():
        if not messagebox.askyesno("Hentikan", "Hentikan server? Client lain akan terputus."):
            return
        WORKER.stop_ev.set()
        try:
            srv.shutdown()
        except Exception:
            pass
        WORKER.join(timeout=8)
        root.destroy()

    tk.Button(fr, text="Buka di browser", command=lambda: webbrowser.open(url_lokal)).pack(side="left", padx=4)
    tk.Button(fr, text="Salin alamat", command=salin).pack(side="left", padx=4)
    tk.Button(fr, text="Diagnosa", command=lambda: WORKER.cmd_q.put({"diag": True})).pack(side="left", padx=4)
    tk.Button(fr, text="Hentikan", command=hentikan).pack(side="left", padx=4)
    root.protocol("WM_DELETE_WINDOW", hentikan)

    def segar():
        lbl.config(text="Status WhatsApp: " + WORKER.status)
        root.after(1500, segar)

    segar()
    root.mainloop()


STOP_CMD = threading.Event()


def _baris_log(e):
    jam = e["time"][11:16]
    if e["type"] == "IN":
        return f"[{jam}] MASUK  {e.get('who', '')}: {(e.get('text') or ('[gambar]' if e.get('images') else ''))[:80]}"
    if e["type"] == "OUT":
        oleh = "otomatis: " + e["auto"] if e.get("auto") else (("jadwal: " if e.get("terjadwal") else "") + (e.get("user") or ""))
        isi = e.get("text") or ("[gambar]" if e.get("images") else "[file]" if e.get("files") else "")
        return f"[{jam}] KELUAR {e.get('who', '')} ({oleh}): {isi[:80]}"
    if e["type"] == "SYS":
        return f"[{jam}] SISTEM {e.get('text', '')[:150]}"
    return f"[{jam}] CATATAN {e.get('text', '')[:100]}"


def main_cmd(user=None, password=None):
    """Mode cmd/terminal: tanpa jendela GUI. Login lewat prompt, log tampil di layar."""
    global SERVER_SESSION, WEB_APP_URL
    import getpass
    from werkzeug.serving import make_server
    try:
        sys.stdout.reconfigure(encoding="utf-8", errors="replace")
    except Exception:
        pass
    print("=== WhatsApp Server (mode cmd) ===")
    if not WEB_APP_URL.startswith("https://script.google.com/"):
        url = input("Tempel URL Web App Apps Script (berakhiran /exec): ").strip()
        if not url.startswith("https://script.google.com/"):
            print("URL tidak valid.")
            return 1
        WEB_APP_URL = url
        simpan_config(WEB_APP_URL=url)
    try:
        with open(LAST_USER_FILE, "r", encoding="utf-8") as f:
            last = f.read().strip()
    except Exception:
        last = ""
    user = user or os.environ.get("WA_USER") or (input(f"Username{f' [{last}]' if last else ''}: ").strip() or last)
    password = password or os.environ.get("WA_PASS") or getpass.getpass("Password: ")
    try:
        res = api({"action": "login", "username": user, "password": password})
    except Exception as e:
        print("Gagal terhubung ke Apps Script:", e)
        return 1
    if not res.get("ok"):
        print("Login gagal:", res.get("error", "tidak diketahui"))
        return 1
    try:
        with open(LAST_USER_FILE, "w", encoding="utf-8") as f:
            f.write(res["username"])
    except Exception:
        pass
    SERVER_SESSION = Session(res["username"], password, res["token"], bool(res.get("admin")))
    try:
        srv = make_server(HOST, PORT, app, threaded=True)
    except OSError as e:
        print(f"Port {PORT} tidak bisa dipakai (mungkin server sudah berjalan): {e}")
        return 1
    threading.Thread(target=srv.serve_forever, daemon=True).start()
    WORKER.start()
    print(f"Login sebagai : {res['username']}")
    print(f"Alamat client : http://{ip_lokal()}:{PORT}   (di komputer ini: http://localhost:{PORT})")
    print("Chrome        : " + ("tersembunyi (headless)" if HEADLESS else "jendela terlihat"))
    print("Tekan Ctrl+C untuk berhenti.\n")
    status_lama, terakhir_id = None, STORE.next_id - 1
    try:
        while not STOP_CMD.is_set():
            if WORKER.status != status_lama:
                status_lama = WORKER.status
                print(f"[{datetime.now():%H:%M}] STATUS: {status_lama}")
            for e in STORE.after(terakhir_id):
                terakhir_id = e["id"]
                print(_baris_log(e))
            STOP_CMD.wait(1)
    except KeyboardInterrupt:
        pass
    print("\nMenghentikan server...")
    WORKER.stop_ev.set()
    try:
        srv.shutdown()
    except Exception:
        pass
    if WORKER.is_alive():
        WORKER.join(timeout=10)
    return 0


def _pastikan_konsol():
    """Exe 'windowed' / pythonw tidak punya jendela konsol, sehingga sys.stdin & sys.stdout kosong
    ('lost sys.stdin'). Di Windows, buka jendela konsol sendiri lalu sambungkan input/output ke sana."""
    if sys.stdin is not None and sys.stdout is not None:
        return True
    if os.name != "nt":
        return False
    try:
        import ctypes
        k32 = ctypes.windll.kernel32
        if not k32.GetConsoleWindow():
            k32.AllocConsole()
        sys.stdin = open("CONIN$", "r", encoding="utf-8", errors="replace")
        sys.stdout = open("CONOUT$", "w", encoding="utf-8", errors="replace", buffering=1)
        sys.stderr = sys.stdout
        return True
    except Exception:
        return False


if __name__ == "__main__":
    import argparse
    ap = argparse.ArgumentParser(description="WhatsApp Server (tanpa API resmi)")
    ap.add_argument("--cmd", action="store_true", help="jalan di cmd/terminal, tanpa jendela GUI")
    ap.add_argument("--headless", action="store_true", help="Chrome tersembunyi (tanpa jendela)")
    ap.add_argument("--tampil", action="store_true", help="tampilkan jendela Chrome (mis. untuk scan QR pertama kali)")
    ap.add_argument("--user", help="username login (atau env WA_USER)")
    ap.add_argument("--password", help="password login (disarankan pakai env WA_PASS / prompt)")
    args, _ = ap.parse_known_args()
    mode_cmd = args.cmd or "cmd" in os.path.basename(sys.executable).lower()
    if mode_cmd:
        _pastikan_konsol()
    if args.tampil:
        HEADLESS = False
    elif args.headless or mode_cmd:
        HEADLESS = True
        if mode_cmd and not args.headless and not os.path.isdir(PROFILE_DIR):
            HEADLESS = False  # pertama kali (belum login WhatsApp): tampilkan Chrome agar QR bisa dipindai
            print("Pertama kali dijalankan: jendela Chrome ditampilkan, scan QR WhatsApp di sana.")
    if mode_cmd:
        kode = 0
        try:
            kode = main_cmd(args.user, args.password)
        except KeyboardInterrupt:
            pass
        finally:
            if getattr(sys, "frozen", False):  # exe: tahan jendela agar pesan error sempat dibaca
                try:
                    input("\nTekan Enter untuk menutup...")
                except Exception:
                    pass
        raise SystemExit(kode)
    main()
