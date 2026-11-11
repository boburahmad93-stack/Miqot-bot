# -*- coding: utf-8 -*-
"""
Oshxona uchun Telegram bot + Mini App (professional buyurtma ilovasi).

- Mijoz: /start -> "🛍 Buyurtma berish" (Mini App) yoki oddiy chat orqali menyu/savat
- Har bir buyurtmada mijozning Telegram username va doimiy ID'si avtomatik yoziladi
- Egasi (OWNER_CHAT_ID): yangi buyurtma haqida xabar oladi, mijozga to'g'ridan-to'g'ri
  yozish tugmasi bilan, va holatni o'zgartiradi.

Admin buyruqlari (faqat OWNER_CHAT_ID uchun):
    /menu                 - menyudagi taomlar ro'yxati
    /add_dish             - Nomi;Narxi;Tavsif (rasmsiz)
    /remove_dish id        - taomni o'chirish
    RASM + "Nomi;Narxi;Tavsif" caption -> taom rasm bilan qo'shiladi
    RASM + "logo" caption -> bot va Mini App logotipi sifatida saqlanadi
"""

import json
import os
import re
import time
import threading
import hashlib
import hmac
import urllib.parse
from datetime import datetime, timedelta
from zoneinfo import ZoneInfo

import requests as httpreq
import telebot
from telebot import types
from flask import Flask, request, jsonify, send_from_directory

BOT_TOKEN = os.environ.get("BOT_TOKEN", "TOKEN_BU_YERGA")
OWNER_CHAT_ID = int(os.environ.get("OWNER_CHAT_ID", "0"))
WEBAPP_URL = os.environ.get("WEBAPP_URL", "").rstrip("/")
BUSINESS_NAME = os.environ.get("BUSINESS_NAME", "Miqot Food")
BUSINESS_TAGLINE = os.environ.get("BUSINESS_TAGLINE", "Halol lazzatli, barakali ne'mat")
TIMEZONE = ZoneInfo(os.environ.get("TIMEZONE", "Asia/Riyadh"))

DATA_DIR = os.environ.get("DATA_DIR", ".")
os.makedirs(DATA_DIR, exist_ok=True)

MENU_FILE = os.path.join(DATA_DIR, "menu.json")
ORDERS_FILE = os.path.join(DATA_DIR, "orders.json")
SETTINGS_FILE = os.path.join(DATA_DIR, "settings.json")
CASHBACK_FILE = os.path.join(DATA_DIR, "cashback.json")
ACCOUNT_FILE = os.path.join(DATA_DIR, "hisob.json")      # nasiya va avans
TGDRAFT_FILE = os.path.join(DATA_DIR, "tg_drafts.json")  # Telegramdan ko'chirilgan buyurtmalar
BIZSEEN_FILE = os.path.join(DATA_DIR, "biz_seen.json")   # shaxsiy chatda kimga qachon javob berilgan
WINBACK_FILE = os.path.join(DATA_DIR, "winback.json")

# ---------- mijozni qaytarish sozlamalari (oson o'zgartirish uchun shu yerda) ----------
SUB_OFFER_AFTER = int(os.environ.get("SUB_OFFER_AFTER", "3"))       # nechanchi buyurtmadan keyin obuna taklifi
SUB_OFFER_URL = os.environ.get("SUB_OFFER_URL", "https://t.me/miqot1oybot")
WINBACK_DAYS_1 = int(os.environ.get("WINBACK_DAYS_1", "7"))         # 1-bosqich: necha kundan keyin
WINBACK_DAYS_2 = int(os.environ.get("WINBACK_DAYS_2", "21"))        # 2-bosqich: necha kundan keyin
WINBACK_BONUS = float(os.environ.get("WINBACK_BONUS", "10"))        # 2-bosqichda beriladigan bonus (SAR)
WINBACK_HOUR = int(os.environ.get("WINBACK_HOUR", "12"))            # har kuni soat nechada tekshiriladi
REPEAT_MIN_TOTAL = float(os.environ.get("REPEAT_MIN_TOTAL", "30"))  # takrorlash uchun eng kam summa
DISH_PHOTOS_DIR = os.path.join(DATA_DIR, "static", "dishes")
LOGO_PATH = os.path.join(DATA_DIR, "static", "logo.jpg")

os.makedirs(DISH_PHOTOS_DIR, exist_ok=True)

bot = telebot.TeleBot(BOT_TOKEN)
app = Flask(__name__)
app.config["MAX_CONTENT_LENGTH"] = 12 * 1024 * 1024  # rasm uchun eng katta hajm: 12 MB

# ---------- fayl bilan ishlash ----------

def load_json(path, default):
    with DATA_LOCK:
        if not os.path.exists(path):
            return default
        try:
            with open(path, "r", encoding="utf-8") as f:
                return json.load(f)
        except Exception as e:
            print(f"{path} o'qishda xato: {e}")
            return default

# Bir vaqtda bir necha mijoz javob berganda ma'lumot buzilmasligi uchun qulf.
# Bot (polling) va Mini App (Flask) alohida oqimlarda ishlaydi — ikkalasi ham shu qulfdan foydalanadi.
DATA_LOCK = threading.RLock()

def save_json(path, data):
    """Avval vaqtinchalik faylga yozib, keyin almashtiramiz —
       yozish o'rtasida uzilib qolsa ham eski fayl butun qoladi."""
    tmp = path + ".tmp"
    with DATA_LOCK:
        with open(tmp, "w", encoding="utf-8") as f:
            json.dump(data, f, ensure_ascii=False, indent=2)
            f.flush()
            os.fsync(f.fileno())
        os.replace(tmp, path)

def load_menu():
    return load_json(MENU_FILE, [])

def save_menu(menu):
    save_json(MENU_FILE, menu)

def load_orders():
    return load_json(ORDERS_FILE, [])

def save_orders(orders):
    save_json(ORDERS_FILE, orders)

def load_settings():
    return load_json(SETTINGS_FILE, {})

def save_settings(s):
    save_json(SETTINGS_FILE, s)

def next_order_id(orders):
    return (max([o["id"] for o in orders], default=0)) + 1

def today_key(ts=None):
    dt = datetime.fromtimestamp(ts, TIMEZONE) if ts else datetime.now(TIMEZONE)
    return dt.strftime("%Y-%m-%d")

def next_daily_number(orders, day_key):
    same_day = [o for o in orders if o.get("day_key") == day_key]
    return len(same_day) + 1

def renumber_day(orders, day_key):
    """day_key kuniga tegishli buyurtmalarni 1,2,3... qilib qayta raqamlaydi (bo'shliqsiz)."""
    same_day = [o for o in orders if o.get("day_key") == day_key]
    same_day.sort(key=lambda o: o["id"])
    for i, o in enumerate(same_day, start=1):
        o["daily_number"] = i

carts = {}
checkout_state = {}

BUILDER_CATEGORY = "Taomni o'zingiz tayyorlang"   # mijoz o'zi yig'adigan taom
BUILDER_MIN_DEFAULT = 30                          # shundan kam bo'lsa qabul qilinmaydi

# Bo'lim nomi o'zgarsa, menyudagi eski mahsulotlar osilib qolmasligi uchun
BUILDER_OLD_NAMES = ["O'zingiz yig'ing"]

# Tartib muhim: shu ketma-ketlikda bo'limlar sahifasida va menyuda ko'rinadi
CATEGORIES = [BUILDER_CATEGORY, "Ovqatlar", "Nonushta", "Fast Food", "Salatlar",
              "Salqin ichimliklar", "Boshqa mahsulotlar"]
DEFAULT_CATEGORY = "Boshqa mahsulotlar"
CATEGORY_EMOJI = {
    "Nonushta": "🍳",
    "Ovqatlar": "🍲",
    "Fast Food": "🍔",
    "Salatlar": "🥗",
    BUILDER_CATEGORY: "🧑‍🍳",
    "Salqin ichimliklar": "🥤",
    "Boshqa mahsulotlar": "🍽",
}
# Qo'shimcha nomlar — admin "fastfood" yoki "fast-food" deb yozsa ham tushunadi
CATEGORY_ALIASES = {
    "fastfood": "Fast Food",
    "fast-food": "Fast Food",
    "fast food": "Fast Food",
    "ichimliklar": "Salqin ichimliklar",
    "boshqalar": "Boshqa mahsulotlar",
}


# ---------- set tarkibi (taom narxiga qo'shib beriladigan narsalar) ----------

SET_ITEMS = [
    {"key": "non",    "emoji": "🥖",
     "uz": "non", "ar": "خبز", "en": "bread", "ru": "хлеб",
     "tr": "ekmek", "ur": "روٹی", "id": "roti"},
    {"key": "salat",  "emoji": "🥗",
     "uz": "salat", "ar": "سلطة", "en": "salad", "ru": "салат",
     "tr": "salata", "ur": "سلاد", "id": "salad"},
    {"key": "meva",   "emoji": "🍓",
     "uz": "meva salat", "ar": "سلطة فواكه", "en": "fruit salad",
     "ru": "фруктовый салат",
     "tr": "meyve salatası", "ur": "فروٹ سلاد", "id": "salad buah"},
    {"key": "suv",    "emoji": "💧",
     "uz": "suv", "ar": "ماء", "en": "water", "ru": "вода",
     "tr": "su", "ur": "پانی", "id": "air"},
    {"key": "choy",   "emoji": "🍵",
     "uz": "choy", "ar": "شاي", "en": "tea", "ru": "чай",
     "tr": "çay", "ur": "چائے", "id": "teh"},
    {"key": "shorva", "emoji": "🥣",
     "uz": "shorva", "ar": "شوربة", "en": "soup", "ru": "суп",
     "tr": "çorba", "ur": "سوپ", "id": "sup"},
    {"key": "souse",  "emoji": "🧄",
     "uz": "souse", "ar": "صلصة", "en": "sauce", "ru": "соус",
     "tr": "sos", "ur": "ساس", "id": "saus"},
]
SET_BY_KEY = {s["key"]: s for s in SET_ITEMS}
SET_KEYS = [s["key"] for s in SET_ITEMS]

def set_catalog_payload():
    """Mini App va admin paneliga yuboriladigan katalog."""
    return [{"key": s["key"], "emoji": s["emoji"],
             "names": {l: s.get(l) or s["uz"] for l in SUPPORTED_LANGS}}
            for s in SET_ITEMS]

def parse_set_keys(raw):
    """'non,salat,suv' yoki ro'yxatni toza kalitlar ro'yxatiga aylantiradi."""
    if not raw:
        return []
    if isinstance(raw, str):
        parts = raw.replace("+", ",").replace(";", ",").split(",")
    else:
        parts = list(raw)
    out = []
    for p in parts:
        k = str(p).strip().lower()
        if k in SET_BY_KEY and k not in out:
            out.append(k)
    return out

def dish_set_keys(dish):
    return parse_set_keys((dish or {}).get("set_items"))

def set_names(keys, extra="", lang="uz", with_emoji=False):
    """Set tarkibini mijoz tilida nomlar ro'yxati qilib qaytaradi."""
    out = []
    for k in parse_set_keys(keys):
        s = SET_BY_KEY[k]
        nom = s.get(lang) or s["uz"]
        out.append(f"{s['emoji']} {nom}" if with_emoji else nom)
    for piece in str(extra or "").split(","):
        piece = piece.strip()
        if piece:
            out.append(piece)
    return out

def set_line(keys, extra="", lang="uz", sep=" · ", with_emoji=False):
    return sep.join(set_names(keys, extra, lang, with_emoji))

def item_set_line(item, lang="uz", sep=" · ", with_emoji=False):
    """Buyurtmadagi taom uchun — set buyurtma paytida yozib qo'yilgan."""
    return set_line(item.get("set"), item.get("set_extra"), lang, sep, with_emoji)

def match_category(raw):
    if not raw:
        return DEFAULT_CATEGORY
    raw = raw.strip().lower()
    for c in CATEGORIES:
        if c.lower() == raw:
            return c
    if raw in CATEGORY_ALIASES:
        return CATEGORY_ALIASES[raw]
    return None

def load_admin_ids():
    settings = load_settings()
    ids = set(settings.get("admin_ids", []))
    ids.add(OWNER_CHAT_ID)
    return ids

def add_admin_id(new_id):
    settings = load_settings()
    ids = set(settings.get("admin_ids", []))
    ids.add(OWNER_CHAT_ID)
    ids.add(new_id)
    settings["admin_ids"] = list(ids)
    save_settings(settings)

def remove_admin_id(rem_id):
    settings = load_settings()
    ids = set(settings.get("admin_ids", []))
    ids.discard(rem_id)
    settings["admin_ids"] = list(ids)
    save_settings(settings)

def load_staff_ids():
    settings = load_settings()
    return set(settings.get("staff_ids", []))

def add_staff_id(new_id):
    settings = load_settings()
    ids = set(settings.get("staff_ids", []))
    ids.add(new_id)
    settings["staff_ids"] = list(ids)
    save_settings(settings)

def remove_staff_id(rem_id):
    settings = load_settings()
    ids = set(settings.get("staff_ids", []))
    ids.discard(rem_id)
    settings["staff_ids"] = list(ids)
    save_settings(settings)

# ---------- tillar ----------

LANG_FILE = os.path.join(DATA_DIR, "user_lang.json")
SUPPORTED_LANGS = ["uz", "ar", "en", "ru", "tr", "ur", "id"]
LANG_NAMES = {
    "uz": "🇺🇿 O'zbekcha", "ar": "🇸🇦 العربية", "en": "🇬🇧 English",
    "ru": "🇷🇺 Русский", "tr": "🇹🇷 Türkçe", "ur": "🇵🇰 اردو", "id": "🇮🇩 Indonesia",
}
# Telegram til kodini bizdagi tilga moslash
LANG_ALIASES = {
    "ms": "id", "az": "tr", "kk": "ru", "ky": "ru", "tg": "ru", "tk": "ru",
    "hi": "ur", "pa": "ur", "fa": "ar",
}

def load_user_langs():
    return load_json(LANG_FILE, {})

def set_user_lang(user_id, lang):
    if lang not in SUPPORTED_LANGS:
        return
    data = load_user_langs()
    data[str(user_id)] = lang
    save_json(LANG_FILE, data)

DEFAULT_LANG = "uz"

def lang_hint(lang):
    """Boshqa tilda o'qiydigan mijoz tilni qayerdan o'zgartirishni bilsin."""
    if lang != DEFAULT_LANG:
        return ""
    return "\n\n🌐 اللغة · Язык · Language → /til"

def get_user_lang(user_id, tg_code=None):
    """Mijoz o'zi tanlagan til, tanlamagan bo'lsa — o'zbekcha.

    Telefon tiliga qaramaymiz: mijozlarimizning ko'pchiligi telefonini
    ingliz yoki rus tilida ishlatadi, lekin o'sha tillarni bilmaydi.
    Xohlagan odam «Til» tugmasidan o'zgartirib oladi.
    """
    if user_id:
        saved = load_user_langs().get(str(user_id))
        if saved in SUPPORTED_LANGS:
            return saved
    return DEFAULT_LANG

TEXTS = {
    "welcome": {
        "uz": "Assalomu alaykum! 👋\n{biz}ga xush kelibsiz.\n\n🍽 Menyu va narxlarni ko'rish uchun pastdagi tugmani bosing 👇\nTanlab, o'sha yerning o'zidan buyurtma berasiz.",
        "ar": "السلام عليكم! 👋\nمرحبًا بك في {biz}.\n\n🍽 لعرض القائمة والأسعار اضغط الزر بالأسفل 👇\nاختر ما تريد وأرسل طلبك من نفس المكان.",
        "en": "Hello! 👋\nWelcome to {biz}.\n\n🍽 Tap the button below to see the menu and prices 👇\nPick what you want and order right there.",
        "ru": "Здравствуйте! 👋\nДобро пожаловать в {biz}.\n\n🍽 Нажмите кнопку ниже, чтобы посмотреть меню и цены 👇\nВыбирайте и заказывайте прямо там.",
        "tr": "Merhaba! 👋\n{biz}'a hoş geldiniz.\n\n🍽 Menü ve fiyatları görmek için aşağıdaki butona basın 👇\nSeçin ve siparişinizi oradan verin.",
        "ur": "السلام علیکم! 👋\n{biz} میں خوش آمدید۔\n\n🍽 مینو اور قیمتیں دیکھنے کے لیے نیچے والا بٹن دبائیں 👇\nپسند کریں اور وہیں سے آرڈر دیں۔",
        "id": "Halo! 👋\nSelamat datang di {biz}.\n\n🍽 Tekan tombol di bawah untuk melihat menu dan harga 👇\nPilih dan pesan langsung di sana.",
    },
    "btn_order": {
        "uz": "🍽 Menyu va narxlar", "ar": "🍽 القائمة والأسعار", "en": "🍽 Menu & prices",
        "ru": "🍽 Меню и цены", "tr": "🍽 Menü ve fiyatlar", "ur": "🍽 مینو اور قیمتیں",
        "id": "🍽 Menu & harga",
    },
    "menu_hint": {
        "uz": "🍽 Menyu va narxlar pastdagi tugmada 👇\nUni bosing — taomlar rasmi va narxi bilan chiqadi, o'sha yerdan buyurtma berasiz.",
        "ar": "🍽 القائمة والأسعار في الزر بالأسفل 👇\nاضغط عليه — ستظهر الأطباق بالصور والأسعار، وتطلب من هناك مباشرة.",
        "en": "🍽 The menu and prices are in the button below 👇\nTap it — you'll see the dishes with photos and prices, and you order right there.",
        "ru": "🍽 Меню и цены — в кнопке ниже 👇\nНажмите её: блюда с фото и ценами, оттуда же и заказ.",
        "tr": "🍽 Menü ve fiyatlar aşağıdaki butonda 👇\nBasın — yemekler fotoğraf ve fiyatlarıyla görünür, siparişi oradan verirsiniz.",
        "ur": "🍽 مینو اور قیمتیں نیچے والے بٹن میں ہیں 👇\nاسے دبائیں — کھانے تصویر اور قیمت کے ساتھ نظر آئیں گے، وہیں سے آرڈر کریں۔",
        "id": "🍽 Menu dan harga ada di tombol bawah 👇\nTekan — menu tampil dengan foto dan harga, pesan langsung di sana.",
    },
    "btn_contact": {
        "uz": "💬 Biz bilan bog'lanish", "ar": "💬 تواصل معنا", "en": "💬 Contact us",
        "ru": "💬 Связаться с нами", "tr": "💬 Bize ulaşın", "ur": "💬 ہم سے رابطہ", "id": "💬 Hubungi kami",
    },
    "btn_my_account": {
        "uz": "\U0001F4D2 Mening hisobim", "ar": "\U0001F4D2 \u062d\u0633\u0627\u0628\u064a",
        "en": "\U0001F4D2 My account", "ru": "\U0001F4D2 \u041c\u043e\u0439 \u0441\u0447\u0451\u0442",
        "tr": "\U0001F4D2 Hesab\u0131m", "ur": "\U0001F4D2 \u0645\u06cc\u0631\u0627 \u0627\u06a9\u0627\u0624\u0646\u0679",
        "id": "\U0001F4D2 Akun saya",
    },
    "btn_lang": {
        "uz": "🌐 Til", "ar": "🌐 اللغة", "en": "🌐 Language",
        "ru": "🌐 Язык", "tr": "🌐 Dil", "ur": "🌐 زبان", "id": "🌐 Bahasa",
    },
    "contact_prompt": {
        "uz": "✍️ Savolingiz yoki fikringizni shu yerga yozing — tez orada javob beramiz.",
        "ar": "✍️ اكتب سؤالك أو ملاحظتك هنا — سنرد عليك قريبًا.",
        "en": "✍️ Write your question or feedback here — we'll reply shortly.",
        "ru": "✍️ Напишите ваш вопрос или отзыв здесь — мы скоро ответим.",
        "tr": "✍️ Sorunuzu veya görüşünüzü buraya yazın — kısa sürede yanıtlayacağız.",
        "ur": "✍️ اپنا سوال یا رائے یہاں لکھیں — ہم جلد جواب دیں گے۔",
        "id": "✍️ Tulis pertanyaan atau masukan Anda di sini — kami akan segera membalas.",
    },
    "msg_received": {
        "uz": "✅ Xabaringiz qabul qilindi, tez orada javob beramiz.",
        "ar": "✅ تم استلام رسالتك، سنرد قريبًا.",
        "en": "✅ We got your message, we'll reply shortly.",
        "ru": "✅ Сообщение получено, скоро ответим.",
        "tr": "✅ Mesajınız alındı, kısa sürede yanıtlayacağız.",
        "ur": "✅ آپ کا پیغام موصول ہوا، ہم جلد جواب دیں گے۔",
        "id": "✅ Pesan Anda kami terima, segera kami balas.",
    },
    "reply_from": {
        "uz": "💬 {biz}dan javob:", "ar": "💬 رد من {biz}:", "en": "💬 Reply from {biz}:",
        "ru": "💬 Ответ от {biz}:", "tr": "💬 {biz}'dan yanıt:", "ur": "💬 {biz} کی طرف سے جواب:",
        "id": "💬 Balasan dari {biz}:",
    },
    "ask_name": {
        "uz": "Ismingizni kiriting:", "ar": "اكتب اسمك:", "en": "Enter your name:",
        "ru": "Введите ваше имя:", "tr": "Adınızı girin:", "ur": "اپنا نام لکھیں:", "id": "Masukkan nama Anda:",
    },
    "ask_phone": {
        "uz": "Telefon raqamingiz:\n\nPastdagi tugma orqali yuborishingiz, qo'lda yozishingiz (istalgan davlat raqami bo'ladi), yoki raqamingiz bo'lmasa \"Raqamim yo'q\" tugmasini bosishingiz mumkin — u holda siz bilan shu bot orqali bog'lanamiz.",
        "ar": "رقم هاتفك:\n\nيمكنك إرساله بالزر بالأسفل، أو كتابته يدويًا (أي دولة)، أو الضغط على \"ليس لدي رقم\" — وعندها سنتواصل معك عبر هذا البوت.",
        "en": "Your phone number:\n\nSend it with the button below, type it manually (any country), or tap \"No number\" — then we'll reach you through this bot.",
        "ru": "Ваш номер телефона:\n\nОтправьте кнопкой ниже, напишите вручную (любая страна) или нажмите «Нет номера» — тогда свяжемся через этого бота.",
        "tr": "Telefon numaranız:\n\nAşağıdaki butonla gönderin, elle yazın (herhangi bir ülke) veya \"Numaram yok\" deyin — o zaman bu bot üzerinden ulaşırız.",
        "ur": "آپ کا فون نمبر:\n\nنیچے والے بٹن سے بھیجیں، خود لکھیں (کوئی بھی ملک)، یا \"نمبر نہیں ہے\" دبائیں — پھر ہم اسی بوٹ سے رابطہ کریں گے۔",
        "id": "Nomor telepon Anda:\n\nKirim lewat tombol di bawah, ketik manual (negara mana pun), atau pilih \"Tidak punya nomor\" — kami akan menghubungi lewat bot ini.",
    },
    "btn_send_phone": {
        "uz": "📞 Raqamimni yuborish", "ar": "📞 إرسال رقمي", "en": "📞 Send my number",
        "ru": "📞 Отправить номер", "tr": "📞 Numaramı gönder", "ur": "📞 میرا نمبر بھیجیں", "id": "📞 Kirim nomor saya",
    },
    "btn_no_phone": {
        "uz": "📱 Raqamim yo'q — Telegram orqali", "ar": "📱 ليس لدي رقم — عبر تيليجرام",
        "en": "📱 No number — via Telegram", "ru": "📱 Нет номера — через Telegram",
        "tr": "📱 Numaram yok — Telegram'dan", "ur": "📱 نمبر نہیں — ٹیلیگرام پر",
        "id": "📱 Tidak punya nomor — via Telegram",
    },
    "ask_address": {
        "uz": "Endi joylashuvingizni yuboring 📍\nPastdagi tugmani bosing (eng aniq usul) — yoki manzilni yozib yuborishingiz ham mumkin.",
        "ar": "الآن أرسل موقعك 📍\nاضغط الزر بالأسفل (الأدق) — أو اكتب العنوان.",
        "en": "Now send your location 📍\nTap the button below (most accurate) — or type your address.",
        "ru": "Теперь отправьте местоположение 📍\nНажмите кнопку ниже (точнее всего) — или напишите адрес.",
        "tr": "Şimdi konumunuzu gönderin 📍\nAşağıdaki butona basın (en doğrusu) — veya adresi yazın.",
        "ur": "اب اپنی لوکیشن بھیجیں 📍\nنیچے والا بٹن دبائیں (سب سے درست) — یا پتہ لکھیں۔",
        "id": "Sekarang kirim lokasi Anda 📍\nTekan tombol di bawah (paling akurat) — atau tulis alamat.",
    },
    "btn_location": {
        "uz": "📍 Joylashuvimni yuborish", "ar": "📍 إرسال موقعي", "en": "📍 Send my location",
        "ru": "📍 Отправить местоположение", "tr": "📍 Konumumu gönder",
        "ur": "📍 میری لوکیشن بھیجیں", "id": "📍 Kirim lokasi saya",
    },
    "receipt_title": {
        "uz": "✅ Buyurtmangiz qabul qilindi! (#{no})", "ar": "✅ تم استلام طلبك! (رقم {no})",
        "en": "✅ Your order is received! (#{no})", "ru": "✅ Заказ принят! (№{no})",
        "tr": "✅ Siparişiniz alındı! (#{no})", "ur": "✅ آپ کا آرڈر موصول ہوا! (#{no})",
        "id": "✅ Pesanan Anda diterima! (#{no})",
    },
    "receipt_total": {
        "uz": "💰 Jami: {sum} (naqd — yetkazib berilganda)",
        "ar": "💰 الإجمالي: {sum} (نقدًا عند الاستلام)",
        "en": "💰 Total: {sum} (cash on delivery)",
        "ru": "💰 Итого: {sum} (наличными при доставке)",
        "tr": "💰 Toplam: {sum} (teslimatta nakit)",
        "ur": "💰 کل: {sum} (ڈیلیوری پر نقد)",
        "id": "💰 Total: {sum} (tunai saat pengantaran)",
    },
    "receipt_total_plain": {
        "uz": "\U0001F4B0 Jami: {sum}",
        "ar": "\U0001F4B0 \u0627\u0644\u0625\u062c\u0645\u0627\u0644\u064a: {sum}",
        "en": "\U0001F4B0 Total: {sum}",
        "ru": "\U0001F4B0 \u0418\u0442\u043e\u0433\u043e: {sum}",
        "tr": "\U0001F4B0 Toplam: {sum}",
        "ur": "\U0001F4B0 \u06a9\u0644: {sum}",
        "id": "\U0001F4B0 Total: {sum}",
    },
    "receipt_nophone": {
        "uz": "\n📱 Telefon raqami kiritilmadi — siz bilan shu bot orqali bog'lanamiz. Xabarlarni kuzatib turing.",
        "ar": "\n📱 لم يُدخل رقم هاتف — سنتواصل معك عبر هذا البوت. تابع الرسائل.",
        "en": "\n📱 No phone number given — we'll reach you through this bot. Please watch for messages.",
        "ru": "\n📱 Номер не указан — свяжемся через этого бота. Следите за сообщениями.",
        "tr": "\n📱 Numara girilmedi — bu bot üzerinden ulaşacağız. Mesajları takip edin.",
        "ur": "\n📱 فون نمبر نہیں دیا گیا — ہم اسی بوٹ سے رابطہ کریں گے۔ پیغامات دیکھتے رہیں۔",
        "id": "\n📱 Nomor tidak diisi — kami hubungi lewat bot ini. Pantau pesannya.",
    },
    "receipt_tail": {
        "uz": "\nTez orada siz bilan bog'lanamiz. Holat o'zgarganda sizga xabar boradi.",
        "ar": "\nسنتواصل معك قريبًا. وسنخبرك عند تغيّر حالة الطلب.",
        "en": "\nWe'll contact you shortly. You'll be notified when the status changes.",
        "ru": "\nСкоро свяжемся с вами. Сообщим об изменении статуса.",
        "tr": "\nKısa sürede sizinle iletişime geçeceğiz. Durum değişince haber vereceğiz.",
        "ur": "\nہم جلد رابطہ کریں گے۔ حالت بدلنے پر آپ کو اطلاع دی جائے گی۔",
        "id": "\nKami akan segera menghubungi. Anda akan diberi tahu bila status berubah.",
    },
    "discount_line": {
        "uz": "🏷 Aksiya −{pct}%: {old} → {new}\n",
        "ar": "🏷 خصم −{pct}%: {old} ← {new}\n",
        "en": "🏷 Discount −{pct}%: {old} → {new}\n",
        "ru": "🏷 Акция −{pct}%: {old} → {new}\n",
        "tr": "🏷 İndirim −{pct}%: {old} → {new}\n",
        "ur": "🏷 رعایت −{pct}%: {old} ← {new}\n",
        "id": "🏷 Diskon −{pct}%: {old} → {new}\n",
    },
    "sale_badge": {
        "uz": "AKSIYA", "ar": "خصم", "en": "SALE", "ru": "АКЦИЯ",
        "tr": "İNDİRİM", "ur": "رعایت", "id": "DISKON",
    },
    "closed_today": {
        "uz": "Assalomu alaykum! 🌙\nBugun ish kunimiz emas — buyurtma qabul qilinmaydi.\n\nIsh faoliyatimiz tiklanganda sizni yangi buyurtmalar bilan kutib qolamiz. Rahmat!",
        "ar": "السلام عليكم! 🌙\nاليوم إجازة — لا نستقبل الطلبات.\n\nننتظر طلباتكم عند استئناف العمل. شكرًا لكم!",
        "en": "Hello! 🌙\nWe're closed today — orders aren't being accepted.\n\nWe'll be glad to welcome your orders when we reopen. Thank you!",
        "ru": "Здравствуйте! 🌙\nСегодня у нас выходной — заказы не принимаются.\n\nБудем рады вашим заказам, когда снова откроемся. Спасибо!",
        "tr": "Merhaba! 🌙\nBugün kapalıyız — sipariş alınmıyor.\n\nYeniden açıldığımızda siparişlerinizi bekliyoruz. Teşekkürler!",
        "ur": "السلام علیکم! 🌙\nآج ہماری چھٹی ہے — آرڈر وصول نہیں کیے جا رہے۔\n\nدوبارہ کھلنے پر آپ کے آرڈرز کے منتظر رہیں گے۔ شکریہ!",
        "id": "Halo! 🌙\nHari ini kami tutup — pesanan tidak diterima.\n\nKami menanti pesanan Anda saat buka kembali. Terima kasih!",
    },
    "closed_hours": {
        "uz": "Assalomu alaykum! 🌙\nIsh vaqtimiz tugadi — hozircha buyurtma qabul qilinmaydi.\n\n🕒 Ish vaqtimiz: {open} — {close}\nSizdan {open} dan boshlab yangi buyurtmalar kutib qolamiz. Rahmat!",
        "ar": "السلام عليكم! 🌙\nانتهى دوام العمل — لا نستقبل الطلبات حاليًا.\n\n🕒 ساعات العمل: {open} — {close}\nننتظر طلباتكم ابتداءً من {open}. شكرًا لكم!",
        "en": "Hello! 🌙\nWe're closed for the day — orders aren't being accepted right now.\n\n🕒 Working hours: {open} — {close}\nWe'll welcome your orders from {open}. Thank you!",
        "ru": "Здравствуйте! 🌙\nРабочий день закончился — заказы сейчас не принимаются.\n\n🕒 Часы работы: {open} — {close}\nЖдём ваши заказы с {open}. Спасибо!",
        "tr": "Merhaba! 🌙\nÇalışma saatimiz sona erdi — şu an sipariş alınmıyor.\n\n🕒 Çalışma saatleri: {open} — {close}\nSiparişlerinizi {open}'dan itibaren bekliyoruz. Teşekkürler!",
        "ur": "السلام علیکم! 🌙\nہمارا کام کا وقت ختم ہو گیا — فی الحال آرڈر وصول نہیں کیے جا رہے۔\n\n🕒 اوقاتِ کار: {open} — {close}\n{open} سے آپ کے آرڈرز کے منتظر ہیں۔ شکریہ!",
        "id": "Halo! 🌙\nJam kerja kami sudah berakhir — pesanan belum diterima saat ini.\n\n🕒 Jam buka: {open} — {close}\nKami menanti pesanan Anda mulai {open}. Terima kasih!",
    },
    "closed_short": {
        "uz": "Hozir yopiqmiz — buyurtma qabul qilinmaydi.",
        "ar": "نحن مغلقون الآن — لا نستقبل الطلبات.",
        "en": "We're closed right now — orders aren't accepted.",
        "ru": "Сейчас закрыто — заказы не принимаются.",
        "tr": "Şu an kapalıyız — sipariş alınmıyor.",
        "ur": "ہم اس وقت بند ہیں — آرڈر وصول نہیں کیے جا رہے۔",
        "id": "Kami sedang tutup — pesanan tidak diterima.",
    },
    "order_cancelled": {
        "uz": "❌ Buyurtmangiz #{no} bekor qilindi.\n\nNoqulaylik uchun uzr so'raymiz. Savolingiz bo'lsa shu yerga yozing — javob beramiz.",
        "ar": "❌ تم إلغاء طلبك رقم {no}.\n\nنعتذر عن الإزعاج. إذا كان لديك سؤال اكتب لنا هنا.",
        "en": "❌ Your order #{no} has been cancelled.\n\nSorry for the inconvenience. Write to us here if you have any questions.",
        "ru": "❌ Ваш заказ №{no} отменён.\n\nПриносим извинения. Если есть вопросы — напишите нам сюда.",
        "tr": "❌ #{no} numaralı siparişiniz iptal edildi.\n\nVerdiğimiz rahatsızlık için özür dileriz. Sorunuz olursa buraya yazın.",
        "ur": "❌ آپ کا آرڈر #{no} منسوخ کر دیا گیا ہے۔\n\nتکلیف کے لیے معذرت۔ کوئی سوال ہو تو یہیں لکھیں۔",
        "id": "❌ Pesanan Anda #{no} dibatalkan.\n\nMohon maaf atas ketidaknyamanannya. Ada pertanyaan? Tulis di sini.",
    },
    "order_restored": {
        "uz": "♻️ Buyurtmangiz #{no} qayta tiklandi — tayyorlanmoqda.",
        "ar": "♻️ تمت إعادة طلبك رقم {no} — جارٍ التحضير.",
        "en": "♻️ Your order #{no} has been restored — we're preparing it.",
        "ru": "♻️ Ваш заказ №{no} восстановлен — готовим.",
        "tr": "♻️ #{no} numaralı siparişiniz geri alındı — hazırlanıyor.",
        "ur": "♻️ آپ کا آرڈر #{no} بحال کر دیا گیا — تیار ہو رہا ہے۔",
        "id": "♻️ Pesanan Anda #{no} dipulihkan — sedang disiapkan.",
    },
    "item_cancelled": {
        "uz": "ℹ️ Buyurtmangiz #{no} o'zgardi.\n\n«{dish}» olib tashlandi.\n💰 Yangi summa: {sum}\n\nSavolingiz bo'lsa shu yerga yozing.",
        "ar": "ℹ️ تم تعديل طلبك رقم {no}.\n\nتمت إزالة «{dish}».\n💰 المبلغ الجديد: {sum}\n\nإذا كان لديك سؤال اكتب لنا هنا.",
        "en": "ℹ️ Your order #{no} has changed.\n\n\"{dish}\" was removed.\n💰 New total: {sum}\n\nWrite to us here if you have questions.",
        "ru": "ℹ️ Ваш заказ №{no} изменён.\n\n«{dish}» удалено.\n💰 Новая сумма: {sum}\n\nЕсли есть вопросы — напишите сюда.",
        "tr": "ℹ️ #{no} numaralı siparişiniz değişti.\n\n\"{dish}\" çıkarıldı.\n💰 Yeni tutar: {sum}\n\nSorunuz olursa buraya yazın.",
        "ur": "ℹ️ آپ کا آرڈر #{no} تبدیل ہو گیا۔\n\n«{dish}» نکال دیا گیا۔\n💰 نئی رقم: {sum}\n\nکوئی سوال ہو تو یہیں لکھیں۔",
        "id": "ℹ️ Pesanan Anda #{no} berubah.\n\n\"{dish}\" dihapus.\n💰 Total baru: {sum}\n\nAda pertanyaan? Tulis di sini.",
    },
    "status_update": {
        "uz": "Buyurtmangiz #{no} holati: {st}", "ar": "حالة طلبك #{no}: {st}",
        "en": "Your order #{no} status: {st}", "ru": "Статус заказа №{no}: {st}",
        "tr": "Sipariş #{no} durumu: {st}", "ur": "آپ کے آرڈر #{no} کی حالت: {st}",
        "id": "Status pesanan #{no}: {st}",
    },
    # Oyna qaysi tilda ochilishidan qat'i nazar hamma tushunsin
    "lang_choose": {
        "uz": "🌐 Tilni tanlang · اختر اللغة · Выберите язык · Choose language",
    },
    "cb_earned": {
        "uz": "\U0001F381 Sizga {amt} keshbek yozildi!\n\U0001F4B3 Keshbek hisobingiz: {bal}\n\nKeyingi buyurtmada ishlatishingiz mumkin \u2014 savatda \u00abKeshbekdan foydalanish\u00bb ni belgilang.",
        "ar": "\U0001F381 \u062A\u0645\u0651 \u0625\u0636\u0627\u0641\u0629 {amt} \u0643\u0627\u0634 \u0628\u0627\u0643!\n\U0001F4B3 \u0631\u0635\u064A\u062F\u0643: {bal}\n\n\u064A\u0645\u0643\u0646\u0643 \u0627\u0633\u062A\u062E\u062F\u0627\u0645\u0647 \u0641\u064A \u0627\u0644\u0637\u0644\u0628 \u0627\u0644\u0642\u0627\u062F\u0645 \u2014 \u0641\u0639\u0651\u0644 \u00ab\u0627\u0633\u062A\u062E\u062F\u0627\u0645 \u0627\u0644\u0643\u0627\u0634 \u0628\u0627\u0643\u00bb \u0641\u064A \u0627\u0644\u0633\u0644\u0629.",
        "en": "\U0001F381 You earned {amt} cashback!\n\U0001F4B3 Your balance: {bal}\n\nUse it on your next order \u2014 tick \u00abUse cashback\u00bb in the cart.",
        "ru": "\U0001F381 Вам начислен кешбэк {amt}!\n\U0001F4B3 Ваш баланс: {bal}\n\nИспользуйте его в следующем заказе \u2014 отметьте \u00abИспользовать кешбэк\u00bb в корзине.",
        "tr": "\U0001F381 {amt} nakit iade kazandınız!\n\U0001F4B3 Bakiyeniz: {bal}\n\nBir sonraki siparişte kullanın \u2014 sepette \u00abNakit iadeyi kullan\u00bb seçeneğini işaretleyin.",
        "ur": "\U0001F381 \u0622\u067E \u06A9\u0648 {amt} \u06A9\u06CC\u0634 \u0628\u06CC\u06A9 \u0645\u0644\u0627!\n\U0001F4B3 \u0622\u067E \u06A9\u0627 \u0628\u06CC\u0644\u0646\u0633: {bal}\n\n\u0627\u06AF\u0644\u06D2 \u0622\u0631\u0688\u0631 \u0645\u06CC\u06BA \u0627\u0633\u062A\u0639\u0645\u0627\u0644 \u06A9\u0631\u06CC\u06BA\u06D4",
        "id": "\U0001F381 Anda mendapat cashback {amt}!\n\U0001F4B3 Saldo Anda: {bal}\n\nGunakan pada pesanan berikutnya \u2014 centang \u00abPakai cashback\u00bb di keranjang.",
    },
    "cb_refunded": {
        "uz": "\U0001F4B3 {amt} keshbek hisobingizga qaytarildi.\nJami keshbegingiz: {bal}",
        "ar": "\U0001F4B3 \u062A\u0645\u0651 \u0625\u0631\u062C\u0627\u0639 {amt} \u0625\u0644\u0649 \u0631\u0635\u064A\u062F\u0643.\n\u0627\u0644\u0645\u062C\u0645\u0648\u0639: {bal}",
        "en": "\U0001F4B3 {amt} cashback has been returned to your balance.\nTotal: {bal}",
        "ru": "\U0001F4B3 Кешбэк {amt} возвращён на ваш баланс.\nВсего: {bal}",
        "tr": "\U0001F4B3 {amt} nakit iade bakiyenize geri yüklendi.\nToplam: {bal}",
        "ur": "\U0001F4B3 {amt} \u06A9\u06CC\u0634 \u0628\u06CC\u06A9 \u0622\u067E \u06A9\u06D2 \u0628\u06CC\u0644\u0646\u0633 \u0645\u06CC\u06BA \u0648\u0627\u067E\u0633 \u06A9\u0631 \u062F\u06CC\u0627 \u06AF\u06CC\u0627\u06D4\n\u06A9\u0644: {bal}",
        "id": "\U0001F4B3 Cashback {amt} telah dikembalikan ke saldo Anda.\nTotal: {bal}",
    },
    "acct_charged": {
        "uz": "\U0001F4D2 Buyurtmangiz hisobingizga yozildi: {amt}\nHozirgi hisobingiz: {bal}",
        "ru": "\U0001F4D2 \u0417\u0430\u043a\u0430\u0437 \u0437\u0430\u043f\u0438\u0441\u0430\u043d \u043d\u0430 \u0432\u0430\u0448 \u0441\u0447\u0451\u0442: {amt}\n\u0422\u0435\u043a\u0443\u0449\u0438\u0439 \u0431\u0430\u043b\u0430\u043d\u0441: {bal}",
        "en": "\U0001F4D2 Your order was charged to your account: {amt}\nCurrent balance: {bal}",
        "ar": "\U0001F4D2 \u062a\u0645 \u062a\u0642\u064a\u064a\u062f \u0637\u0644\u0628\u0643 \u0639\u0644\u0649 \u062d\u0633\u0627\u0628\u0643: {amt}\n\u0627\u0644\u0631\u0635\u064a\u062f: {bal}",
    },
    "acct_paid": {
        "uz": "\U0001F4B5 To\u2018lovingiz qabul qilindi: {amt}\nHozirgi hisobingiz: {bal}",
        "ru": "\U0001F4B5 \u041e\u043f\u043b\u0430\u0442\u0430 \u043f\u0440\u0438\u043d\u044f\u0442\u0430: {amt}\n\u0422\u0435\u043a\u0443\u0449\u0438\u0439 \u0431\u0430\u043b\u0430\u043d\u0441: {bal}",
        "en": "\U0001F4B5 Payment received: {amt}\nCurrent balance: {bal}",
        "ar": "\U0001F4B5 \u062a\u0645 \u0627\u0633\u062a\u0644\u0627\u0645 \u0627\u0644\u062f\u0641\u0639\u0629: {amt}\n\u0627\u0644\u0631\u0635\u064a\u062f: {bal}",
    },
    "acct_my_debt": {
        "uz": "\U0001F4D2 Hisobingiz: {bal}\n\nYa\u2019ni {amt} qarzingiz bor. Keyingi buyurtmada yoki naqd to\u2018lab yuborishingiz mumkin.",
        "ru": "\U0001F4D2 \u0412\u0430\u0448 \u0441\u0447\u0451\u0442: {bal}\n\n\u0414\u043e\u043b\u0433: {amt}.",
        "en": "\U0001F4D2 Your account: {bal}\n\nYou owe {amt}.",
        "ar": "\U0001F4D2 \u062d\u0633\u0627\u0628\u0643: {bal}\n\n\u0639\u0644\u064a\u0643 {amt}.",
    },
    "acct_my_adv": {
        "uz": "\U0001F4D2 Hisobingiz: {bal}\n\nOldindan to\u2018langan {amt} bor \u2014 buyurtmalaringiz shundan yechiladi.",
        "ru": "\U0001F4D2 \u0412\u0430\u0448 \u0441\u0447\u0451\u0442: {bal}\n\n\u041f\u0440\u0435\u0434\u043e\u043f\u043b\u0430\u0442\u0430: {amt}.",
        "en": "\U0001F4D2 Your account: {bal}\n\nPrepaid: {amt}.",
        "ar": "\U0001F4D2 \u062d\u0633\u0627\u0628\u0643: {bal}\n\n\u0631\u0635\u064a\u062f \u0645\u062f\u0641\u0648\u0639 \u0645\u0642\u062f\u0645\u0627\u064b: {amt}.",
    },
    "acct_receipt_debt": {
        "uz": "\U0001F4D2 Hisobingizdagi qarz: {amt}\n",
        "ru": "\U0001F4D2 \u0414\u043e\u043b\u0433 \u043d\u0430 \u0441\u0447\u0451\u0442\u0435: {amt}\n",
        "en": "\U0001F4D2 Outstanding balance: {amt}\n",
        "ar": "\U0001F4D2 \u0627\u0644\u0645\u0628\u0644\u063a \u0627\u0644\u0645\u0633\u062a\u062d\u0642: {amt}\n",
    },
    "acct_receipt_adv": {
        "uz": "\U0001F4D2 Oldindan to'langan: {amt}\n",
        "ru": "\U0001F4D2 \u041f\u0440\u0435\u0434\u043e\u043f\u043b\u0430\u0442\u0430: {amt}\n",
        "en": "\U0001F4D2 Prepaid balance: {amt}\n",
        "ar": "\U0001F4D2 \u0631\u0635\u064a\u062f \u0645\u062f\u0641\u0648\u0639 \u0645\u0642\u062f\u0645\u0627\u064b: {amt}\n",
    },
    "acct_my_hist": {
        "uz": "\U0001F4C3 Oxirgi harakatlar:",
        "ar": "\U0001F4C3 \u0623\u062d\u062f\u062b \u0627\u0644\u062d\u0631\u0643\u0627\u062a:",
        "en": "\U0001F4C3 Recent activity:",
        "ru": "\U0001F4C3 \u041f\u043e\u0441\u043b\u0435\u0434\u043d\u0438\u0435 \u043e\u043f\u0435\u0440\u0430\u0446\u0438\u0438:",
    },
    "acct_my_zero": {
        "uz": "\U0001F4D2 Hisobingiz toza \u2014 qarz ham, avans ham yo\u2018q.",
        "ru": "\U0001F4D2 \u0421\u0447\u0451\u0442 \u0447\u0438\u0441\u0442: \u043d\u0438 \u0434\u043e\u043b\u0433\u0430, \u043d\u0438 \u043f\u0440\u0435\u0434\u043e\u043f\u043b\u0430\u0442\u044b.",
        "en": "\U0001F4D2 Your account is clear \u2014 no debt, no prepaid balance.",
        "ar": "\U0001F4D2 \u062d\u0633\u0627\u0628\u0643 \u0646\u0638\u064a\u0641 \u2014 \u0644\u0627 \u062f\u064a\u0646 \u0648\u0644\u0627 \u0631\u0635\u064a\u062f.",
    },
    "cb_balance": {
        "uz": "\U0001F4B3 Keshbek hisobingiz: {bal}\n\nHar bir yetkazilgan buyurtmadan {pct}% keshbek yig'iladi. Menyuni oching, savatda \u00abKeshbekdan foydalanish\u00bb ni belgilasangiz, keshbegingiz summadan chegiriladi.",
        "ar": "\U0001F4B3 \u0631\u0635\u064A\u062F \u0627\u0644\u0643\u0627\u0634 \u0628\u0627\u0643: {bal}\n\n\u062A\u062D\u0635\u0644 \u0639\u0644\u0649 {pct}% \u0645\u0646 \u0643\u0644 \u0637\u0644\u0628 \u064A\u062A\u0645 \u062A\u0648\u0635\u064A\u0644\u0647.",
        "en": "\U0001F4B3 Your cashback balance: {bal}\n\nYou earn {pct}% on every delivered order. Open the menu and tick \u00abUse cashback\u00bb in the cart to spend it.",
        "ru": "\U0001F4B3 Ваш кешбэк: {bal}\n\nС каждого доставленного заказа начисляется {pct}%. Откройте меню и отметьте \u00abИспользовать кешбэк\u00bb в корзине.",
        "tr": "\U0001F4B3 Nakit iade bakiyeniz: {bal}\n\nTeslim edilen her siparişten {pct}% kazanırsınız.",
        "ur": "\U0001F4B3 \u0622\u067E \u06A9\u0627 \u06A9\u06CC\u0634 \u0628\u06CC\u06A9: {bal}\n\n\u06C1\u0631 \u0688\u0644\u06CC\u0648\u0631 \u0622\u0631\u0688\u0631 \u067E\u0631 {pct}% \u0645\u0644\u062A\u0627 \u06C1\u06D2\u06D4",
        "id": "\U0001F4B3 Saldo cashback Anda: {bal}\n\nAnda mendapat {pct}% dari setiap pesanan yang terkirim.",
    },
    "cb_zero": {
        "uz": "\U0001F4B3 Hozircha keshbegingiz yo'q.\n\nHar bir yetkazilgan buyurtmadan {pct}% keshbek yig'iladi \u2014 u hisobingizda to'planib boradi va xohlagan paytingizda ishlatasiz.",
        "ar": "\U0001F4B3 \u0644\u0627 \u064A\u0648\u062C\u062F \u0631\u0635\u064A\u062F \u062D\u0627\u0644\u064A\u0627\u064B.\n\n\u062A\u062D\u0635\u0644 \u0639\u0644\u0649 {pct}% \u0645\u0646 \u0643\u0644 \u0637\u0644\u0628 \u064A\u062A\u0645 \u062A\u0648\u0635\u064A\u0644\u0647.",
        "en": "\U0001F4B3 You have no cashback yet.\n\nYou earn {pct}% on every delivered order \u2014 it builds up and you can spend it any time.",
        "ru": "\U0001F4B3 Кешбэка пока нет.\n\nС каждого доставленного заказа начисляется {pct}% \u2014 копится и тратится когда захотите.",
        "tr": "\U0001F4B3 Henüz nakit iadeniz yok.\n\nTeslim edilen her siparişten {pct}% kazanırsınız.",
        "ur": "\U0001F4B3 \u0627\u0628\u06BE\u06CC \u06A9\u0648\u0626\u06CC \u06A9\u06CC\u0634 \u0628\u06CC\u06A9 \u0646\u06C1\u06CC\u06BA\u06D4\n\n\u06C1\u0631 \u0688\u0644\u06CC\u0648\u0631 \u0622\u0631\u0688\u0631 \u067E\u0631 {pct}% \u0645\u0644\u062A\u0627 \u06C1\u06D2\u06D4",
        "id": "\U0001F4B3 Belum ada cashback.\n\nAnda mendapat {pct}% dari setiap pesanan yang terkirim.",
    },
    "cb_off": {
        "uz": "\U0001F4B3 Keshbek hozircha ishlamayapti.",
        "ar": "\U0001F4B3 \u0627\u0644\u0643\u0627\u0634 \u0628\u0627\u0643 \u063A\u064A\u0631 \u0645\u0641\u0639\u0651\u0644 \u062D\u0627\u0644\u064A\u0627\u064B.",
        "en": "\U0001F4B3 Cashback is currently switched off.",
        "ru": "\U0001F4B3 Кешбэк сейчас отключён.",
        "tr": "\U0001F4B3 Nakit iade şu anda kapalı.",
        "ur": "\U0001F4B3 \u06A9\u06CC\u0634 \u0628\u06CC\u06A9 \u0641\u06CC \u0627\u0644\u062D\u0627\u0644 \u0628\u0646\u062F \u06C1\u06D2\u06D4",
        "id": "\U0001F4B3 Cashback sedang nonaktif.",
    },
    "cb_receipt_line": {
        "uz": "\U0001F4B3 Keshbek: \u2212{amt}\n\U0001F4B5 To'lanadi: {pay}\n",
        "ar": "\U0001F4B3 \u0643\u0627\u0634 \u0628\u0627\u0643: \u2212{amt}\n\U0001F4B5 \u0627\u0644\u0645\u0637\u0644\u0648\u0628: {pay}\n",
        "en": "\U0001F4B3 Cashback: \u2212{amt}\n\U0001F4B5 To pay: {pay}\n",
        "ru": "\U0001F4B3 Кешбэк: \u2212{amt}\n\U0001F4B5 К оплате: {pay}\n",
        "tr": "\U0001F4B3 Nakit iade: \u2212{amt}\n\U0001F4B5 Ödenecek: {pay}\n",
        "ur": "\U0001F4B3 \u06A9\u06CC\u0634 \u0628\u06CC\u06A9: \u2212{amt}\n\U0001F4B5 \u0642\u0627\u0628\u0644 \u0627\u062F\u0627: {pay}\n",
        "id": "\U0001F4B3 Cashback: \u2212{amt}\n\U0001F4B5 Dibayar: {pay}\n",
    },
    "cb_line_only": {
        "uz": "\U0001F4B3 Keshbek: \u2212{amt}\n",
        "ar": "\U0001F4B3 \u0643\u0627\u0634 \u0628\u0627\u0643: \u2212{amt}\n",
        "en": "\U0001F4B3 Cashback: \u2212{amt}\n",
        "ru": "\U0001F4B3 \u041a\u0435\u0448\u0431\u044d\u043a: \u2212{amt}\n",
        "tr": "\U0001F4B3 Nakit iade: \u2212{amt}\n",
        "ur": "\U0001F4B3 \u06A9\u06CC\u0634 \u0628\u06CC\u06A9: \u2212{amt}\n",
        "id": "\U0001F4B3 Cashback: \u2212{amt}\n",
    },
    "adv_line_only": {
        "uz": "\U0001F4D2 Avansingizdan: \u2212{amt}\n",
        "ar": "\U0001F4D2 \u0645\u0646 \u0631\u0635\u064a\u062f\u0643 \u0627\u0644\u0645\u062f\u0641\u0648\u0639: \u2212{amt}\n",
        "en": "\U0001F4D2 From your prepaid balance: \u2212{amt}\n",
        "ru": "\U0001F4D2 \u0418\u0437 \u043f\u0440\u0435\u0434\u043e\u043f\u043b\u0430\u0442\u044b: \u2212{amt}\n",
        "tr": "\U0001F4D2 \u00d6n \u00f6demenizden: \u2212{amt}\n",
        "ur": "\U0001F4D2 \u0622\u067e \u06a9\u06cc \u067e\u06cc\u0634\u06af\u06cc \u0633\u06d2: \u2212{amt}\n",
        "id": "\U0001F4D2 Dari saldo prabayar: \u2212{amt}\n",
    },
    "pay_line_only": {
        "uz": "\U0001F4B5 To'lanadi: {pay}\n",
        "ar": "\U0001F4B5 \u0627\u0644\u0645\u0637\u0644\u0648\u0628: {pay}\n",
        "en": "\U0001F4B5 To pay: {pay}\n",
        "ru": "\U0001F4B5 \u041a \u043e\u043f\u043b\u0430\u0442\u0435: {pay}\n",
        "tr": "\U0001F4B5 \u00d6denecek: {pay}\n",
        "ur": "\U0001F4B5 \u0642\u0627\u0628\u0644 \u0627\u062f\u0627: {pay}\n",
        "id": "\U0001F4B5 Dibayar: {pay}\n",
    },
    "paid_full_line": {
        "uz": "\u2705 Hammasi to'langan \u2014 kuryerga pul berishingiz shart emas.\n",
        "ar": "\u2705 \u062a\u0645 \u0627\u0644\u062f\u0641\u0639 \u0628\u0627\u0644\u0643\u0627\u0645\u0644 \u2014 \u0644\u0627 \u062d\u0627\u062c\u0629 \u0644\u0644\u062f\u0641\u0639 \u0644\u0644\u0645\u0646\u062f\u0648\u0628.\n",
        "en": "\u2705 Fully paid \u2014 nothing to pay the courier.\n",
        "ru": "\u2705 \u041e\u043f\u043b\u0430\u0447\u0435\u043d\u043e \u043f\u043e\u043b\u043d\u043e\u0441\u0442\u044c\u044e \u2014 \u043a\u0443\u0440\u044c\u0435\u0440\u0443 \u043f\u043b\u0430\u0442\u0438\u0442\u044c \u043d\u0435 \u043d\u0443\u0436\u043d\u043e.\n",
        "tr": "\u2705 Tamamen \u00f6dendi \u2014 kuryeye \u00f6deme yapman\u0131z gerekmez.\n",
        "ur": "\u2705 \u0645\u06a9\u0645\u0644 \u0627\u062f\u0627\u0626\u06af\u06cc \u06c1\u0648 \u06af\u0626\u06cc\u06d4\n",
        "id": "\u2705 Sudah dibayar penuh \u2014 tidak perlu bayar ke kurir.\n",
    },
    "adv_refunded": {
        "uz": "\U0001F4D2 Buyurtma bekor qilindi \u2014 {amt} avansingiz hisobingizga qaytarildi.\nHozirgi hisobingiz: {bal}",
        "ar": "\U0001F4D2 \u062a\u0645 \u0625\u0644\u063a\u0627\u0621 \u0627\u0644\u0637\u0644\u0628 \u2014 \u062a\u0645 \u0625\u0631\u062c\u0627\u0639 {amt} \u0625\u0644\u0649 \u062d\u0633\u0627\u0628\u0643.\n\u0627\u0644\u0631\u0635\u064a\u062f: {bal}",
        "en": "\U0001F4D2 Order cancelled \u2014 {amt} was returned to your account.\nCurrent balance: {bal}",
        "ru": "\U0001F4D2 \u0417\u0430\u043a\u0430\u0437 \u043e\u0442\u043c\u0435\u043d\u0451\u043d \u2014 {amt} \u0432\u043e\u0437\u0432\u0440\u0430\u0449\u0435\u043d\u043e \u043d\u0430 \u0432\u0430\u0448 \u0441\u0447\u0451\u0442.\n\u0422\u0435\u043a\u0443\u0449\u0438\u0439 \u0431\u0430\u043b\u0430\u043d\u0441: {bal}",
    },
    "adv_spent": {
        "uz": "\U0001F4D2 Buyurtmangizdan {amt} avansingizdan yechildi.\nHozirgi hisobingiz: {bal}",
        "ar": "\U0001F4D2 \u062a\u0645 \u062e\u0635\u0645 {amt} \u0645\u0646 \u0631\u0635\u064a\u062f\u0643.\n\u0627\u0644\u0631\u0635\u064a\u062f: {bal}",
        "en": "\U0001F4D2 {amt} was taken from your prepaid balance.\nCurrent balance: {bal}",
        "ru": "\U0001F4D2 \u0421 \u043f\u0440\u0435\u0434\u043e\u043f\u043b\u0430\u0442\u044b \u0441\u043f\u0438\u0441\u0430\u043d\u043e {amt}.\n\u0422\u0435\u043a\u0443\u0449\u0438\u0439 \u0431\u0430\u043b\u0430\u043d\u0441: {bal}",
    },
    "btn_repeat": {
        "uz": "🔁 Avvalgi buyurtmani takrorlash",
        "ar": "🔁 إعادة الطلب السابق",
        "en": "🔁 Repeat last order",
        "ru": "🔁 Повторить прошлый заказ",
        "tr": "🔁 Son siparişi tekrarla",
        "ur": "🔁 پچھلا آرڈر دوبارہ",
        "id": "🔁 Ulangi pesanan terakhir",
    },
    "sub_offer": {
        "uz": "Har kuni {biz}dan buyurtma berasizmi? 😊\n1 oylik tarifimiz bilan har kuni tushlik va kechki ovqat uyingizga keladi — arzonroq va har kuni o'ylab o'tirmaysiz.",
        "ar": "هل تطلب من {biz} يومياً؟ 😊\nمع اشتراك الشهر يصلك الغداء والعشاء كل يوم — أرخص وبلا تفكير يومي.",
        "en": "Do you order from {biz} every day? 😊\nWith our monthly plan, lunch and dinner come to your door every day — cheaper, and no deciding every evening.",
        "ru": "Заказываете в {biz} каждый день? 😊\nС месячным тарифом обед и ужин приезжают к вам каждый день — дешевле и без ежедневных раздумий.",
        "tr": "Her gün {biz}'dan sipariş veriyor musunuz? 😊\nAylık paketimizle öğle ve akşam yemeği her gün kapınıza gelir — daha ucuz ve her gün düşünmek yok.",
        "ur": "کیا آپ روزانہ {biz} سے آرڈر کرتے ہیں؟ 😊\nہمارے ماہانہ پلین میں دوپہر اور رات کا کھانا روز آپ کے گھر آئے گا — سستا اور آسان۔",
        "id": "Apakah Anda memesan dari {biz} setiap hari? 😊\nDengan paket bulanan kami, makan siang dan malam datang setiap hari — lebih murah dan tanpa repot memilih.",
    },
    "btn_sub_info": {
        "uz": "📅 1 oylik tarif haqida", "ar": "📅 عن اشتراك الشهر",
        "en": "📅 About the monthly plan", "ru": "📅 О месячном тарифе",
        "tr": "📅 Aylık paket hakkında", "ur": "📅 ماہانہ پلین کے بارے میں",
        "id": "📅 Tentang paket bulanan",
    },
    "wb_7": {
        "uz": "Assalomu alaykum, {ism}! 😊\nBir haftadan beri sizdan buyurtma bo'lmadi, uzoqlashib ketdik.\nBalki biror narsa ko'nglingizga tegdimi? Ovqat, vaqt yoki boshqa narsa bo'lsa, bemalol yozing. Har bir fikringiz biz uchun muhim 🙏",
        "ar": "السلام عليكم يا {ism}! 😊\nمضى أسبوع بلا طلب منك واشتقنا إليك.\nربما لم يعجبك شيء؟ اكتب لنا بكل صراحة — رأيك يهمنا 🙏",
        "en": "Hello, {ism}! 😊\nIt has been a week since your last order and we have missed you.\nWas something not right — the food, the timing, anything else? Please write to us, your opinion matters 🙏",
        "ru": "Здравствуйте, {ism}! 😊\nУже неделю от вас нет заказов, мы соскучились.\nМожет, что-то не понравилось — еда, время или что-то ещё? Напишите нам, ваше мнение важно 🙏",
        "tr": "Merhaba {ism}! 😊\nBir haftadır sipariş vermediniz, sizi özledik.\nBir şey mi ters gitti — yemek, zaman ya da başka bir şey? Bize yazın, görüşünüz bizim için önemli 🙏",
        "ur": "السلام علیکم، {ism}! 😊\nایک ہفتے سے آپ کا آرڈر نہیں آیا، ہمیں آپ کی یاد آئی۔\nکیا کوئی بات ناگوار گزری؟ براہ کرم ہمیں لکھیں 🙏",
        "id": "Halo, {ism}! 😊\nSudah seminggu tidak ada pesanan dari Anda, kami merindukan Anda.\nApakah ada yang kurang pas — makanan, waktu, atau hal lain? Tulis saja kepada kami, pendapat Anda penting 🙏",
    },
    "wb_21": {
        "uz": "{ism}, sizni yana mehmon qilgimiz keldi 🍲\nHisobingizga {bonus} bonus qo'shdik, keyingi buyurtmada ishlatishingiz mumkin. {biz} sizni kutadi!",
        "ar": "{ism}، نشتاق لضيافتك مرة أخرى 🍲\nأضفنا {bonus} إلى رصيدك، يمكنك استخدامه في طلبك القادم. {biz} في انتظارك!",
        "en": "{ism}, we would love to host you again 🍲\nWe have added a {bonus} bonus to your balance — use it on your next order. {biz} is waiting for you!",
        "ru": "{ism}, мы будем рады снова вас угостить 🍲\nМы добавили на ваш баланс бонус {bonus} — используйте его в следующем заказе. {biz} вас ждёт!",
        "tr": "{ism}, sizi yeniden ağırlamak isteriz 🍲\nBakiyenize {bonus} bonus ekledik, bir sonraki siparişinizde kullanabilirsiniz. {biz} sizi bekliyor!",
        "ur": "{ism}، ہم آپ کی دوبارہ میزبانی کرنا چاہتے ہیں 🍲\nہم نے آپ کے بیلنس میں {bonus} بونس شامل کیا ہے۔ {biz} آپ کا منتظر ہے!",
        "id": "{ism}, kami ingin menjamu Anda lagi 🍲\nKami menambahkan bonus {bonus} ke saldo Anda, pakai pada pesanan berikutnya. {biz} menunggu Anda!",
    },
    "btn_feedback": {
        "uz": "✉️ Fikr bildirish", "ar": "✉️ شاركنا رأيك", "en": "✉️ Share feedback",
        "ru": "✉️ Оставить отзыв", "tr": "✉️ Görüş bildir",
        "ur": "✉️ رائے دیں", "id": "✉️ Beri masukan",
    },
    "btn_order_now": {
        "uz": "🛍 Buyurtma berish", "ar": "🛍 اطلب الآن", "en": "🛍 Order now",
        "ru": "🛍 Заказать", "tr": "🛍 Sipariş ver",
        "ur": "🛍 آرڈر کریں", "id": "🛍 Pesan sekarang",
    },
    "rep_none": {
        "uz": "Sizda hali yetkazilgan buyurtma yo'q. Menyuni oching va birinchi buyurtmangizni bering 😊",
        "ar": "لا يوجد لديك طلب سابق. افتح القائمة واطلب 😊",
        "en": "You have no delivered orders yet. Open the menu and place your first one 😊",
        "ru": "У вас пока нет доставленных заказов. Откройте меню и сделайте первый 😊",
        "tr": "Henüz teslim edilmiş siparişiniz yok. Menüyü açıp ilk siparişinizi verin 😊",
        "ur": "ابھی کوئی پچھلا آرڈر نہیں۔ مینو کھولیں 😊",
        "id": "Anda belum punya pesanan yang terkirim. Buka menu dan pesan yang pertama 😊",
    },
    "rep_title": {
        "uz": "🔁 Avvalgi buyurtmangiz:", "ar": "🔁 طلبك السابق:",
        "en": "🔁 Your last order:", "ru": "🔁 Ваш прошлый заказ:",
        "tr": "🔁 Son siparişiniz:", "ur": "🔁 آپ کا پچھلا آرڈر:",
        "id": "🔁 Pesanan terakhir Anda:",
    },
    "rep_removed": {
        "uz": "⚠️ Bu taomlar hozir menyuda yo'q, shuning uchun chiqarib tashladik: {list}",
        "ar": "⚠️ هذه الأطباق غير متوفرة الآن وتمّ حذفها: {list}",
        "en": "⚠️ These dishes are not on the menu right now, so we removed them: {list}",
        "ru": "⚠️ Этих блюд сейчас нет в меню, мы их убрали: {list}",
        "tr": "⚠️ Bu yemekler şu an menüde yok, çıkardık: {list}",
        "ur": "⚠️ یہ کھانے اب مینو میں نہیں، اس لیے ہٹا دیے: {list}",
        "id": "⚠️ Menu ini sedang tidak tersedia, jadi kami hapus: {list}",
    },
    "rep_too_small": {
        "uz": "Avvalgi buyurtmangizdagi taomlarning ko'pi hozir menyuda yo'q — qolgani {sum} bo'lib qoldi, eng kami {min}.\nMenyuni ochib, yangisini tanlang 👇",
        "ar": "معظم أطباق طلبك السابق غير متوفرة — المتبقي {sum} والحد الأدنى {min}.\nافتح القائمة واختر من جديد 👇",
        "en": "Most dishes from your last order are unavailable — what is left comes to {sum}, and the minimum is {min}.\nOpen the menu and pick again 👇",
        "ru": "Большинства блюд из прошлого заказа сейчас нет — осталось на {sum}, а минимум {min}.\nОткройте меню и выберите заново 👇",
        "tr": "Son siparişinizdeki yemeklerin çoğu şu an yok — kalan {sum}, en az {min} olmalı.\nMenüyü açıp yeniden seçin 👇",
        "ur": "پچھلے آرڈر کے زیادہ تر کھانے دستیاب نہیں — باقی {sum}، کم از کم {min}.\nمینو کھولیں 👇",
        "id": "Sebagian besar menu pesanan lama tidak tersedia — sisanya {sum}, minimum {min}.\nBuka menu dan pilih lagi 👇",
    },
    "rep_ask_addr": {
        "uz": "Yangi manzilni yozing yoki joylashuvingizni yuboring 📍",
        "ar": "اكتب العنوان الجديد أو أرسل موقعك 📍",
        "en": "Type the new address or send your location 📍",
        "ru": "Напишите новый адрес или отправьте геолокацию 📍",
        "tr": "Yeni adresi yazın veya konumunuzu gönderin 📍",
        "ur": "نیا پتہ لکھیں یا لوکیشن بھیجیں 📍",
        "id": "Tulis alamat baru atau kirim lokasi Anda 📍",
    },
    "rep_addr_ok": {
        "uz": "✅ Manzil yangilandi.", "ar": "✅ تم تحديث العنوان.",
        "en": "✅ Address updated.", "ru": "✅ Адрес обновлён.",
        "tr": "✅ Adres güncellendi.", "ur": "✅ پتہ اپ ڈیٹ ہو گیا۔",
        "id": "✅ Alamat diperbarui.",
    },
    "rep_cancelled": {
        "uz": "Bekor qilindi.", "ar": "تم الإلغاء.", "en": "Cancelled.",
        "ru": "Отменено.", "tr": "İptal edildi.", "ur": "منسوخ۔", "id": "Dibatalkan.",
    },
    "rep_expired": {
        "uz": "Bu so'rov eskirdi. Tugmani qaytadan bosing.",
        "ar": "انتهت صلاحية الطلب. اضغط الزر مرة أخرى.",
        "en": "This request expired. Tap the button again.",
        "ru": "Запрос устарел. Нажмите кнопку ещё раз.",
        "tr": "Bu istek zaman aşımına uğradı. Butona tekrar basın.",
        "ur": "یہ درخواست پرانی ہو گئی۔ دوبارہ دبائیں۔",
        "id": "Permintaan ini kedaluwarsa. Tekan tombol lagi.",
    },
    "btn_rep_ok": {
        "uz": "✅ Tasdiqlash", "ar": "✅ تأكيد", "en": "✅ Confirm",
        "ru": "✅ Подтвердить", "tr": "✅ Onayla", "ur": "✅ تصدیق", "id": "✅ Konfirmasi",
    },
    "btn_rep_no": {
        "uz": "❌ Bekor qilish", "ar": "❌ إلغاء", "en": "❌ Cancel",
        "ru": "❌ Отмена", "tr": "❌ İptal", "ur": "❌ منسوخ", "id": "❌ Batal",
    },
    "btn_rep_addr": {
        "uz": "📍 Manzilni o'zgartirish", "ar": "📍 تغيير العنوان",
        "en": "📍 Change address", "ru": "📍 Изменить адрес",
        "tr": "📍 Adresi değiştir", "ur": "📍 پتہ بدلیں",
        "id": "📍 Ubah alamat",
    },
    "btn_rep_cb_on": {
        "uz": "💳 Keshbekni ishlatish", "ar": "💳 استخدام الكاش باك",
        "en": "💳 Use cashback", "ru": "💳 Использовать кешбэк",
        "tr": "💳 Nakit iadeyi kullan", "ur": "💳 کیش بیک استعمال",
        "id": "💳 Pakai cashback",
    },
    "btn_rep_cb_off": {
        "uz": "↩️ Keshbeksiz", "ar": "↩️ بدون كاش باك",
        "en": "↩️ Without cashback", "ru": "↩️ Без кешбэка",
        "tr": "↩️ Nakit iadesiz", "ur": "↩️ کیش بیک کے بغیر",
        "id": "↩️ Tanpa cashback",
    },
    "lang_saved": {
        "uz": "✅ Til o'zgartirildi.", "ar": "✅ تم تغيير اللغة.", "en": "✅ Language changed.",
        "ru": "✅ Язык изменён.", "tr": "✅ Dil değiştirildi.", "ur": "✅ زبان تبدیل ہو گئی۔",
        "id": "✅ Bahasa diubah.",
    },
}

STATUS_NAMES = {
    "Tayyorlanmoqda": {"uz":"Tayyorlanmoqda","ar":"قيد التحضير","en":"Being prepared","ru":"Готовится","tr":"Hazırlanıyor","ur":"تیار ہو رہا ہے","id":"Sedang disiapkan"},
    "Yo'lda":         {"uz":"Yo'lda","ar":"في الطريق","en":"On the way","ru":"В пути","tr":"Yolda","ur":"راستے میں","id":"Dalam perjalanan"},
    "Yetkazildi":     {"uz":"Yetkazildi","ar":"تم التوصيل","en":"Delivered","ru":"Доставлено","tr":"Teslim edildi","ur":"پہنچا دیا گیا","id":"Terkirim"},
    "Yangi":          {"uz":"Yangi","ar":"جديد","en":"New","ru":"Новый","tr":"Yeni","ur":"نیا","id":"Baru"},
    "Bekor qilindi":  {"uz":"Bekor qilindi","ar":"ملغى","en":"Cancelled","ru":"Отменён","tr":"İptal edildi","ur":"منسوخ","id":"Dibatalkan"},
}

def t(key, lang, **kw):
    entry = TEXTS.get(key, {})
    text = entry.get(lang) or entry.get("uz") or ""
    try:
        return text.format(**kw) if kw else text
    except Exception:
        return text

def status_name(status, lang):
    return STATUS_NAMES.get(status, {}).get(lang, status)

# ---------- viktorina ----------

# ---------- mijozlar ro'yxati (e'lon yuborish uchun) ----------

USERS_FILE = os.path.join(DATA_DIR, "users.json")

def load_users():
    return load_json(USERS_FILE, {})

_bot_username = {"v": os.environ.get("BOT_USERNAME", "").lstrip("@")}

def bot_username():
    """Botning @nomi. Telegramdan bir marta so'raymiz va eslab qolamiz."""
    if not _bot_username["v"]:
        try:
            _bot_username["v"] = (bot.get_me().username or "").lstrip("@")
        except Exception:
            pass
    return _bot_username["v"]

def start_links(payload="dm", app_name=None):
    """Mijozni botga olib keladigan havolalar."""
    u = bot_username()
    if not u:
        return {}
    p = urllib.parse.quote(str(payload)[:60])
    out = {"start": f"https://t.me/{u}?start={p}"}
    name = (app_name or os.environ.get("MINIAPP_NAME", "")).strip().lstrip("/")
    if name:
        out["app"] = f"https://t.me/{u}/{name}?startapp={p}"
    return out

def add_known_user(user):
    """Bot bilan muloqot qilgan har bir mijozni eslab qolamiz."""
    if not user or not getattr(user, "id", None):
        return
    try:
        with DATA_LOCK:
            users = load_users()
            uid = str(user.id)
            rec = users.get(uid) or {"first_seen": int(time.time())}
            rec["name"] = (getattr(user, "first_name", "") or "Mijoz")
            rec["username"] = getattr(user, "username", None)
            rec["last_seen"] = int(time.time())
            rec["blocked"] = rec.get("blocked", False)
            users[uid] = rec
            save_json(USERS_FILE, users)
    except Exception as e:
        print(f"Mijozni eslab qolishda xato: {e}")

def mark_user_blocked(uid, blocked=True):
    try:
        with DATA_LOCK:
            users = load_users()
            rec = users.get(str(uid))
            if rec is not None:
                rec["blocked"] = blocked
                users[str(uid)] = rec
                save_json(USERS_FILE, users)
    except Exception:
        pass

def backfill_users_from_history():
    """Eski buyurtmalar va viktorina natijalaridan mijozlarni yig'ib oladi.
       Ro'yxat keyinroq qo'shilgani uchun eskilari tushmay qolgan edi."""
    try:
        with DATA_LOCK:
            users = load_users()
            qoshildi = 0

            for o in load_orders():
                uid = o.get("user_id")
                if not uid:
                    continue
                key = str(uid)
                if key in users:
                    continue
                users[key] = {
                    "name": o.get("customer_name") or "Mijoz",
                    "username": o.get("username"),
                    "first_seen": o.get("created_at", int(time.time())),
                    "last_seen": o.get("created_at", int(time.time())),
                    "blocked": False,
                    "from_history": True,
                }
                qoshildi += 1

            for key, r in load_quiz_results().items():
                if key in users:
                    continue
                users[key] = {
                    "name": r.get("name") or "Mijoz",
                    "username": r.get("username"),
                    "first_seen": r.get("started_at", int(time.time())),
                    "last_seen": r.get("started_at", int(time.time())),
                    "blocked": False,
                    "from_history": True,
                }
                qoshildi += 1

            if qoshildi:
                save_json(USERS_FILE, users)
            return qoshildi
    except Exception as e:
        print(f"Eski mijozlarni yig'ishda xato: {e}")
        return 0

def active_user_ids():
    return [int(uid) for uid, r in load_users().items() if not r.get("blocked")]

QUIZ_FILE = os.path.join(DATA_DIR, "quiz.json")
QUIZ_RESULTS_FILE = os.path.join(DATA_DIR, "quiz_results.json")

def load_quiz():
    q = load_json(QUIZ_FILE, {})
    return {
        "active": bool(q.get("active")),
        "test": bool(q.get("test")),          # sinov rejimi: faqat adminlar ko'radi
        "title": q.get("title") or "Viktorina",
        "prize": q.get("prize") or "",
        "questions": q.get("questions") or [],
    }

def quiz_visible_to(user_id):
    """Viktorina shu odamga ko'rinadimi."""
    q = load_quiz()
    if not q["active"] or not q["questions"]:
        return False
    if q["test"]:
        return is_owner(user_id) or user_id in load_staff_ids()
    return True

def save_quiz(q):
    save_json(QUIZ_FILE, q)

def load_quiz_results():
    return load_json(QUIZ_RESULTS_FILE, {})

def save_quiz_results(r):
    save_json(QUIZ_RESULTS_FILE, r)

def parse_quiz_text(text):
    """Savollarni oddiy matndan o'qiydi.
       Har bir savol bloki: birinchi qator — savol, keyingilari — variantlar,
       to'g'ri javob oldida * turadi. Bloklar bo'sh qator bilan ajratiladi."""
    questions, errors = [], []
    blocks = [b for b in re.split(r"\n\s*\n", (text or "").strip()) if b.strip()]
    for bi, block in enumerate(blocks, start=1):
        lines = [ln.strip() for ln in block.splitlines() if ln.strip()]
        if len(lines) < 3:
            errors.append(f"{bi}-savol: savol va kamida 2 ta variant kerak")
            continue
        q = lines[0]
        opts, correct = [], None
        for ln in lines[1:]:
            if ln.startswith("*"):
                if correct is not None:
                    errors.append(f"{bi}-savol: bitta to'g'ri javob belgilansin")
                correct = len(opts)
                ln = ln[1:].strip()
            opts.append(ln)
        if correct is None:
            errors.append(f"{bi}-savol: to'g'ri javob * bilan belgilanmagan")
            continue
        if len(opts) > 6:
            errors.append(f"{bi}-savol: 6 tadan ko'p variant bo'lmasin")
            continue
        questions.append({"q": q, "options": opts, "correct": correct})
    return questions, errors

def quiz_to_text(quiz):
    out = []
    for item in quiz.get("questions", []):
        lines = [item["q"]]
        for i, o in enumerate(item.get("options", [])):
            lines.append(("*" if i == item.get("correct") else "") + o)
        out.append("\n".join(lines))
    return "\n\n".join(out)

def quiz_leaderboard(limit=None):
    """Tugatganlar: avval ko'p to'g'ri, keyin kam vaqt."""
    rows = []
    for uid, r in load_quiz_results().items():
        if not r.get("done"):
            continue
        rows.append({
            "uid": int(uid),
            "name": r.get("name") or "Mijoz",
            "username": r.get("username"),
            "correct": r.get("correct", 0),
            "ms": r.get("elapsed_ms", 0),
            "finished_at": r.get("finished_at", 0),
        })
    rows.sort(key=lambda x: (-x["correct"], x["ms"], x["finished_at"]))
    return rows[:limit] if limit else rows

def fmt_secs(ms):
    sec = ms / 1000.0
    if sec < 60:
        return f"{sec:.1f} s"
    m = int(sec // 60)
    return f"{m} daq {sec - m*60:.0f} s"

# ---------- ish vaqti ----------

def get_hours():
    """Ish vaqti sozlamasi:
       closed_today — qo'lda yopish (dam olish kuni)
       schedule_on  — kunlik jadval yoqilganmi
       open/close   — 'HH:MM' ko'rinishida"""
    s = load_settings()
    h = s.get("hours") or {}
    return {
        "closed_today": bool(h.get("closed_today")),
        "schedule_on": bool(h.get("schedule_on")),
        "open": h.get("open") or "06:00",
        "close": h.get("close") or "22:00",
    }

def set_hours(closed_today=None, schedule_on=None, open_time=None, close_time=None):
    s = load_settings()
    h = s.get("hours") or {}
    if closed_today is not None:
        h["closed_today"] = bool(closed_today)
    if schedule_on is not None:
        h["schedule_on"] = bool(schedule_on)
    if open_time is not None and valid_hhmm(open_time):
        h["open"] = open_time
    if close_time is not None and valid_hhmm(close_time):
        h["close"] = close_time
    s["hours"] = h
    save_settings(s)
    return get_hours()

def valid_hhmm(value):
    try:
        hh, mm = str(value).split(":")
        return 0 <= int(hh) <= 23 and 0 <= int(mm) <= 59
    except Exception:
        return False

def _minutes(hhmm):
    hh, mm = str(hhmm).split(":")
    return int(hh) * 60 + int(mm)

def shop_status():
    """Hozir buyurtma qabul qilinadimi. {'open': bool, 'reason': 'closed_today'|'schedule'|None, ...}"""
    h = get_hours()
    if h["closed_today"]:
        return {"open": False, "reason": "closed_today", "open_time": h["open"], "close_time": h["close"]}
    if h["schedule_on"] and valid_hhmm(h["open"]) and valid_hhmm(h["close"]):
        now = datetime.now(TIMEZONE)
        cur = now.hour * 60 + now.minute
        start, end = _minutes(h["open"]), _minutes(h["close"])
        if start == end:
            is_open = True                      # 24 soat
        elif start < end:
            is_open = start <= cur < end        # masalan 06:00–22:00
        else:
            is_open = cur >= start or cur < end  # yarim tundan oshadigan jadval
        if not is_open:
            return {"open": False, "reason": "schedule", "open_time": h["open"], "close_time": h["close"]}
    return {"open": True, "reason": None, "open_time": h["open"], "close_time": h["close"]}

def closed_message(lang, st=None):
    st = st or shop_status()
    if st["reason"] == "closed_today":
        return t("closed_today", lang)
    return t("closed_hours", lang, open=st["open_time"], close=st["close_time"])

# ---------- aksiya (chegirma) ----------

def migrate_builder_category():
    """Bo'lim nomi o'zgargan bo'lsa, menyudagi mahsulotlarni yangi nomga ko'chiramiz."""
    if not BUILDER_OLD_NAMES:
        return 0
    try:
        with DATA_LOCK:
            menu = load_menu()
            n = 0
            for d in menu:
                if (d.get("category") or "") in BUILDER_OLD_NAMES:
                    d["category"] = BUILDER_CATEGORY
                    n += 1
            if n:
                save_menu(menu)
        if n:
            print(f"Bo'lim nomi yangilandi: {n} ta mahsulot \u2192 {BUILDER_CATEGORY}")
        return n
    except Exception as e:
        print(f"Bo'lim nomini ko'chirishda xato: {e}")
        return 0

def builder_min():
    """«O'zingiz yig'ing» bo'limi uchun eng kam summa."""
    try:
        v = money(load_settings().get("yigma_min", BUILDER_MIN_DEFAULT))
    except Exception:
        v = BUILDER_MIN_DEFAULT
    return v if v > 0 else 0.0

def set_builder_min(value):
    with DATA_LOCK:
        s = load_settings()
        s["yigma_min"] = money(max(0, value))
        save_settings(s)

def get_discount():
    """Hozirgi aksiya: {'active': bool, 'percent': int}."""
    s = load_settings()
    d = s.get("discount") or {}
    try:
        percent = int(d.get("percent", 0))
    except Exception:
        percent = 0
    percent = max(0, min(90, percent))
    return {"active": bool(d.get("active")) and percent > 0, "percent": percent}

def set_discount(active=None, percent=None):
    s = load_settings()
    d = s.get("discount") or {}
    if percent is not None:
        try:
            d["percent"] = max(0, min(90, int(percent)))
        except Exception:
            pass
    if active is not None:
        d["active"] = bool(active)
    s["discount"] = d
    save_settings(s)
    return get_discount()

def discounted_price(price, disc=None):
    """Aksiya yoqilgan bo'lsa chegirmali narx, aks holda o'zi. Natija butun songa yaxlitlanadi."""
    disc = disc if disc is not None else get_discount()
    if not disc["active"]:
        return price
    return round(price * (100 - disc["percent"]) / 100)


# ---------- keshbek ----------

DEFAULT_CASHBACK_PERCENT = 5

def load_cashback():
    return load_json(CASHBACK_FILE, {})

def save_cashback(data):
    save_json(CASHBACK_FILE, data)

def get_cashback_cfg():
    """Hozirgi sozlama: {'active': bool, 'percent': float}."""
    s = load_settings()
    cb = s.get("cashback") or {}
    try:
        percent = float(cb.get("percent", DEFAULT_CASHBACK_PERCENT))
    except Exception:
        percent = DEFAULT_CASHBACK_PERCENT
    percent = max(0.0, min(100.0, percent))
    active = bool(cb.get("active", True)) and percent > 0
    return {"active": active, "percent": percent}

def set_cashback_cfg(active=None, percent=None):
    with DATA_LOCK:
        s = load_settings()
        cb = s.get("cashback") or {}
        if percent is not None:
            try:
                cb["percent"] = max(0.0, min(100.0, float(percent)))
            except Exception:
                pass
        if active is not None:
            cb["active"] = bool(active)
        s["cashback"] = cb
        save_settings(s)
    return get_cashback_cfg()

def cashback_balance(user_id):
    if not user_id:
        return 0.0
    rec = load_cashback().get(str(user_id)) or {}
    return money(rec.get("balance", 0))

def cashback_move(user_id, delta, order_id=None, note=""):
    """Balansni o'zgartiradi (+ qo'shish, − yechish). Yangi balansni qaytaradi.
    Balans hech qachon manfiy bo'lmaydi."""
    delta = money(delta)
    if not user_id or delta == 0:
        return cashback_balance(user_id)
    with DATA_LOCK:
        data = load_cashback()
        uid = str(user_id)
        rec = data.get(uid) or {"balance": 0.0, "earned": 0.0, "spent": 0.0, "history": []}
        cur = money(rec.get("balance", 0))
        new_bal = money(cur + delta)
        if new_bal < 0:                 # bor-yo'g'idan ortig'ini yecha olmaymiz
            delta = money(-cur)
            new_bal = 0.0
        rec["balance"] = new_bal
        if delta > 0:
            rec["earned"] = money(rec.get("earned", 0) + delta)
        else:
            rec["spent"] = money(rec.get("spent", 0) - delta)
        hist = rec.get("history") or []
        hist.append({"ts": int(time.time()), "delta": delta, "order": order_id,
                     "note": note, "balance": new_bal})
        rec["history"] = hist[-40:]
        rec["updated_at"] = int(time.time())
        data[uid] = rec
        save_cashback(data)
    return new_bal

def cashback_for(amount):
    """Shu summadan qancha keshbek yoziladi."""
    cfg = get_cashback_cfg()
    if not cfg["active"]:
        return 0.0
    return money(amount * cfg["percent"] / 100.0)

def order_cashback_used(order):
    return money(order.get("cashback_used") or 0)

def order_payable(order):
    """Mijoz naqd to'laydigan summa — keshbek chegirilgandan keyin."""
    return max(0.0, money(order.get("total", 0) - order_cashback_used(order)))

def credit_order_cashback(order):
    """Yetkazilgan buyurtma uchun keshbek yozadi. (yozilgan_summa, yangi_balans).
    Keshbek bilan to'langan qismdan qayta keshbek hisoblanmaydi."""
    uid = order.get("user_id")
    # Telegram orqali qo'lda kiritilgan buyurtmalarga keshbek yozilmaydi
    if not uid or order.get("cashback_credited") or is_cancelled(order) or order.get("no_cashback"):
        return 0.0, cashback_balance(uid)
    amount = cashback_for(order_payable(order))
    order["cashback_credited"] = True
    order["cashback_earned"] = amount
    order["cashback_credited_at"] = int(time.time())
    if amount <= 0:
        return 0.0, cashback_balance(uid)
    return amount, cashback_move(uid, amount, order.get("id"), "buyurtma yetkazildi")

def revoke_order_cashback(order, note="yetkazildi bekor qilindi"):
    """Yozilgan keshbekni qaytarib oladi (bekor qilinganda yoki holat orqaga o'zgarganda)."""
    uid = order.get("user_id")
    if not uid or not order.get("cashback_credited"):
        return 0.0, cashback_balance(uid)
    amount = money(order.get("cashback_earned") or 0)
    order["cashback_credited"] = False
    order["cashback_earned"] = 0.0
    order.pop("cashback_credited_at", None)
    if amount <= 0:
        return 0.0, cashback_balance(uid)
    return amount, cashback_move(uid, -amount, order.get("id"), note)

def refund_used_cashback(order, note="buyurtma bekor qilindi"):
    """Bekor qilinganda ishlatilgan keshbekni mijozga qaytaradi."""
    uid = order.get("user_id")
    used = order_cashback_used(order)
    if not uid or used <= 0 or order.get("cashback_refunded"):
        return 0.0, cashback_balance(uid)
    order["cashback_refunded"] = True
    return used, cashback_move(uid, used, order.get("id"), note)

def recharge_used_cashback(order):
    """Bekor qaytarilganda keshbekni qaytadan yechadi. Balans yetmasa False qaytaradi."""
    uid = order.get("user_id")
    used = order_cashback_used(order)
    if not uid or used <= 0 or not order.get("cashback_refunded"):
        return True
    with DATA_LOCK:
        if cashback_balance(uid) + 1e-9 < used:
            order["cashback_used"] = 0.0        # oraliqda sarflab yuborilgan
            order["cashback_refunded"] = False
            return False
        cashback_move(uid, -used, order.get("id"), "bekor qaytarildi")
        order["cashback_refunded"] = False
    return True

def trim_cashback_to_total(order):
    """Taom olib tashlangach keshbek summadan oshib ketsa, ortig'ini qaytaradi."""
    used = order_cashback_used(order)
    total = money(order.get("total") or 0)
    if used <= total:
        return 0.0
    extra = money(used - total)
    order["cashback_used"] = total
    if order.get("user_id") and not order.get("cashback_refunded"):
        cashback_move(order["user_id"], extra, order.get("id"), "taom olib tashlandi")
    return extra

def cashback_holders():
    """Keshbegi bor mijozlar — ko'pidan ozigacha. [(uid, balans, ism, username)]"""
    users = load_users()
    out = []
    for uid, rec in load_cashback().items():
        bal = money(rec.get("balance", 0))
        if bal <= 0:
            continue
        u = users.get(str(uid)) or {}
        out.append((uid, bal, (u.get("name") or "").strip(), u.get("username") or ""))
    out.sort(key=lambda r: -r[1])
    return out

def cashback_find_user(needle):
    """Username yoki ism bo'yicha mijozni topadi. Bitta topilsa uning id sini qaytaradi."""
    needle = (needle or "").strip().lstrip("@").lower()
    if not needle:
        return []
    hits = []
    for uid, u in load_users().items():
        uname = (u.get("username") or "").lower()
        name = (u.get("name") or "").lower()
        if needle == uname or needle in name:
            hits.append(int(uid))
    return hits

def cashback_holder_line(uid, bal, name, uname):
    kim = name or "Ism yo'q"
    if uname:
        kim += f" @{uname}"
    return f"{fmt_sum(bal)} \u2014 {kim} (ID {uid})"

def cashback_totals():
    """Barcha mijozlardagi yig'ilib turgan keshbek — bu bizning qarzimiz."""
    data = load_cashback()
    bal = money(sum(money(r.get("balance", 0)) for r in data.values()))
    people = sum(1 for r in data.values() if money(r.get("balance", 0)) > 0)
    return {"balance": bal, "people": people, "all": len(data)}

# ======================================================================
#  MIJOZ HISOBI — nasiya (minus) va avans (plyus)
#
#  Keshbekdan butunlay ajratilgan: keshbek — bonus, hisob — haqiqiy pul.
#  Balans manfiy bo'lishi mumkin, chegara yo'q.
# ======================================================================

def load_account():
    return load_json(ACCOUNT_FILE, {})

def save_account(data):
    save_json(ACCOUNT_FILE, data)

def account_balance(user_id):
    if not user_id:
        return 0.0
    rec = load_account().get(str(user_id)) or {}
    return money(rec.get("balance", 0))

def fmt_signed(x):
    """−120 SAR / +380 SAR — belgisi bilan."""
    v = money(x)
    if v < 0:
        return "−" + fmt_sum(-v)
    if v > 0:
        return "+" + fmt_sum(v)
    return fmt_sum(0)

def account_move(user_id, delta, order_id=None, note=""):
    """Hisobni o'zgartiradi. Minusga tushishi mumkin — bu nasiya.
    Yangi balansni qaytaradi."""
    delta = money(delta)
    if not user_id or delta == 0:
        return account_balance(user_id)
    with DATA_LOCK:
        data = load_account()
        uid = str(user_id)
        rec = data.get(uid) or {"balance": 0.0, "history": []}
        new_bal = money(money(rec.get("balance", 0)) + delta)
        rec["balance"] = new_bal
        hist = rec.get("history") or []
        hist.append({"ts": int(time.time()), "delta": delta,
                     "order_id": order_id, "note": note, "bal": new_bal})
        rec["history"] = hist[-60:]
        data[uid] = rec
        save_account(data)
    return new_bal

def account_holders():
    """Nol bo'lmagan hisoblar: [(uid, balans, ism, username)].
    Avval eng katta qarzdorlar, keyin avansi borlar."""
    users = load_users()
    out = []
    for uid, rec in load_account().items():
        bal = money(rec.get("balance", 0))
        if bal == 0:
            continue
        u = users.get(str(uid)) or {}
        out.append((int(uid), bal, (u.get("name") or "").strip(), u.get("username") or ""))
    out.sort(key=lambda r: r[1])          # eng katta minus birinchi
    return out

def account_totals():
    data = load_account()
    debt = adv = 0.0
    nd = na = 0
    for rec in data.values():
        bal = money(rec.get("balance", 0))
        if bal < 0:
            debt = money(debt - bal)
            nd += 1
        elif bal > 0:
            adv = money(adv + bal)
            na += 1
    return {"debt": debt, "debtors": nd, "advance": adv, "advanced": na}

def account_line(uid, bal, name, uname):
    kim = name or "Ism yo'q"
    if uname:
        kim += f" @{uname}"
    belgi = "🔴" if bal < 0 else "🟢"
    return f"{belgi} {fmt_signed(bal)} — {kim} (ID {uid})"

def hisob_webapp_kb(uid, uname):
    """Nasiya sahifasini ochadigan tugma."""
    if not WEBAPP_URL:
        return None
    ts, sig = sign_user_params(uid, uname)
    params = (f"uid={uid}&uname={urllib.parse.quote(uname or '')}"
              f"&ts={ts}&sig={sig}&v={ts}")
    kb = types.InlineKeyboardMarkup()
    kb.add(types.InlineKeyboardButton(
        "\U0001F4D2 Hisobni ochish",
        web_app=types.WebAppInfo(url=f"{WEBAPP_URL}/hisob?{params}")))
    return kb

def order_on_account(order):
    return bool(order.get("on_account"))

# ---------- avansni buyurtmada ishlatish ----------
#
#  Mijozning avansi (balans plyusda) bo'lsa, buyurtma tushgan payt bot
#  o'zi yechib qo'yadi — keshbek chegirilgandan keyin qolgan summadan.
#  Qarzni esa faqat qo'lda kiritamiz: mijoz "pulim yo'q" desa.

def order_advance_used(order):
    return money(order.get("advance_used") or 0)

def order_cash_due(order):
    """Mijoz naqd beradigan summa: jami − keshbek − avans."""
    return max(0.0, money(order_payable(order) - order_advance_used(order)))

def advance_for_order(user_id, payable):
    """Shu buyurtmaga avansdan qancha ishlatish mumkin."""
    if not user_id:
        return 0.0
    bal = account_balance(user_id)
    if bal <= 0:
        return 0.0
    use = money(min(bal, max(0.0, money(payable))))
    return use if use >= 0.01 else 0.0

def refund_used_advance(order, note="buyurtma bekor qilindi"):
    """Bekor qilinganda ishlatilgan avans hisobga qaytadi."""
    uid = order.get("user_id")
    used = order_advance_used(order)
    if not uid or used <= 0 or order.get("advance_refunded"):
        return 0.0, account_balance(uid)
    order["advance_refunded"] = True
    return used, account_move(uid, used, order.get("id"), note)

def recharge_used_advance(order):
    """Bekor qaytarilganda avansni qaytadan yechadi.
    Hisob minusga tushsa ham yechiladi — bu haqiqiy pul, qarzga aylanadi."""
    uid = order.get("user_id")
    used = order_advance_used(order)
    if not uid or used <= 0 or not order.get("advance_refunded"):
        return 0.0, account_balance(uid)
    order["advance_refunded"] = False
    return used, account_move(uid, -used, order.get("id"), "bekor qaytarildi")

def trim_advance_to_total(order):
    """Taom olib tashlangach avans ortib qolsa, ortig'i hisobga qaytadi."""
    used = order_advance_used(order)
    cap = money(order_payable(order))
    if used <= cap:
        return 0.0
    extra = money(used - cap)
    order["advance_used"] = cap
    if order.get("user_id") and not order.get("advance_refunded"):
        account_move(order["user_id"], extra, order.get("id"), "taom olib tashlandi")
    return extra

def account_history(user_id, limit=10):
    """Mijozga ko'rsatiladigan oxirgi harakatlar — yangisi birinchi."""
    if not user_id:
        return []
    rec = load_account().get(str(user_id)) or {}
    hist = (rec.get("history") or [])[-limit:]
    return list(reversed(hist))

# ======================================================================
#  TELEGRAMDAN TUSHGAN BUYURTMA
#
#  Admin mijozning xabarini botga forward qiladi; bot undan ism, t.me
#  havolasi va joylashuvni ajratib oladi. Keyin admin savatni yig'adi.
#  Bunday buyurtmalarga keshbek yozilmaydi.
# ======================================================================

TGDRAFT_TTL = 24 * 3600          # qoralama shuncha vaqt yashaydi

def load_tgdrafts():
    return load_json(TGDRAFT_FILE, {})

def save_tgdrafts(data):
    save_json(TGDRAFT_FILE, data)

def tgdraft_clean(data):
    """Eskirganlarini tashlab yuboramiz."""
    now = int(time.time())
    return {k: v for k, v in data.items() if now - int(v.get("ts", 0)) < TGDRAFT_TTL}

def tgdraft_get(token):
    return tgdraft_clean(load_tgdrafts()).get(str(token))

def tgdraft_put(token, draft):
    with DATA_LOCK:
        data = tgdraft_clean(load_tgdrafts())
        draft["ts"] = int(time.time())
        data[str(token)] = draft
        save_tgdrafts(data)
    return draft

def tgdraft_drop(token):
    with DATA_LOCK:
        data = tgdraft_clean(load_tgdrafts())
        data.pop(str(token), None)
        save_tgdrafts(data)

TGDRAFT_JOIN_WINDOW = 20 * 60     # shuncha vaqt ichida qo'shish taklif qilinadi

def tgdraft_same_sender(admin_id, uid, uname, name):
    """Shu adminning, AYNAN SHU mijozdan ochilgan oxirgi qoralamasi.

    Mijozni ajratmasak, 20 daqiqa ichida tushgan ikkinchi buyurtma
    birinchisining ustiga yopishib ketadi — shuning uchun kimligini
    tekshiramiz."""
    now = int(time.time())
    best = None
    for token, d in tgdraft_clean(load_tgdrafts()).items():
        if d.get("admin_id") != admin_id or d.get("used"):
            continue
        if now - int(d.get("ts", 0)) > TGDRAFT_JOIN_WINDOW:
            continue
        mos = False
        if uid and d.get("user_id") and int(d["user_id"]) == int(uid):
            mos = True
        elif uname and d.get("username") and d["username"].lower() == uname.lower():
            mos = True
        elif name and d.get("name") and d["name"].strip().lower() == name.strip().lower() \
                and not uid and not d.get("user_id"):
            mos = True
        if not mos:
            continue
        if best is None or d["ts"] > best[1]["ts"]:
            best = (token, d)
    return best

def tgdraft_merge(dst, src):
    """src dagi bo'sh bo'lmagan maydonlarni dst ga ko'chiradi (dst ustun turadi)."""
    for k in ("user_id", "username", "tme", "name", "phone", "address", "map_link"):
        if not dst.get(k) and src.get(k):
            dst[k] = src[k]
    if dst.get("lat") is None and src.get("lat") is not None:
        dst["lat"], dst["lon"] = src["lat"], src["lon"]
    if src.get("text"):
        dst["text"] = ((dst.get("text", "") + "\n" + src["text"]).strip())[:900]
    return dst

_COORD_RE = re.compile(r"(-?\d{1,3}\.\d{3,})[,\s]+(-?\d{1,3}\.\d{3,})")

def parse_map_link(text):
    """Xarita havolasidan yoki oddiy matndan koordinata ajratadi.
    Qaytaradi: (lat, lon) yoki (None, None)."""
    if not text:
        return None, None
    s = str(text)

    # Yandex: ll=UZUNLIK,KENGLIK (tartibi teskari)
    m = re.search(r"[?&](?:ll|whatshere\[point\])=(-?\d+\.\d+)(?:,|%2C)(-?\d+\.\d+)", s, re.I)
    if m:
        lon, lat = float(m.group(1)), float(m.group(2))
        if -90 <= lat <= 90 and -180 <= lon <= 180:
            return lat, lon

    # Google: @KENGLIK,UZUNLIK  yoki  q=KENGLIK,UZUNLIK  yoki  !3dKENGLIK!4dUZUNLIK
    for pat in (r"@(-?\d+\.\d+),(-?\d+\.\d+)",
                r"[?&](?:q|query|destination|daddr)=(-?\d+\.\d+)(?:,|%2C)(-?\d+\.\d+)",
                r"!3d(-?\d+\.\d+)!4d(-?\d+\.\d+)"):
        m = re.search(pat, s, re.I)
        if m:
            lat, lon = float(m.group(1)), float(m.group(2))
            if -90 <= lat <= 90 and -180 <= lon <= 180:
                return lat, lon

    # Oddiy matn: 21.39042, 39.87661
    m = _COORD_RE.search(s)
    if m:
        lat, lon = float(m.group(1)), float(m.group(2))
        if -90 <= lat <= 90 and -180 <= lon <= 180:
            return lat, lon
    return None, None

def first_url(text):
    if not text:
        return ""
    m = re.search(r"https?://\S+", str(text))
    return m.group(0) if m else ""

def extract_phone(text):
    """Matndan telefon raqamini ajratadi (Saudiya va O'zbekiston formatlari)."""
    if not text:
        return ""
    m = re.search(r"(\+?\d[\d\s\-()]{7,17}\d)", str(text))
    if not m:
        return ""
    raw = re.sub(r"[^\d+]", "", m.group(1))
    return raw if len(re.sub(r"\D", "", raw)) >= 9 else ""

# ---------- mijozni qaytarish: kimga nima yuborilgani ----------

def load_winback():
    """{"<user_id>": {"offer3": ts, "s7": ts, "s21": ts}} — bir xil xabar ikki marta ketmasin."""
    return load_json(WINBACK_FILE, {})

def save_winback(data):
    save_json(WINBACK_FILE, data)

def winback_mark(user_id, key):
    with DATA_LOCK:
        data = load_winback()
        uid = str(user_id)
        rec = data.get(uid) or {}
        rec[key] = int(time.time())
        data[uid] = rec
        save_winback(data)

def winback_reset(user_id):
    """Mijoz qayta buyurtma berdi — uxlash bosqichlari noldan boshlanadi."""
    if not user_id:
        return
    with DATA_LOCK:
        data = load_winback()
        uid = str(user_id)
        rec = data.get(uid)
        if not rec:
            return
        if not rec.get("s7") and not rec.get("s21"):
            return
        rec.pop("s7", None)
        rec.pop("s21", None)
        data[uid] = rec
        save_winback(data)

def order_delivered_ts(order):
    return order.get("delivered_at") or order.get("cashback_credited_at") or order.get("created_at") or 0

def delivered_orders_of(user_id, orders=None):
    """Mijozning yetkazilgan (bekor qilinmagan) buyurtmalari — eskidan yangiga."""
    if not user_id:
        return []
    orders = orders if orders is not None else load_orders()
    mine = [o for o in orders
            if o.get("user_id") == user_id
            and o.get("status") == "Yetkazildi"
            and not is_cancelled(o)]
    mine.sort(key=order_delivered_ts)
    return mine

def last_delivery_by_user(orders=None):
    """{user_id: oxirgi yetkazilgan vaqti} — bitta o'qishda hammasi."""
    orders = orders if orders is not None else load_orders()
    out = {}
    for o in orders:
        uid = o.get("user_id")
        if not uid or is_cancelled(o) or o.get("status") != "Yetkazildi":
            continue
        ts = order_delivered_ts(o)
        if ts > out.get(uid, 0):
            out[uid] = ts
    return out

# Tugmalarni chizishda har safar orders.json o'qimaslik uchun kichik kesh
_delivered_cache = {"ts": 0.0, "ids": set()}

def users_with_delivery():
    now = time.time()
    if now - _delivered_cache["ts"] > 60:
        _delivered_cache["ids"] = set(last_delivery_by_user().keys())
        _delivered_cache["ts"] = now
    return _delivered_cache["ids"]

def mark_delivered_user(user_id):
    """Yangi yetkazilgan buyurtma — keshni darhol yangilaymiz."""
    if user_id:
        _delivered_cache["ids"].add(user_id)

# ---------- versiya: qaysi kod ishlayotganini bir qarashda bilish uchun ----------

def _build_version():
    """bot.py faylining o'zgartirilgan vaqti — har deploy'da yangilanadi."""
    try:
        ts = os.path.getmtime(os.path.abspath(__file__))
    except Exception:
        ts = time.time()
    return datetime.fromtimestamp(ts, TIMEZONE).strftime("%d.%m.%Y %H:%M")

APP_VERSION = _build_version()

def no_cache(html, status=200):
    """Telegram va brauzer eski sahifani keshdan ko'rsatmasin."""
    return html, status, {
        "Content-Type": "text/html; charset=utf-8",
        "Cache-Control": "no-store, no-cache, must-revalidate, max-age=0",
        "Pragma": "no-cache",
        "Expires": "0",
    }

def is_owner(chat_id):
    """To'liq admin — menyu, zaxira, adminlarni boshqara oladi."""
    return chat_id in load_admin_ids()

def is_staff_or_admin(chat_id):
    """Xodim yoki admin — buyurtma xabarini oladi, holatini o'zgartira oladi."""
    return chat_id in load_admin_ids() or chat_id in load_staff_ids()

def notify_recipients():
    return load_admin_ids() | load_staff_ids()

def money(x):
    """Pulni 2 xonagacha yaxlitlaydi — suzuvchi nuqta xatolari yig'ilib ketmasin."""
    try:
        return round(float(x) + 1e-9, 2)
    except Exception:
        return 0.0

def fmt_sum(n):
    """Butun bo'lsa '18 SAR', kasrli bo'lsa '17.10 SAR'."""
    v = money(n)
    s = f"{v:,.2f}".replace(",", " ")
    if s.endswith(".00"):
        s = s[:-3]
    return s + " SAR"

def parse_dish_caption(text):
    """'Nomi;Narxi;Tavsif;Kategoriya;Set' formatini o'qiydi. Oxirgi ikkisi ixtiyoriy."""
    parts = text.split(";")
    name = parts[0].strip()
    price = float(parts[1].strip())
    desc = parts[2].strip() if len(parts) > 2 else ""
    category_raw = parts[3].strip() if len(parts) > 3 else ""
    set_raw = parts[4].strip() if len(parts) > 4 else ""
    category = match_category(category_raw)
    category_warning = category is None
    if category is None:
        category = DEFAULT_CATEGORY
    return name, price, desc, category, category_warning, parse_set_keys(set_raw)

def download_telegram_file(file_id, dest_path):
    file_info = bot.get_file(file_id)
    file_url = f"https://api.telegram.org/file/bot{BOT_TOKEN}/{file_info.file_path}"
    r = httpreq.get(file_url, timeout=30)
    r.raise_for_status()
    with open(dest_path, "wb") as f:
        f.write(r.content)

# ---------- doimiy pastki klaviatura ----------

def sign_user_params(user_id, username):
    ts = int(time.time())
    uname = username or ""
    payload = f"{user_id}:{uname}:{ts}"
    sig = hmac.new(BOT_TOKEN.encode(), payload.encode(), hashlib.sha256).hexdigest()
    return ts, sig

def main_keyboard(user_id=None, username=None, lang=None):
    lang = lang or get_user_lang(user_id)
    kb = types.ReplyKeyboardMarkup(resize_keyboard=True)
    if WEBAPP_URL and user_id:
        ts, sig = sign_user_params(user_id, username)
        params = f"uid={user_id}&uname={urllib.parse.quote(username or '')}&ts={ts}&sig={sig}&v={ts}"
        fresh_url = f"{WEBAPP_URL}?{params}"
        kb.row(types.KeyboardButton(t("btn_order", lang), web_app=types.WebAppInfo(url=fresh_url)))
        if is_owner(user_id):
            admin_url = f"{WEBAPP_URL}/admin?{params}"
            kitchen_url = f"{WEBAPP_URL}/kitchen?{params}"
            kb.row(types.KeyboardButton("🧑‍🍳 Menyuni boshqarish", web_app=types.WebAppInfo(url=admin_url)))
            kb.row(types.KeyboardButton("🖨 Oshxona", web_app=types.WebAppInfo(url=kitchen_url)))
            hisob_url = f"{WEBAPP_URL}/hisob?{params}"
            kb.row(types.KeyboardButton("📒 Nasiya va avans",
                                        web_app=types.WebAppInfo(url=hisob_url)))
    try:
        if user_id and user_id in users_with_delivery():
            kb.row(types.KeyboardButton(t("btn_repeat", lang)))
    except Exception:
        pass
    try:
        if user_id and quiz_visible_to(user_id):
            kb.row(types.KeyboardButton(QUIZ_BTN), types.KeyboardButton(BOARD_BTN))
    except Exception:
        pass
    # Qarzi yoki avansi bo'lgan mijozga alohida tugma — boshqalarga ko'rinmaydi
    try:
        if user_id and not is_owner(user_id) and account_balance(user_id) != 0:
            kb.row(types.KeyboardButton(t("btn_my_account", lang)))
    except Exception:
        pass
    kb.row(types.KeyboardButton(t("btn_contact", lang)), types.KeyboardButton(t("btn_lang", lang)))
    return kb

def is_contact_button(text):
    return any(text == TEXTS["btn_contact"][l] for l in SUPPORTED_LANGS)

def is_my_account_button(text):
    return any(text == TEXTS["btn_my_account"][l] for l in SUPPORTED_LANGS)

def is_lang_button(text):
    return any(text == TEXTS["btn_lang"][l] for l in SUPPORTED_LANGS)

def is_no_phone_button(text):
    return any(text == TEXTS["btn_no_phone"][l] for l in SUPPORTED_LANGS)

def is_any_bot_button(text):
    return (is_contact_button(text) or is_lang_button(text) or is_no_phone_button(text)
            or is_repeat_button(text) or text in (QUIZ_BTN, BOARD_BTN))

def lang_keyboard():
    kb = types.InlineKeyboardMarkup(row_width=2)
    buttons = [types.InlineKeyboardButton(LANG_NAMES[c], callback_data=f"setlang:{c}") for c in SUPPORTED_LANGS]
    for i in range(0, len(buttons), 2):
        kb.row(*buttons[i:i+2])
    return kb

# ---------- /start ----------

@bot.message_handler(commands=["start"])
def cmd_start(message):
    add_known_user(message.from_user)
    # "/start dm" \u2014 mijoz qayerdan kelganini eslab qolamiz
    parts = (message.text or "").split(maxsplit=1)
    if len(parts) > 1 and parts[1].strip():
        src = re.sub(r"[^A-Za-z0-9_\-]", "", parts[1].strip())[:32]
        if src:
            try:
                with DATA_LOCK:
                    users = load_users()
                    rec = users.get(str(message.from_user.id)) or {}
                    if not rec.get("src"):
                        rec["src"] = src
                        rec["src_at"] = int(time.time())
                        users[str(message.from_user.id)] = rec
                        save_json(USERS_FILE, users)
            except Exception:
                pass
    carts.pop(message.from_user.id, None)
    checkout_state.pop(message.from_user.id, None)
    lang = get_user_lang(message.from_user.id, getattr(message.from_user, "language_code", None))
    st = shop_status()
    if st["open"] or is_owner(message.chat.id):
        welcome = t("welcome", lang, biz=BUSINESS_NAME) + lang_hint(lang)
        if not st["open"]:
            welcome = closed_message(lang, st) + "\n\n— — —\n(Siz adminsiz, shuning uchun buyurtma bera olasiz.)"
    else:
        welcome = closed_message(lang, st)
    settings = load_settings()
    kb = main_keyboard(message.from_user.id, message.from_user.username, lang)
    if settings.get("logo_photo_id"):
        bot.send_photo(message.chat.id, settings["logo_photo_id"], caption=welcome, reply_markup=kb)
    else:
        bot.send_message(message.chat.id, welcome, reply_markup=kb)

# ---------- menyuni ko'rsatish (chat fallback) ----------

def sort_menu_by_availability(menu):
    """Mavjud taomlar avval, tugaganlari oxirida — ikkalasi ichida qo'shilgan tartib saqlanadi."""
    def is_sold_out(d):
        stock = d.get("stock")
        return stock is not None and stock <= 0
    return sorted(menu, key=is_sold_out)

def group_menu_by_category(menu):
    """Kategoriya bo'yicha guruhlaydi (CATEGORIES tartibida), har bir guruh ichida
    mavjud taomlar avval, tugaganlari oxirida keladi. Bo'sh kategoriyalar tashlab ketiladi."""
    groups = []
    for cat in CATEGORIES:
        items = [d for d in menu if d.get("category", DEFAULT_CATEGORY) == cat]
        if items:
            groups.append((cat, sort_menu_by_availability(items)))
    return groups

def send_dish_card(chat_id, dish, caption, kb):
    """Taomni rasm bilan yuboradi. Mini App orqali qo'shilgan taomlarda Telegram
    photo_id bo'lmaydi — u holda rasm sayt manzili orqali yuboriladi va
    Telegram bergan photo_id keyingi safar uchun saqlab qo'yiladi."""
    if dish.get("photo_id"):
        try:
            bot.send_photo(chat_id, dish["photo_id"], caption=caption, reply_markup=kb)
            return
        except Exception as e:
            print(f"photo_id bilan yuborib bo'lmadi (#{dish.get('id')}): {e}")
    if dish.get("local_photo") and WEBAPP_URL:
        try:
            sent = bot.send_photo(
                chat_id,
                f"{WEBAPP_URL}/static/dishes/{dish['local_photo']}",
                caption=caption, reply_markup=kb
            )
            try:
                new_id = sent.photo[-1].file_id
                menu = load_menu()
                target = next((d for d in menu if d["id"] == dish["id"]), None)
                if target is not None and not target.get("photo_id"):
                    target["photo_id"] = new_id
                    save_menu(menu)
            except Exception:
                pass
            return
        except Exception as e:
            print(f"Rasmni URL orqali yuborib bo'lmadi (#{dish.get('id')}): {e}")
    bot.send_message(chat_id, caption, reply_markup=kb)

def send_menu(chat_id):
    menu = load_menu()
    if not menu:
        bot.send_message(chat_id, "Menyu hozircha bo'sh.")
        return
    disc = get_discount()
    if disc["active"]:
        bot.send_message(chat_id, f"🏷 Bugun aksiya: barcha taomga −{disc['percent']}% chegirma!")
    for category, dishes in group_menu_by_category(menu):
        emoji = CATEGORY_EMOJI.get(category, "🍽")
        bot.send_message(chat_id, f"{emoji} {category.upper()}")
        for dish in dishes:
            stock = dish.get("stock")
            sold_out = stock is not None and stock <= 0
            unit = discounted_price(dish["price"], disc)
            if unit != dish["price"]:
                caption = f"{dish['name']} — {fmt_sum(unit)}  (eski narx: {fmt_sum(dish['price'])})"
            else:
                caption = f"{dish['name']} — {fmt_sum(dish['price'])}"
            if dish.get("desc"):
                caption += f"\n{dish['desc']}"
            if sold_out:
                caption += "\n❌ Tugadi"
            elif stock is not None:
                caption += f"\n📦 Qoldi: {stock} dona"
            kb = types.InlineKeyboardMarkup()
            if sold_out:
                kb.add(types.InlineKeyboardButton("❌ Tugadi", callback_data="noop"))
            else:
                kb.add(types.InlineKeyboardButton("➕ Savatga qo'shish", callback_data=f"add:{dish['id']}"))
            send_dish_card(chat_id, dish, caption, kb)
    bot.send_message(chat_id, "Tanlab bo'lgach, pastdagi \"🛒 Savat\" tugmasini bosing.")

def _fwd_info(message):
    """Forward qilingan xabardan kim yuborganini aniqlaydi.
    Telegram'ning eski va yangi maydonlarini ham tekshiramiz."""
    uid = uname = name = None

    fu = getattr(message, "forward_from", None)
    if fu is not None:
        uid = getattr(fu, "id", None)
        uname = getattr(fu, "username", None)
        name = " ".join(x for x in [getattr(fu, "first_name", "") or "",
                                    getattr(fu, "last_name", "") or ""] if x).strip()

    if uid is None:
        org = getattr(message, "forward_origin", None)
        su = getattr(org, "sender_user", None) if org is not None else None
        if su is not None:
            uid = getattr(su, "id", None)
            uname = getattr(su, "username", None)
            name = " ".join(x for x in [getattr(su, "first_name", "") or "",
                                        getattr(su, "last_name", "") or ""] if x).strip()
        elif org is not None:
            name = (getattr(org, "sender_user_name", None) or "").strip() or None

    if not name:
        name = (getattr(message, "forward_sender_name", None) or "").strip() or None

    return uid, uname, name

def is_forwarded(message):
    return bool(getattr(message, "forward_date", None)
                or getattr(message, "forward_from", None)
                or getattr(message, "forward_origin", None)
                or getattr(message, "forward_sender_name", None)
                or getattr(message, "forward_from_chat", None))

def tgdraft_card(token, d):
    """Adminga ko'rinadigan qoralama kartasi."""
    satrlar = ["\U0001F4E5 Telegramdan buyurtma (qoralama)", ""]
    satrlar.append(f"\U0001F464 Mijoz: {d.get('name') or '—'}")
    if d.get("username"):
        satrlar.append(f"   @{d['username']}")
    if d.get("tme"):
        satrlar.append(f"   {d['tme']}")
    satrlar.append(f"\U0001F4DE Tel: {d.get('phone') or '— (sahifada yozasiz)'}")
    if d.get("lat") is not None:
        satrlar.append(f"\U0001F4CD Joylashuv: {d['lat']:.5f}, {d['lon']:.5f}")
    elif d.get("map_link"):
        satrlar.append(f"\U0001F517 Xarita havolasi: {d['map_link']}")
    else:
        satrlar.append(f"\U0001F4CD Manzil: {(d.get('address') or '—')[:120]}")
    if d.get("text"):
        satrlar.append("")
        satrlar.append("\U0001F4AC Xabar:")
        satrlar.append(d["text"][:400])
    satrlar.append("")
    satrlar.append("Yetmagan narsa bo'lsa — mijozning boshqa xabarini (joylashuv, "
                   "telefon) shu yerga yana forward qiling, qoralamaga qo'shiladi.")
    satrlar.append("⚠️ Bu buyurtmaga keshbek yozilmaydi.")
    return "\n".join(satrlar)

def tgdraft_kb(token, admin_id, admin_uname, join_to=None):
    kb = types.InlineKeyboardMarkup()
    if WEBAPP_URL:
        ts, sig = sign_user_params(admin_id, admin_uname)
        params = (f"draft={urllib.parse.quote(token)}&uid={admin_id}"
                  f"&uname={urllib.parse.quote(admin_uname or '')}&ts={ts}&sig={sig}&v={ts}")
        kb.add(types.InlineKeyboardButton(
            "\U0001F6D2 Savatni yig'ish",
            web_app=types.WebAppInfo(url=f"{WEBAPP_URL}/tgorder?{params}")))
    if join_to:
        kb.add(types.InlineKeyboardButton("🔗 Oldingi qoralamaga qo'shish",
                                          callback_data=f"tgd:join:{token}:{join_to}"))
    kb.add(types.InlineKeyboardButton("❌ Qoralamani o'chirish",
                                      callback_data=f"tgd:del:{token}"))
    return kb

@bot.message_handler(func=lambda m: (is_forwarded(m)
                                     and is_staff_or_admin(m.chat.id)
                                     and m.from_user.id not in checkout_state
                                     and m.from_user.id not in repeat_state),
                     content_types=["text", "location", "contact", "photo", "venue"])
def handle_forwarded_order(message):
    """Mijozning xabari forward qilindi \u2014 undan buyurtma qoralamasini yasaymiz.

    Matnli xabar har doim YANGI qoralama ochadi: 20 daqiqa ichida ikkita
    alohida buyurtma tushishi mumkin, ularni qo'shib yuborish xato bo'lardi.
    Joylashuv, kontakt va venue esa o'z-o'zidan buyurtma emas \u2014 ular
    aynan o'sha mijozning ochiq qoralamasiga qo'shiladi.
    """
    admin_id = message.chat.id
    uid, uname, name = _fwd_info(message)
    qoshimcha = message.content_type in ("location", "contact", "venue")
    oldingi = tgdraft_same_sender(admin_id, uid, uname, name)

    if qoshimcha and oldingi:
        token, d = oldingi
        join_to = None
    else:
        token = hashlib.md5(f"{admin_id}:{time.time()}:{uid or name}".encode()).hexdigest()[:12]
        d = {"admin_id": admin_id}
        join_to = oldingi[0] if oldingi else None

    if uid and not d.get("user_id"):
        d["user_id"] = uid
    if uname and not d.get("username"):
        d["username"] = uname
        d["tme"] = f"https://t.me/{uname}"
    if name and not d.get("name"):
        d["name"] = name
    if uid and not d.get("tme"):
        d["tme"] = f"tg://user?id={uid}"

    if message.content_type == "location" and message.location:
        d["lat"] = message.location.latitude
        d["lon"] = message.location.longitude
    elif message.content_type == "venue" and getattr(message, "venue", None):
        d["lat"] = message.venue.location.latitude
        d["lon"] = message.venue.location.longitude
        d["address"] = (getattr(message.venue, "address", "") or "").strip()
    elif message.content_type == "contact" and getattr(message, "contact", None):
        d["phone"] = (message.contact.phone_number or "").strip()
        if not d.get("name"):
            d["name"] = " ".join(x for x in [message.contact.first_name or "",
                                             message.contact.last_name or ""] if x).strip()
        if getattr(message.contact, "user_id", None) and not d.get("user_id"):
            d["user_id"] = message.contact.user_id

    matn = (message.text or message.caption or "").strip()
    if matn:
        d["text"] = ((d.get("text", "") + "\n" + matn).strip())[:900]
        link = first_url(matn)
        if link and not d.get("map_link"):
            d["map_link"] = link
        if d.get("lat") is None:
            la, lo = parse_map_link(matn)
            if la is not None:
                d["lat"], d["lon"] = la, lo
        if not d.get("phone"):
            tel = extract_phone(matn)
            if tel:
                d["phone"] = tel
        if not d.get("address") and d.get("lat") is None:
            d["address"] = matn[:200]

    tgdraft_put(token, d)
    matn_karta = tgdraft_card(token, d)
    if qoshimcha and oldingi:
        matn_karta = "\u2795 Oldingi qoralamaga qo'shildi.\n\n" + matn_karta
    elif join_to:
        matn_karta += ("\n\n\u2139\ufe0f Shu mijozdan yaqinda boshqa qoralama ham ochilgan. "
                       "Bu bitta buyurtmaning davomi bo'lsa, pastdagi "
                       "\u00abOldingi qoralamaga qo'shish\u00bb ni bosing.")
    bot.send_message(admin_id, matn_karta,
                     reply_markup=tgdraft_kb(token, admin_id,
                                             message.from_user.username, join_to),
                     disable_web_page_preview=True)

@bot.callback_query_handler(func=lambda c: c.data.startswith("tgd:join:"))
def cb_tgdraft_join(call):
    """Yangi qoralamani oldingisiga qo'shadi."""
    if not is_staff_or_admin(call.message.chat.id):
        bot.answer_callback_query(call.id, "Ruxsat yo'q.")
        return
    parts = call.data.split(":")
    if len(parts) < 4:
        bot.answer_callback_query(call.id, "Noto'g'ri so'rov.")
        return
    yangi_t, eski_t = parts[2], parts[3]
    yangi, eski = tgdraft_get(yangi_t), tgdraft_get(eski_t)
    if not yangi or not eski:
        bot.answer_callback_query(call.id, "Qoralamalardan biri topilmadi.", show_alert=True)
        return
    eski = tgdraft_merge(eski, yangi)
    tgdraft_put(eski_t, eski)
    tgdraft_drop(yangi_t)
    bot.answer_callback_query(call.id, "Qo'shildi.")
    try:
        bot.edit_message_text("\u2795 Oldingi qoralamaga qo'shildi.\n\n" + tgdraft_card(eski_t, eski),
                              call.message.chat.id, call.message.message_id,
                              reply_markup=tgdraft_kb(eski_t, call.message.chat.id,
                                                      call.from_user.username),
                              disable_web_page_preview=True)
    except Exception:
        pass

@bot.callback_query_handler(func=lambda c: c.data.startswith("tgd:del:"))
def cb_tgdraft_del(call):
    if not is_staff_or_admin(call.message.chat.id):
        bot.answer_callback_query(call.id, "Ruxsat yo'q.")
        return
    tgdraft_drop(call.data.split(":", 2)[2])
    bot.answer_callback_query(call.id, "Qoralama o'chirildi.")
    try:
        bot.edit_message_text("❌ Qoralama o'chirildi.",
                              call.message.chat.id, call.message.message_id)
    except Exception:
        pass

@bot.message_handler(func=lambda m: m.text == "🍽 Menyu" and m.from_user.id not in checkout_state)
def handle_menu_button(message):
    send_menu(message.chat.id)

@bot.callback_query_handler(func=lambda c: c.data == "show_menu")
def cb_show_menu(call):
    send_menu(call.message.chat.id)
    bot.answer_callback_query(call.id)

@bot.callback_query_handler(func=lambda c: c.data.startswith("add:"))
def cb_add_dish_to_cart(call):
    dish_id = int(call.data.split(":")[1])
    menu = load_menu()
    dish = next((d for d in menu if d["id"] == dish_id), None)
    if not dish:
        bot.answer_callback_query(call.id, "Bu taom endi mavjud emas.")
        return
    user_id = call.from_user.id
    cart = carts.setdefault(user_id, {})
    current_qty = cart.get(dish_id, 0)
    stock = dish.get("stock")
    if stock is not None and current_qty + 1 > stock:
        bot.answer_callback_query(call.id, f"Faqat {stock} dona qoldi.")
        return
    cart[dish_id] = current_qty + 1
    bot.answer_callback_query(call.id, f"{dish['name']} savatga qo'shildi ✅")

# ---------- savat (chat fallback) ----------

def cart_summary_text(user_id):
    menu = {d["id"]: d for d in load_menu()}
    cart = carts.get(user_id, {})
    if not cart:
        return "Savatingiz bo'sh.", 0
    lines = []
    total = 0
    original = 0
    disc = get_discount()
    for dish_id, qty in cart.items():
        dish = menu.get(dish_id)
        if not dish:
            continue
        unit = discounted_price(dish["price"], disc)
        line_total = unit * qty
        total += line_total
        original += dish["price"] * qty
        lines.append(f"{dish['name']} × {qty} = {fmt_sum(line_total)}")
    text = "🛒 Savatingiz:\n" + "\n".join(lines)
    if disc["active"] and original > total:
        text += f"\n\n🏷 Aksiya −{disc['percent']}%: {fmt_sum(original)} → {fmt_sum(total)}"
    text += f"\n\nJami: {fmt_sum(total)}"
    return text, total

def build_cart_keyboard(user_id):
    cart = carts.get(user_id, {})
    menu = {d["id"]: d for d in load_menu()}
    kb = types.InlineKeyboardMarkup(row_width=3)
    for dish_id in cart:
        dish = menu.get(dish_id)
        if not dish:
            continue
        kb.row(
            types.InlineKeyboardButton("➖", callback_data=f"dec:{dish_id}"),
            types.InlineKeyboardButton(dish["name"], callback_data="noop"),
            types.InlineKeyboardButton("➕", callback_data=f"add:{dish_id}"),
        )
    if cart:
        kb.add(types.InlineKeyboardButton("✅ Buyurtma berish", callback_data="checkout"))
        kb.add(types.InlineKeyboardButton("🗑 Savatni tozalash", callback_data="clear_cart"))
    return kb

def send_cart(chat_id, user_id):
    text, _ = cart_summary_text(user_id)
    bot.send_message(chat_id, text, reply_markup=build_cart_keyboard(user_id))

@bot.message_handler(func=lambda m: m.text == "🛒 Savat" and m.from_user.id not in checkout_state)
def handle_cart_button(message):
    send_cart(message.chat.id, message.from_user.id)

@bot.callback_query_handler(func=lambda c: c.data == "show_cart")
def cb_show_cart(call):
    send_cart(call.message.chat.id, call.from_user.id)
    bot.answer_callback_query(call.id)

@bot.callback_query_handler(func=lambda c: c.data.startswith("dec:"))
def cb_dec_dish(call):
    dish_id = int(call.data.split(":")[1])
    user_id = call.from_user.id
    cart = carts.setdefault(user_id, {})
    if dish_id in cart:
        cart[dish_id] -= 1
        if cart[dish_id] <= 0:
            del cart[dish_id]
    text, _ = cart_summary_text(user_id)
    try:
        bot.edit_message_text(text, call.message.chat.id, call.message.message_id,
                               reply_markup=build_cart_keyboard(user_id))
    except Exception:
        pass
    bot.answer_callback_query(call.id)

@bot.callback_query_handler(func=lambda c: c.data == "clear_cart")
def cb_clear_cart(call):
    carts[call.from_user.id] = {}
    bot.edit_message_text("Savat tozalandi.", call.message.chat.id, call.message.message_id)
    bot.answer_callback_query(call.id)

@bot.callback_query_handler(func=lambda c: c.data == "noop")
def cb_noop(call):
    bot.answer_callback_query(call.id)

# ---------- checkout (chat fallback: ism -> telefon -> lokatsiya) ----------

@bot.callback_query_handler(func=lambda c: c.data == "checkout")
def cb_checkout(call):
    user_id = call.from_user.id
    if not carts.get(user_id):
        bot.answer_callback_query(call.id, "Savatingiz bo'sh.")
        return
    lang = get_user_lang(user_id)
    st = shop_status()
    if not st["open"] and not is_owner(call.message.chat.id):
        bot.answer_callback_query(call.id, t("closed_short", lang), show_alert=True)
        bot.send_message(call.message.chat.id, closed_message(lang, st))
        return
    checkout_state[user_id] = {"step": "name"}
    bot.send_message(call.message.chat.id, t("ask_name", lang), reply_markup=types.ReplyKeyboardRemove())
    bot.answer_callback_query(call.id)

def location_keyboard(lang):
    kb = types.ReplyKeyboardMarkup(resize_keyboard=True, one_time_keyboard=True)
    kb.add(types.KeyboardButton(t("btn_location", lang), request_location=True))
    return kb

def phone_keyboard(lang):
    kb = types.ReplyKeyboardMarkup(resize_keyboard=True, one_time_keyboard=True)
    kb.add(types.KeyboardButton(t("btn_send_phone", lang), request_contact=True))
    kb.add(types.KeyboardButton(t("btn_no_phone", lang)))
    return kb

def order_phone_line(order):
    """Raqam bo'lsa raqam, bo'lmasa Telegram orqali bog'lanish ko'rsatmasi."""
    phone = (order.get("phone") or "").strip()
    if phone:
        return f"📞 {phone}"
    uname = order.get("username")
    if uname:
        return f"📱 Raqam yo'q — Telegram: @{uname}\n   ↩️ Shu xabarga \"Reply\" qilib yozsangiz, mijozga boradi."
    return "📱 Raqam yo'q — mijozda username ham yo'q\n   ↩️ Shu xabarga \"Reply\" qilib yozsangiz, mijozga boradi."

@bot.message_handler(func=lambda m: m.from_user.id in checkout_state, content_types=["text", "location", "contact"])
def handle_checkout_steps(message):
    user_id = message.from_user.id
    state = checkout_state[user_id]
    step = state["step"]
    lang = get_user_lang(user_id, getattr(message.from_user, "language_code", None))

    if step == "name":
        if message.content_type != "text":
            return
        state["name"] = message.text.strip()
        state["step"] = "phone"
        bot.send_message(message.chat.id, t("ask_phone", lang), reply_markup=phone_keyboard(lang))
        return

    if step == "phone":
        if message.content_type == "contact":
            state["phone"] = (message.contact.phone_number or "").strip()
        elif message.content_type == "text":
            txt = message.text.strip()
            state["phone"] = "" if is_no_phone_button(txt) else txt
        else:
            return
        state["step"] = "address"
        bot.send_message(message.chat.id, t("ask_address", lang), reply_markup=location_keyboard(lang))
        return

    if step == "address":
        if message.content_type == "location":
            state["latitude"] = message.location.latitude
            state["longitude"] = message.location.longitude
            state["address_text"] = None
        else:
            state["latitude"] = None
            state["longitude"] = None
            state["address_text"] = message.text.strip()
        order, error = create_order(
            items_cart=carts.get(user_id, {}),
            customer_name=state["name"],
            phone=state["phone"],
            latitude=state.get("latitude"),
            longitude=state.get("longitude"),
            address_text=state.get("address_text"),
            note="",
            tg_user_id=user_id,
            username=message.from_user.username,
        )
        checkout_state.pop(user_id, None)
        if error:
            bot.send_message(
                message.chat.id,
                f"❌ {error}\nIltimos, savatingizni tekshirib, qayta urinib ko'ring.",
                reply_markup=main_keyboard(message.from_user.id, message.from_user.username)
            )
            return
        carts[user_id] = {}
        # Chek create_order ichida avtomatik mijozga yuboriladi — bu yerda qayta yuborish shart emas.
        return

# ---------- buyurtma yaratish (chat va Mini App uchun umumiy) ----------

def create_order(items_cart, customer_name, phone, latitude, longitude, address_text, note, tg_user_id, username, use_cashback=False, extra=None, custom_items=None):
    """Muvaffaqiyatli bo'lsa (order, None), zaxira yetmasa (None, xato_matni) qaytaradi.

    custom_items — menyuda yo'q qatorlar: [{"name", "price", "qty", "unit"}].
    Masalan "1 kg osh" yoki "0.5 kg go'sht".
    """
    with DATA_LOCK:
        order, error = _create_order_locked(items_cart, customer_name, phone, latitude, longitude,
                                            address_text, note, tg_user_id, username, use_cashback,
                                            extra, custom_items)
    if error:
        return None, error
    # xabarlarni qulfdan tashqarida yuboramiz — boshqa mijozlar kutib qolmasin
    if OWNER_CHAT_ID:
        notify_owner_new_order(order)
    if tg_user_id:
        try:
            bot.send_message(tg_user_id, build_customer_receipt_text(order),
                             reply_markup=main_keyboard(tg_user_id, username))
        except Exception:
            pass
    return order, None

def _create_order_locked(items_cart, customer_name, phone, latitude, longitude, address_text, note, tg_user_id, username, use_cashback=False, extra=None, custom_items=None):
    full_menu = load_menu()
    menu = {d["id"]: d for d in full_menu}
    items = []
    total = 0
    original_total = 0
    disc = get_discount()
    parsed_cart = []
    for dish_id, qty in items_cart.items():
        dish_id = int(dish_id)
        qty = int(qty)
        dish = menu.get(dish_id)
        if not dish or qty <= 0:
            continue
        stock = dish.get("stock")
        if stock is not None and qty > stock:
            if stock <= 0:
                return None, f"\"{dish['name']}\" tugagan. Iltimos, savatdan olib tashlang."
            return None, f"\"{dish['name']}\" uchun faqat {stock} dona qoldi (siz {qty} dona so'ragansiz)."
        parsed_cart.append((dish, qty))
        unit = discounted_price(dish["price"], disc)
        item = {"name": dish["name"], "price": unit, "qty": qty}
        if unit != dish["price"]:
            item["old_price"] = dish["price"]
        # set tarkibini buyurtma paytidagi holatda saqlaymiz — keyin menyu o'zgarsa ham chek o'zgarmaydi
        skeys = dish_set_keys(dish)
        if skeys:
            item["set"] = skeys
        if (dish.get("set_extra") or "").strip():
            item["set_extra"] = dish["set_extra"].strip()
        items.append(item)
        total += unit * qty
        original_total += dish["price"] * qty

    # Menyuda yo'q qatorlar: kilogramm bilan sotiladigan narsalar va boshqalar.
    # Zaxira tekshirilmaydi, miqdori kasr bo'lishi mumkin (0.5 kg).
    for ci in (custom_items or []):
        nomi = str(ci.get("name") or "").strip()[:60]
        try:
            narx = money(float(ci.get("price")))
            miqdor = round(float(ci.get("qty") or 1), 3)
        except Exception:
            continue
        if not nomi or narx < 0 or miqdor <= 0:
            continue
        birlik = str(ci.get("unit") or "").strip()[:8]
        qator = {"name": nomi, "price": narx, "qty": miqdor, "free": True}
        if birlik:
            qator["unit"] = birlik
        items.append(qator)
        total += narx * miqdor
        original_total += narx * miqdor

    if not items:
        return None, "Savat bo'sh."

    # «O'zingiz yig'ing» qoidasi: butun buyurtma shu bo'limdan iborat bo'lsa,
    # jami belgilangan summadan kam bo'lmasligi kerak. Boshqa taom ham olingan
    # bo'lsa (masalan lag'mon + kotlet) qoida qo'llanmaydi.
    eng_kam = builder_min()
    if eng_kam > 0 and parsed_cart and not (custom_items or []):
        hammasi_yigma = all((d.get("category") or DEFAULT_CATEGORY) == BUILDER_CATEGORY
                            for d, _ in parsed_cart)
        if hammasi_yigma and money(total) < eng_kam:
            yetmaydi = money(eng_kam - money(total))
            return None, (f"Eng kam buyurtma summasi \u2014 {fmt_sum(eng_kam)}. "
                          f"Hozir {fmt_sum(total)}, yana {fmt_sum(yetmaydi)} qo'shsangiz bo'ldi.")

    # zaxirani kamaytiramiz
    for dish, qty in parsed_cart:
        if dish.get("stock") is not None:
            dish["stock"] = max(0, dish["stock"] - qty)
    save_menu(full_menu)

    # keshbek: balansdan buyurtma summasidan oshmaydigan qismi ishlatiladi
    cb_used = 0.0
    if use_cashback and tg_user_id and get_cashback_cfg()["active"]:
        cb_used = money(min(cashback_balance(tg_user_id), money(total)))
        if cb_used < 0.01:
            cb_used = 0.0

    # avans: oldindan to'langan puli bo'lsa, qolgan summadan o'zi yechiladi.
    # Keshbekdan keyin hisoblanadi — avval bonus, keyin haqiqiy pul.
    adv_used = advance_for_order(tg_user_id, money(total) - cb_used)

    orders = load_orders()
    created_at = int(time.time())
    day_key = today_key(created_at)
    order = {
        "id": next_order_id(orders),
        "day_key": day_key,
        "daily_number": next_daily_number(orders, day_key),
        "customer_name": customer_name,
        "phone": phone,
        "latitude": latitude,
        "longitude": longitude,
        "address_text": address_text,
        "note": note,
        "items": items,
        "total": total,
        "original_total": original_total,
        "discount_percent": disc["percent"] if disc["active"] else 0,
        "status": "Yangi",
        "cashback_used": cb_used,
        "cashback_earned": 0.0,
        "cashback_credited": False,
        "advance_used": adv_used,
        "printed": False,
        "payment": "naqd",
        "created_at": created_at,
        "user_id": tg_user_id,
        "username": username,
    }
    if extra:
        order.update(extra)
    orders.append(order)
    save_orders(orders)
    if cb_used > 0:
        cashback_move(tg_user_id, -cb_used, order["id"], "buyurtmada ishlatildi")
    if adv_used > 0:
        account_move(tg_user_id, -adv_used, order["id"], "avans buyurtmada ishlatildi")
    if tg_user_id:
        try:
            users = load_users()
            uid = str(tg_user_id)
            rec = users.get(uid) or {"first_seen": int(time.time())}
            rec["name"] = customer_name or rec.get("name") or "Mijoz"
            rec["username"] = username or rec.get("username")
            rec["last_seen"] = int(time.time())
            rec["blocked"] = rec.get("blocked", False)
            users[uid] = rec
            save_json(USERS_FILE, users)
        except Exception:
            pass
    return order, None

def build_customer_receipt_text(order, lang=None):
    lang = lang or get_user_lang(order.get("user_id"))
    text = (
        t("receipt_title", lang, no=order["daily_number"]) + "\n\n"
        f"{order_items_text(order, lang)}\n\n"
        + discount_line_for_customer(order, lang)
        + t("receipt_total_plain" if (order_cashback_used(order) > 0
                                       or order_advance_used(order) > 0)
            else "receipt_total", lang, sum=fmt_sum(order["total"])) + "\n"
        + cashback_line_for_customer(order, lang)
        + f"{order_address_line(order)}\n"
    )
    text += account_line_for_customer(order, lang)
    if order.get("note"):
        text += f"📝 {order['note']}\n"
    if not (order.get("phone") or "").strip():
        text += t("receipt_nophone", lang)
    text += t("receipt_tail", lang)
    return text

def account_line_for_customer(order, lang):
    """Mijoz chekida: hisobida qarz yoki avans bo'lsa ko'rsatamiz."""
    try:
        bal = account_balance(order.get("user_id"))
    except Exception:
        return ""
    if not bal:
        return ""
    if bal < 0:
        return t("acct_receipt_debt", lang, amt=fmt_sum(-bal))
    return t("acct_receipt_adv", lang, amt=fmt_sum(bal))

def cashback_line_for_customer(order, lang):
    """Keshbek va avans qatorlari, oxirida naqd beriladigan summa."""
    used = order_cashback_used(order)
    adv = order_advance_used(order)
    if used <= 0 and adv <= 0:
        return ""
    out = ""
    if used > 0:
        out += t("cb_line_only", lang, amt=fmt_sum(used))
    if adv > 0:
        out += t("adv_line_only", lang, amt=fmt_sum(adv))
    naqd = order_cash_due(order)
    if naqd > 0:
        out += t("pay_line_only", lang, pay=fmt_sum(naqd))
    else:
        out += t("paid_full_line", lang)
    return out

def discount_line_for_customer(order, lang):
    pct = order.get("discount_percent") or 0
    old = order.get("original_total")
    if not pct or not old or old <= order.get("total", 0):
        return ""
    return t("discount_line", lang, pct=pct,
             old=fmt_sum(old), new=fmt_sum(order["total"]))

def fmt_qty(it):
    """Miqdorni chiroyli ko'rsatadi: 2 → "2", 0.5 kg → "0.5 kg"."""
    q = it.get("qty", 1)
    try:
        qf = float(q)
    except Exception:
        return str(q)
    s = str(int(qf)) if abs(qf - round(qf)) < 1e-9 else ("%.3f" % qf).rstrip("0").rstrip(".")
    u = (it.get("unit") or "").strip()
    return f"{s} {u}" if u else s

def order_items_text(order, lang="uz"):
    lines = []
    for it in order["items"]:
        line = f"{it['name']} × {fmt_qty(it)} = {fmt_sum(it['price']*it['qty'])}"
        if it.get("cancelled"):
            line = f"❌ {line}  (bekor qilindi)"
        lines.append(line)
        s = item_set_line(it, lang, with_emoji=True)
        if s and not it.get("cancelled"):
            lines.append(f"   └ {s}")
    return "\n".join(lines)

# ---------- oshxona cheki (termoprinter) ----------

RECEIPT_WIDTH = int(os.environ.get("RECEIPT_WIDTH", "32"))  # 58mm = 32, 80mm = 48

# Termoprinterlar ko'pincha faqat oddiy belgilarni biladi — xavflilarini almashtiramiz
_SAFE_MAP = {
    "\u2019": "'", "\u2018": "'", "\u02bb": "'", "\u02bc": "'", "\u00b4": "'",
    "\u201c": '"', "\u201d": '"', "\u201e": '"', "\u00ab": '"', "\u00bb": '"',
    "\u2014": "-", "\u2013": "-", "\u2212": "-", "\u2026": "...",
    "\u00a0": " ", "\u2022": "*", "\u20bd": "RUB",
}

def ascii_safe(text):
    out = []
    for ch in str(text):
        out.append(_SAFE_MAP.get(ch, ch))
    return "".join(out)

def _rline(left, right, width):
    """Chap va o'ng matnni chekning ikki chetiga joylaydi."""
    space = width - len(left) - len(right)
    if space < 1:
        left = left[:max(0, width - len(right) - 1)]
        space = max(1, width - len(left) - len(right))
    return left + " " * space + right

def _wrap(text, width):
    width = max(4, int(width))
    out, line = [], ""
    for word in str(text).split():
        while len(word) > width:          # bitta uzun so'z — majburan bo'lamiz
            if line:
                out.append(line)
                line = ""
            out.append(word[:width])
            word = word[width:]
        if not word:
            continue
        if not line:
            line = word
        elif len(line) + 1 + len(word) <= width:
            line += " " + word
        else:
            out.append(line); line = word
    if line:
        out.append(line)
    return out or [""]

def _labeled(label, value, w):
    """'Mijoz: Ali' kabi qatorni qog'oz kengligiga moslab bo'ladi."""
    value = str(value if value is not None else "")
    if len(label) + len(value) <= w:
        return [label + value]
    if len(label) + 6 > w:               # yorliqning o'zi qatorni to'ldirib qo'ysa
        out = _wrap(label.strip(), w)
        out += ["  " + r for r in _wrap(value, max(4, w - 2))]
        return out
    inner = max(4, w - len(label))
    pad = " " * len(label)
    rows = _wrap(value, inner)
    return [(label if i == 0 else pad) + r for i, r in enumerate(rows)]

def _center(text, w):
    """Sig'masa bo'lib tashlaydi, aks holda o'rtaga qo'yadi."""
    rows = _wrap(text, w)
    return [r.center(w).rstrip() for r in rows]

# Chekning pastki yozuvi — printerning o'z shrifti chiroyli emas, shuning uchun
# uni logo kabi rasm qilib yuboramiz. 1152 nuqta eni: 80 mm uchun ikki barobar
# zaxira, 58 mm qog'ozga kichraytirilganda ham harflar toza chiqadi.
RECEIPT_FOOT_TEXT = "Ibodatga quvvat bo'lsin"
RECEIPT_FOOT_PNG = (
    "iVBORw0KGgoAAAANSUhEUgAABIAAAAB2AQAAAACYV9XgAAAJD0lEQVR42u2bvW7ryhHHf7tiJBaCzSpQcRIzb2CkOlXEIkUe"
    "Q8gTuEwVL4IUJ9X1A6Twm2TPRYpT+gGCgCcBEpf0vQZCCxQnxS4pkiL1deRrF1oYlvi1+9+Z2Zn/zFJKeF9NcwZ0BnQGdAZ0"
    "BvQOAKV7ARLTvbh55ui2bB1dA8lOQN/b7sXNM0e3SWuiwNdKSqtwANDTBuSn5GR4PreOypyXuDp4Xm4C+qyUkqjbyUt0Mjwv"
    "7akVyFosmWwCshtKBshPZ8SPnZ7Dsmng5s1XWdaWvX1zQGk8BOeNANlkhx+6gclk49Ll6RB86BybkdkK6AJmbPqc03mhUQcP"
    "LLYCUrAgfk0lmQNjWf/9rwZRwXqdJccZ9dcjw9pLz6y6mVdyDKD0SGH0eldp62HAMW4PFJWB//lQH9irlyaESH2LH5I/nsSI"
    "PjW+T8dHATID+j9O1UXTJeTHAKpwlBxo3H2+rDwBhS1P6YD0CQAVR4Y+eS2S/7h2ad9ApU8I6KRu6ABAzl3ctXzH39ffxX38"
    "qyM4ifo88hPAw/p41ezCty+N3Oau0rKIiOFWMuYWERHLpYiIUSlzEctEpACUCNwikjIS1zKu8omIuRThysClE8g8RUmGEhGA"
    "WxGxiHsK5iKMJONKJOVSROxcJJtn3IqIiG4LKAFJ+AFYGUncjF7g2cUlN42YlV87dzzm8GS6WYW7JomXihfQynXxBUxQRY0f"
    "XAIgEXfcb6hsBQ+wdEJ8doazBGIfAB7hR8WqFq8YlhkSwSrpLHAtBr40HeAzJPAIS0jCajxJJAT+hBg/iG6v7dzZxX0dhPJ1"
    "PCKFUlPUtlqCLLY4rqIT1FK4BzFcX1cYSZfAylBWner2kiicXLJ6XT2osl4qFgh4RPxQRcsTp3AzZmRQdsb0mVtTdtZp5sRo"
    "ubR14K0m+48KfxPQw4wSLDE5WEIAq5Upqkx/lBOSKmzpJ6AbfnOGMspOF4yZcJ1hFi2vmCzIETBrF5Ii9WTzKhq0jPq/CBj1"
    "Twow/M8ABCT1TKcBEWhi8TP8he88AAI0xFFECCZBEbXMavRXCkomf6iFglVUkyWrvLpuMUsDwlhRIigWPhYJV5bbsgRN5pRk"
    "3AwXEagURrZDe00KYCcZV97NBBoomAUNZ6lJyonPAW57HKMmwZSEGKFk3I2QRYPDWffPhJ7ZxXVP4YB/DxUlObFe27qpu0pR"
    "xrjjJqCgModkiOsrNz0PzCiCJoTSQcj9UO0yS+QVo7oDxkCErgbVnbGte9QUnf52xKWoGikJBmOwETfXXioT9MWysBo2rkeX"
    "FsuKoajMB6QbmaVBVWyDUK/lnDYZUmsRhtUzuj+se0Gh2t4NwGwja9YAiCaRQbbWvGJ1LeK4T2URZJ38sOwmEA062zecHuSK"
    "CdjdDFh37c59SbP+vNX0K76+aoCy10qS9RfTiFXBoQTN6G6MStT2JNkhjffJBsojGGOyMYV46JGkCSlSezHuxWxwuVWGkrZ9"
    "Wryx+qOgJ7nyJioaEIqQsA+2/dyRZvK3dA8Jtdzi7Lp7eTpr+4n+Np5uU2kdztUOlYWNFeVwTTYyvdEQ4Y+dURjIQWXD1R3b"
    "ZG2vuteROgsw7FfhNjUXPh6Q0VvDB8N7GP3tbiugHRWz3dPOCkfqsnivnDrp01nQ13HTWJ82txzCfea+CoZNbf1tdbjKoo0J"
    "fBq4M6wjc1rll7u7NocCWjUHTHdsouUOfkqylymFfeWaXYCeO6413LN+sNrjnnFf0WAXoIcNc3scujWALIYIrOnzMJte0rQp"
    "Uw+gfIMbWq7S+tasJCLlMtteRXL51iTvp1oNmSx6aOjOaL/uQPH8TIzlZlfVxkDKx90imvUERH3ANoVZRSRO0kPUKoHQRyzL"
    "YRuxA4CiLkEIWhJWZpuzLtcat4odYduBLg+UUNl0khGM2xAHKfXWGENru3w3IDsUJi5gtg9b3FUErQVlp3sAireNqNKtmZr3"
    "mcs9i8Sf+8So+3YmvKDSjlGJKpuRLuiyRoNyPQa9gupauSR9CaUeEFDcQ1OXeu8SuuxZRd+TDw3kQHmwZ1IVbt9sMIfUqZNo"
    "uCad7ahGJztq66qZkw1Vv3V/fTzpU/p997WRgtxbS3bAtoc6rJIfOly1oDL/xdY95sPDB2vvWni5ZV0LNYdU8i0+ABs/pcBL"
    "K4bCFQS1K9L6mWbe9NNm9cxfe3DTk9rOtZuX3iqQ9glfgrIQ1nVh32H6H8WLCqkrMjTLlEnLmmOg9BrPl6a6OSDavT/UBJQK"
    "oMkxao2k8G4uuwd4MVCu1hUop86yZxTxXrLw/MkUjnSWLQ9lgqF9ewtkJRrFUtAEDolmFTpbf3JVyTuFBLVlGAso/AZFMw8y"
    "aLf6VrGTlM0JCXj0pbmMrH51KPW6T2tAbk+Bp98SgJFfE6BZ/S6qfHW2LtnlTjO5G/kvpmY2jxupWUBR2yB8HxGheflS8e7c"
    "x+57HnngmXs/S7f/A5IBXLqDSxHgmon7GEkGIzGAEgMzlIhICgETEQMfQdwOj4jlVsTCFKRojMDc7Q7NRaSsvPlVCUqcPap6"
    "N8g2+YCrimIg4cV9rAirJS0kELswGnkrTvxf6NZZjAFHrhPddDvecyR+OSQGiEuQW+A3PjbrDcY3c1QsqZ5Wn5yDmTkrNXGd"
    "c4VeR3GPc4ng9275j6t7Vc3xvGJvmrJINlfZzwzKwNg9c80oBGJ3h4ZFWQ2l1mnMwhnQqC/n8r7MUaifO2QzGgX5i+57PB0J"
    "hTdcAMpyAUyZusE+uIxl5Lcl7JSLOo1xsx0zDfy2SF08G3vCvPCe4VeWj45Fr8m/snzYZPnSaP92H9+JiMiPrXOFSMZcYC5P"
    "9f3lbcFkfWur5f5zXp1wvZbz5k3fbT6H7N1SbiV1C6luDtApmz7sNYUZvJ+3hdNdDP4nf31Zwbt6n9r+JK89HjxCdn4Fnm8t"
    "fZ5/JHAGtC0/Lt8ToOR1X5A9RmWG4rCtjNcFFHPfUxMuTgxI7f9i39d4kqtOovc1VuWbSSjiRXUDbHzKn+scKqFVAIyK7qmr"
    "9K0kpAGm72jZK9tbyI3fbtl/9KBetR3CSSc2+WX7zOj0P2xW599KnwGdAZ0BnQG9c0D/B5yHN1HqfFYmAAAAAElFTkSuQmCC"
)

@app.route("/static/chek_pastki.png")
def chek_pastki_png():
    """Chek pastidagi yozuvning rasmi (oshxona sahifasi shuni printerga yuboradi)."""
    import base64
    data = base64.b64decode(RECEIPT_FOOT_PNG)
    resp = app.response_class(data, mimetype="image/png")
    resp.headers["Cache-Control"] = "public, max-age=604800"
    return resp


RECEIPT_INDENT = int(os.environ.get("RECEIPT_INDENT", "2"))   # yozuvlarni ichkariga surish

def _blk(text, style="n"):
    return {"t": text, "s": style}

def _fits_big(text, w):
    """Ikki barobar kattalikda qator qog'ozga sig'adimi (ustunlar yarmiga tushadi)."""
    return len(text) <= max(8, w // 2)

def build_receipt_blocks(order, width=None, safe=True, header=True):
    """Chek — har qatori o'z uslubi bilan.
    Uslublar: n oddiy, b qalin, d ikki barobar, db ikki barobar qalin,
    hr ajratuvchi chiziq, foot pastki yozuv (rasm bo'lib chiqadi)."""
    w = width or RECEIPT_WIDTH
    ind = " " * max(0, RECEIPT_INDENT)
    tw = max(8, w - len(ind))          # surilgan matn uchun qolgan kenglik
    B = []

    def add(rows, style="n"):
        for r in rows:
            B.append(_blk(ind + r if r else "", style))

    if header:
        add(_wrap(BUSINESS_NAME.upper(), tw))
    B.append(_blk("-" * w, "hr"))
    created = datetime.fromtimestamp(order.get("created_at", int(time.time())), TIMEZONE)
    add([f"Buyurtma #{order.get('daily_number', '?')}"])
    add(_labeled("Sana: ", created.strftime("%d.%m.%Y %H:%M"), tw))
    B.append(_blk("", "n"))
    # ism va telefon — kuryer eng ko'p qaraydigan ikki qator, taom nomi kabi qalin
    add(_labeled("Mijoz: ", order.get("customer_name") or "-", tw), "b")
    tel = (order.get("phone") or "").strip()
    if tel:
        add(_labeled("Tel: ", tel, tw), "b")
    else:
        add(_labeled("Tel: ", "yo'q (Telegram orqali)" if tw >= 28 else "yo'q, Telegram", tw), "b")
    if order.get("username"):
        add(_labeled("TG: ", "@" + str(order["username"]), tw))
    if order.get("latitude") is not None:
        add(_labeled("Manzil: ", "xaritada yuborilgan" if tw >= 28 else "xaritada", tw))
        add(_labeled("  ", f"{order['latitude']:.5f}, {order['longitude']:.5f}", tw))
    else:
        add(_labeled("Manzil: ", order.get("address_text") or "-", tw))
    B.append(_blk("-" * w, "hr"))

    for it in order.get("items", []):
        if it.get("cancelled"):
            continue
        add(_wrap(it["name"], tw), "b")           # taom nomi qalin
        qty_line = f"{fmt_qty(it)} x {fmt_sum(it['price'])} = {fmt_sum(it['price'] * it['qty'])}"
        add(_labeled("  ", qty_line, tw))

    B.append(_blk("-" * w, "hr"))
    pct = order.get("discount_percent") or 0
    old = order.get("original_total")
    if pct and old and old > order.get("total", 0):
        add(_labeled("Oldingi: " if tw < 26 else "Oldingi summa: ", f"{old:.0f}", tw))
        add(_labeled(f"Aksiya -{pct}%: ", f"-{old - order['total']:.0f}", tw))
    used_cb = order_cashback_used(order)
    used_adv = order_advance_used(order)
    if used_cb > 0:
        add(_labeled("Keshbek: ", "-" + fmt_sum(used_cb), tw))
    if used_adv > 0:
        add(_labeled("Avansdan: ", "-" + fmt_sum(used_adv), tw))

    # Summalar — katta harfda. Sig'masa oddiy o'lchamga tushamiz.
    B.append(_blk("", "n"))
    jami = " " + f"JAMI: {fmt_sum(order.get('total', 0))}"
    if _fits_big(jami, w):
        B.append(_blk(jami, "d"))
    else:
        add([jami.strip()], "b")
    if used_cb > 0 or used_adv > 0:
        naqd = " " + f"TO'LOVGA: {fmt_sum(order_cash_due(order))}"
        if _fits_big(naqd, w):
            B.append(_blk(naqd, "db"))
        else:
            add([naqd.strip()], "b")
    B.append(_blk("", "n"))

    if order_on_account(order):
        pay = "To'lov: HISOBGA (naqd emas)" if tw >= 28 else "To'lov: HISOBGA"
    elif order_cash_due(order) <= 0:
        pay = "To'lov: TO'LANGAN (naqd emas)" if tw >= 28 else "To'lov: TO'LANGAN"
    elif used_adv > 0 and used_cb > 0:
        pay = "To'lov: NAQD + KESHBEK + AVANS" if tw >= 32 else "NAQD+KESHBEK+AVANS"
    elif used_adv > 0:
        pay = "To'lov: NAQD + AVANS" if tw >= 24 else "NAQD + AVANS"
    elif used_cb > 0:
        pay = "To'lov: NAQD + KESHBEK" if tw >= 24 else "NAQD + KESHBEK"
    else:
        pay = "To'lov: NAQD (yetkazishda)" if tw >= 28 else "To'lov: NAQD"
    add(_wrap(pay, tw))

    try:
        bal = account_balance(order.get("user_id"))
    except Exception:
        bal = 0
    if bal:
        add(_labeled("Qarzi: " if bal < 0 else "Avansi: ", fmt_sum(abs(bal)), tw))

    if order.get("note"):
        B.append(_blk("-" * w, "hr"))
        add(["IZOH:"], "b")
        for ln in _wrap(order["note"], max(4, tw - 2)):
            add(["  " + ln])

    B.append(_blk("-" * w, "hr"))
    B.append(_blk("", "n"))
    B.append(_blk(RECEIPT_FOOT_TEXT, "foot"))

    if safe:
        for b in B:
            b["t"] = ascii_safe(b["t"])
    return B


def build_receipt_lines(order, width=None, safe=True, header=True):
    """Oddiy matn ko'rinishi — ko'rib turish, nusxalash va tizim chopi uchun."""
    return [x["t"] for x in build_receipt_blocks(order, width, safe, header)]

def build_receipt_text(order, width=None, safe=True, header=True):
    return "\n".join(build_receipt_lines(order, width, safe, header))

def order_discount_line(order):
    """Aksiya bo'lgan buyurtmada eski summa va chegirma qatorini qaytaradi."""
    pct = order.get("discount_percent") or 0
    old = order.get("original_total")
    if not pct or not old or old <= order.get("total", 0):
        return ""
    saved = old - order["total"]
    return f"🏷 Aksiya −{pct}%: {fmt_sum(old)} → {fmt_sum(order['total'])} (−{fmt_sum(saved)})\n"

def order_money_lines(order):
    """Admin ko'radigan pul qatorlari — keshbek va avans ajratib ko'rsatiladi."""
    used = order_cashback_used(order)
    adv = order_advance_used(order)
    if used <= 0 and adv <= 0:
        return f"\U0001F4B0 Jami: {fmt_sum(order.get('total', 0))} (naqd)\n"
    satr = f"\U0001F4B0 Jami: {fmt_sum(order.get('total', 0))}\n"
    if used > 0:
        satr += f"\U0001F4B3 Keshbek bilan: \u2212{fmt_sum(used)}\n"
    if adv > 0:
        satr += f"\U0001F4D2 Avansdan: \u2212{fmt_sum(adv)}\n"
    satr += f"\U0001F4B5 Naqd olinadi: {fmt_sum(order_cash_due(order))}\n"
    return satr

def order_account_line(order):
    """Admin kartasida: hisobga yozilganmi va mijozning balansi qancha."""
    uid = order.get("user_id")
    if not uid:
        return ""
    bal = account_balance(uid)
    if order_on_account(order):
        amt = money(order.get("account_amount") or order_cash_due(order))
        return (f"\U0001F4D2 Hisobga yozilgan: {fmt_sum(amt)} (naqd olinmaydi)\n"
                f"   Mijoz hisobi: {fmt_signed(bal)}\n")
    if bal != 0:
        holat = "qarzi bor" if bal < 0 else "avansi bor"
        return f"\U0001F4D2 Mijoz hisobi: {fmt_signed(bal)} ({holat})\n"
    return ""

def order_address_line(order):
    if order.get("latitude") is not None:
        return "📍 Joylashuv quyida xarita orqali yuborildi"
    return f"📍 {order.get('address_text') or '—'}"

def order_contact_line(order):
    if order.get("source") == "instagram":
        ig = order.get("ig_username")
        return f"📷 Instagram: @{ig}" if ig else "📷 Instagram"
    if order.get("username"):
        return f"@{order['username']}"
    return "username yo'q"

CANCELLED = "Bekor qilindi"

def is_cancelled(order):
    return order.get("status") == CANCELLED

def active_items(order):
    """Bekor qilinmagan taomlar."""
    return [it for it in order.get("items", []) if not it.get("cancelled")]

def recalc_order_total(order):
    """Bekor qilinmagan taomlar bo'yicha summani qayta hisoblaydi."""
    total = 0
    original = 0
    for it in active_items(order):
        total += it["price"] * it["qty"]
        original += (it.get("old_price") or it["price"]) * it["qty"]
    order["total"] = total
    order["original_total"] = original
    return total

def restore_stock(items):
    """Bekor qilingan taomlarning zaxirasini menyuga qaytaradi."""
    if not items:
        return
    menu = load_menu()
    by_name = {}
    for d in menu:
        by_name.setdefault(d["name"], d)
    changed = False
    for it in items:
        dish = by_name.get(it["name"])
        if dish is not None and dish.get("stock") is not None:
            dish["stock"] = dish["stock"] + it["qty"]
            changed = True
    if changed:
        save_menu(menu)

def status_keyboard(order, include_contact=True):
    kb = types.InlineKeyboardMarkup(row_width=2)
    if is_cancelled(order):
        kb.add(types.InlineKeyboardButton("♻️ Bekorni qaytarish", callback_data=f"uncancel:{order['id']}"))
        return kb
    kb.add(
        types.InlineKeyboardButton("👨‍🍳 Tayyorlanmoqda", callback_data=f"status:{order['id']}:Tayyorlanmoqda"),
        types.InlineKeyboardButton("🚴 Yo'lda", callback_data=f"status:{order['id']}:Yo'lda"),
    )
    kb.add(types.InlineKeyboardButton("✅ Yetkazildi", callback_data=f"status:{order['id']}:Yetkazildi"))

    items = order.get("items", [])
    live = active_items(order)
    # Bitta taomni olib tashlash — faqat bir nechta taom bo'lsa ma'noga ega
    if len(live) > 1:
        for idx, it in enumerate(items):
            if it.get("cancelled"):
                continue
            nom = it["name"] if len(it["name"]) <= 18 else it["name"][:17] + "…"
            kb.add(types.InlineKeyboardButton(f"➖ {nom} ({fmt_qty(it)}) olib tashlash",
                                              callback_data=f"rmitem:{order['id']}:{idx}"))
    if order.get("user_id"):
        if order_on_account(order):
            kb.add(types.InlineKeyboardButton("↩️ Hisobdan qaytarish",
                                              callback_data=f"acct:{order['id']}:0"))
        else:
            kb.add(types.InlineKeyboardButton("📒 Hisobga yozish (nasiya/avans)",
                                              callback_data=f"acct:{order['id']}:1"))
    kb.add(types.InlineKeyboardButton("❌ Buyurtmani bekor qilish", callback_data=f"cancel:{order['id']}"))
    if include_contact and order.get("user_id"):
        kb.add(types.InlineKeyboardButton("✉️ Mijozga yozish", url=f"tg://user?id={order['user_id']}"))
    return kb

def notify_owner_new_order(order):
    try:
        text = (
            f"🆕 Yangi buyurtma #{order['daily_number']}\n\n"
            f"👤 {order['customer_name']} ({order_contact_line(order)})\n"
            f"{order_phone_line(order)}\n"
            f"{order_address_line(order)}\n"
            + (f"📝 {order['note']}\n" if order.get('note') else "")
            + f"\n{order_items_text(order)}\n\n"
            + order_discount_line(order)
            + order_money_lines(order)
            + order_account_line(order)
            + f"Holat: {order['status']}"
        )
        kb = status_keyboard(order)
    except Exception as e:
        print(f"Buyurtma matnini tuzishda xato: {e}")
        text = f"🆕 Yangi buyurtma #{order.get('daily_number', order.get('id', '?'))} — {fmt_sum(order.get('total', 0))}. Tafsilot chiqarishda xato bo'ldi, /report bilan tekshiring."
        kb = None

    for recipient_id in notify_recipients():
        if order.get("latitude") is not None:
            try:
                bot.send_location(recipient_id, order["latitude"], order["longitude"])
            except Exception as e:
                print(f"Joylashuv yuborishda xato ({recipient_id}): {e}")
        try:
            sent = bot.send_message(recipient_id, text, reply_markup=kb)
            register_order_reply_target(recipient_id, sent, order)
        except Exception as e:
            print(f"Buyurtma matnini yuborishda xato ({recipient_id}): {e}")
            if "BUTTON_USER_PRIVACY_RESTRICTED" in str(e):
                try:
                    fallback_kb = status_keyboard(order, include_contact=False) if kb is not None else None
                    sent = bot.send_message(recipient_id, text, reply_markup=fallback_kb)
                    register_order_reply_target(recipient_id, sent, order)
                except Exception as e2:
                    print(f"Qayta urinishda ham xato ({recipient_id}): {e2}")

def register_order_reply_target(recipient_id, sent_message, order):
    """Buyurtma xabariga Reply qilinganda javob mijozga borishi uchun eslab qo'yamiz."""
    try:
        if order.get("user_id") and sent_message is not None:
            support_message_map[(recipient_id, sent_message.message_id)] = order["user_id"]
        elif order.get("ig_user_id") and sent_message is not None:
            support_message_map[(recipient_id, sent_message.message_id)] = f"ig:{order['ig_user_id']}"
    except Exception as e:
        print(f"Reply manzilini eslab qolishda xato: {e}")

def order_card_text(order):
    """Admin ko'radigan buyurtma kartochkasi matni."""
    head = "❌ BEKOR QILINDI" if is_cancelled(order) else f"📦 Buyurtma #{order['daily_number']}"
    if is_cancelled(order):
        head = f"❌ Buyurtma #{order['daily_number']} — BEKOR QILINDI"
    return (
        f"{head}\n\n"
        f"👤 {order['customer_name']} ({order_contact_line(order)})\n"
        f"{order_phone_line(order)}\n"
        f"{order_address_line(order)}\n"
        + (f"📝 {order['note']}\n" if order.get('note') else "")
        + f"\n{order_items_text(order)}\n\n"
        + order_discount_line(order)
        + order_money_lines(order)
        + f"Holat: {order['status']}"
    )

def refresh_order_card(call, order):
    """Admin bosgan xabarni yangilaydi."""
    text = order_card_text(order)
    try:
        bot.edit_message_text(text, call.message.chat.id, call.message.message_id,
                              reply_markup=status_keyboard(order))
    except Exception as e:
        if "BUTTON_USER_PRIVACY_RESTRICTED" in str(e):
            try:
                bot.edit_message_text(text, call.message.chat.id, call.message.message_id,
                                      reply_markup=status_keyboard(order, include_contact=False))
            except Exception:
                pass

def tell_customer(order, text_uz_key, **kw):
    """Mijozga o'z tilida xabar yuboradi."""
    uid = order.get("user_id")
    if not uid:
        if order.get("ig_user_id"):
            ig_notify_customer(order, t(text_uz_key, "uz", **kw))
        return
    try:
        lang = get_user_lang(uid)
        bot.send_message(uid, t(text_uz_key, lang, **kw))
    except Exception as e:
        print(f"Mijozga xabar yuborishda xato: {e}")

@bot.callback_query_handler(func=lambda c: c.data.startswith("cancel:"))
def cb_cancel_order(call):
    """Butun buyurtmani bekor qilish."""
    if not is_staff_or_admin(call.message.chat.id):
        bot.answer_callback_query(call.id, "Ruxsat yo'q.")
        return
    order_id = int(call.data.split(":", 1)[1])
    err = None
    taken_back = refunded = new_balance = 0.0
    adv_back = adv_bal = 0.0
    with DATA_LOCK:
        orders = load_orders()
        order = next((o for o in orders if o["id"] == order_id), None)
        if not order:
            err = "Buyurtma topilmadi."
        elif is_cancelled(order):
            err = "Bu buyurtma allaqachon bekor qilingan."
    if err:
        bot.answer_callback_query(call.id, err)
        return

    with DATA_LOCK:
        restore_stock(active_items(order))
        order["status"] = CANCELLED
        order["cancelled_at"] = int(time.time())
        order["cancelled_by"] = call.from_user.id
        # yozilgan keshbek bekor bo'ladi, ishlatilgani esa mijozga qaytadi
        taken_back, _ = revoke_order_cashback(order, "buyurtma bekor qilindi")
        refunded, new_balance = refund_used_cashback(order)
        # ishlatilgan avans ham hisobga qaytadi — bu haqiqiy pul
        adv_back, adv_bal = refund_used_advance(order)
        save_orders(orders)

    msg = "❌ Buyurtma bekor qilindi."
    if taken_back > 0:
        msg += f" Keshbek −{fmt_sum(taken_back)}."
    if refunded > 0:
        msg += f" Mijozga {fmt_sum(refunded)} keshbek qaytarildi."
    if adv_back > 0:
        msg += f" Avans {fmt_sum(adv_back)} qaytarildi (balans {fmt_signed(adv_bal)})."
    bot.answer_callback_query(call.id, msg)
    refresh_order_card(call, order)
    tell_customer(order, "order_cancelled", no=order["daily_number"])
    if refunded > 0:
        tell_customer(order, "cb_refunded", amt=fmt_sum(refunded), bal=fmt_sum(new_balance))
    if adv_back > 0:
        tell_customer(order, "adv_refunded", amt=fmt_sum(adv_back), bal=fmt_signed(adv_bal))

@bot.callback_query_handler(func=lambda c: c.data.startswith("uncancel:"))
def cb_uncancel_order(call):
    """Xato bosilgan bo'lsa — bekorni qaytarish."""
    if not is_staff_or_admin(call.message.chat.id):
        bot.answer_callback_query(call.id, "Ruxsat yo'q.")
        return
    order_id = int(call.data.split(":", 1)[1])
    with DATA_LOCK:
        orders = load_orders()
        order = next((o for o in orders if o["id"] == order_id), None)
        bad = not order or not is_cancelled(order)
    if bad:
        bot.answer_callback_query(call.id, "Bu buyurtma bekor qilinmagan.")
        return
    with DATA_LOCK:
        order["status"] = "Yangi"
        order.pop("cancelled_at", None)
        order.pop("cancelled_by", None)
        cb_ok = recharge_used_cashback(order)
        adv_again, adv_bal = recharge_used_advance(order)
        save_orders(orders)
    msg = "♻️ Buyurtma qaytarildi."
    if adv_again > 0:
        msg += f" Avans yana yechildi: {fmt_sum(adv_again)} (balans {fmt_signed(adv_bal)})."
    if not cb_ok:
        msg = ("♻️ Qaytarildi, lekin mijozning keshbegi yetmadi — "
               "buyurtma to'liq naqd to'lanadigan bo'ldi.")
    bot.answer_callback_query(call.id, msg, show_alert=not cb_ok)
    refresh_order_card(call, order)
    tell_customer(order, "order_restored", no=order["daily_number"])

@bot.callback_query_handler(func=lambda c: c.data.startswith("rmitem:"))
def cb_remove_item(call):
    """Buyurtmadan bitta taomni olib tashlash."""
    if not is_staff_or_admin(call.message.chat.id):
        bot.answer_callback_query(call.id, "Ruxsat yo'q.")
        return
    _, order_id_str, idx_str = call.data.split(":", 2)
    order_id, idx = int(order_id_str), int(idx_str)
    err = None
    alert = False
    with DATA_LOCK:
        orders = load_orders()
        order = next((o for o in orders if o["id"] == order_id), None)
        items = order.get("items", []) if order else []
        if not order:
            err = "Buyurtma topilmadi."
        elif idx < 0 or idx >= len(items) or items[idx].get("cancelled"):
            err = "Bu taom allaqachon olib tashlangan."
        elif len(active_items(order)) <= 1:
            err, alert = "Oxirgi taom — butun buyurtmani bekor qiling.", True
    if err:
        bot.answer_callback_query(call.id, err, show_alert=alert)
        return

    it = items[idx]
    with DATA_LOCK:
        restore_stock([it])
        it["cancelled"] = True
        recalc_order_total(order)
        # keshbek yangi summadan oshib ketgan bo'lsa, ortig'i mijozga qaytadi
        given_back = trim_cashback_to_total(order)
        # avans ham yangi summadan oshib ketgan bo'lsa, ortig'i hisobga qaytadi
        adv_extra = trim_advance_to_total(order)
        save_orders(orders)

    msg = f"➖ {it['name']} olib tashlandi."
    if given_back > 0:
        msg += f" {fmt_sum(given_back)} keshbek mijozga qaytarildi."
    if adv_extra > 0:
        msg += f" {fmt_sum(adv_extra)} avans hisobga qaytarildi."
    bot.answer_callback_query(call.id, msg)
    refresh_order_card(call, order)
    tell_customer(order, "item_cancelled", no=order["daily_number"],
                  dish=it["name"], sum=fmt_sum(order["total"]))

@bot.callback_query_handler(func=lambda c: c.data.startswith("acct:"))
def cb_account_charge(call):
    """Buyurtmani mijoz hisobiga yozadi yoki qaytarib oladi."""
    if not is_staff_or_admin(call.message.chat.id):
        bot.answer_callback_query(call.id, "Ruxsat yo\'q.")
        return
    _, oid_str, flag = call.data.split(":", 2)
    order_id = int(oid_str)
    charge = flag == "1"

    err = None
    uid = None
    amount = 0.0
    with DATA_LOCK:
        orders = load_orders()
        order = next((o for o in orders if o["id"] == order_id), None)
        if not order:
            err = "Buyurtma topilmadi."
        elif not order.get("user_id"):
            err = "Bu buyurtmada mijoz aniqlanmagan."
        elif charge and order_on_account(order):
            err = "Allaqachon hisobga yozilgan."
        elif not charge and not order_on_account(order):
            err = "Bu buyurtma hisobda emas."
        elif charge and money(order_cash_due(order)) <= 0:
            err = ("Bu buyurtmadan naqd olinmaydi — "
                   "summa keshbek va avansdan to‘langan.")
        else:
            uid = order["user_id"]
            if charge:
                # avans va keshbek chegirilgandan keyin qolgan qismi yoziladi
                amount = money(order_cash_due(order))
                order["on_account"] = True
                order["account_amount"] = amount
            else:
                amount = money(order.get("account_amount") or order_cash_due(order))
                order["on_account"] = False
                order.pop("account_amount", None)
            save_orders(orders)

    if err:
        bot.answer_callback_query(call.id, err, show_alert=True)
        return

    delta = -amount if charge else amount
    bal = account_move(uid, delta, order_id,
                       "buyurtma hisobga yozildi" if charge else "hisobdan qaytarildi")

    bot.answer_callback_query(call.id,
        ("Hisobga yozildi: " if charge else "Qaytarildi: ") + fmt_sum(amount) +
        " \u2014 balans " + fmt_signed(bal))

    # Buyurtma kartasidagi tugmalarni yangilaymiz
    try:
        orders = load_orders()
        order = next((o for o in orders if o["id"] == order_id), None)
        if order:
            bot.edit_message_reply_markup(call.message.chat.id, call.message.message_id,
                                          reply_markup=status_keyboard(order))
    except Exception:
        pass

    # Mijozga xabar \u2014 o\'z haqqi va qarzini ko\'rib tursin
    if charge:
        try:
            lang = get_user_lang(uid)
            bot.send_message(uid, t("acct_charged", lang,
                                    amt=fmt_sum(amount), bal=fmt_signed(bal)))
        except Exception:
            pass

@bot.callback_query_handler(func=lambda c: c.data.startswith("status:"))
def cb_update_status(call):
    if not is_staff_or_admin(call.message.chat.id):
        bot.answer_callback_query(call.id, "Ruxsat yo'q.")
        return
    _, order_id_str, new_status = call.data.split(":", 2)
    order_id = int(order_id_str)

    earned = 0.0
    new_balance = 0.0
    taken_back = 0.0
    with DATA_LOCK:
        orders = load_orders()
        order = next((o for o in orders if o["id"] == order_id), None)
        if not order:
            bot.answer_callback_query(call.id, "Buyurtma topilmadi.")
            return
        if is_cancelled(order):
            bot.answer_callback_query(call.id, "Bu buyurtma bekor qilingan. Avval \"Bekorni qaytarish\"ni bosing.", show_alert=True)
            return
        prev_status = order.get("status")
        order["status"] = new_status
        # keshbek faqat YETKAZILGANDA yoziladi
        if new_status == "Yetkazildi":
            if not order.get("delivered_at"):
                order["delivered_at"] = int(time.time())
            earned, new_balance = credit_order_cashback(order)
        elif prev_status == "Yetkazildi":
            taken_back, new_balance = revoke_order_cashback(order, "holat orqaga o'zgartirildi")
        save_orders(orders)

    refresh_order_card(call, order)
    note = f"Holat yangilandi: {new_status}"
    if earned > 0:
        note += f" • keshbek +{fmt_sum(earned)}"
    elif taken_back > 0:
        note += f" • keshbek −{fmt_sum(taken_back)} qaytarib olindi"
    bot.answer_callback_query(call.id, note)

    try:
        clang = get_user_lang(order["user_id"])
        bot.send_message(order["user_id"], t("status_update", clang,
                                             no=order["daily_number"], st=status_name(new_status, clang)))
        if earned > 0:
            bot.send_message(order["user_id"], t("cb_earned", clang,
                                                 amt=fmt_sum(earned), bal=fmt_sum(new_balance)))
    except Exception:
        pass

    if order.get("ig_user_id"):
        ig_notify_customer(order, t("status_update", "uz", no=order["daily_number"],
                                    st=status_name(new_status, "uz")))

    if new_status == "Yetkazildi":
        mark_delivered_user(order.get("user_id"))
        winback_reset(order.get("user_id"))      # qayta buyurtma berdi — uxlash hisobi noldan
        try:
            maybe_send_subscription_offer(order)
        except Exception as e:
            print(f"Obuna taklifi xatosi: {e}")


# ======================================================================
#  OBUNA TAKLIFI — 3-buyurtmadan keyin bir marta
# ======================================================================

def maybe_send_subscription_offer(order):
    """Mijozning SUB_OFFER_AFTER-chi buyurtmasi yetkazilganda 1 oylik tarifni taklif qiladi."""
    uid = order.get("user_id")
    if not uid:
        return False
    wb = load_winback()
    if (wb.get(str(uid)) or {}).get("offer3"):
        return False                                  # bu mijozga allaqachon yuborilgan
    if len(delivered_orders_of(uid)) < SUB_OFFER_AFTER:
        return False

    lang = get_user_lang(uid)
    kb = types.InlineKeyboardMarkup()
    kb.add(types.InlineKeyboardButton(t("btn_sub_info", lang), url=SUB_OFFER_URL))
    try:
        bot.send_message(uid, t("sub_offer", lang, biz=BUSINESS_NAME), reply_markup=kb)
    except Exception as e:
        msg = str(e).lower()
        if "blocked" in msg or "deactivated" in msg or "chat not found" in msg:
            mark_user_blocked(uid)
        print(f"Obuna taklifi yuborilmadi ({uid}): {e}")
        return False
    winback_mark(uid, "offer3")
    return True


# ======================================================================
#  AVVALGI BUYURTMANI TAKRORLASH
# ======================================================================

repeat_state = {}          # user_id -> tayyorlangan takroriy buyurtma
REPEAT_TTL = 30 * 60       # yarim soatdan keyin eskiradi

def is_repeat_button(text):
    return any(text == TEXTS["btn_repeat"][l] for l in SUPPORTED_LANGS)

def build_repeat_plan(user_id):
    """Oxirgi yetkazilgan buyurtmadan bugungi menyu bo'yicha yangi savat tuzadi."""
    orders = load_orders()
    mine = delivered_orders_of(user_id, orders)
    if not mine:
        return None, None
    last = mine[-1]
    by_name = {}
    for d in load_menu():
        by_name.setdefault(d["name"], d)
    disc = get_discount()

    cart, lines, missing = {}, [], []
    total = 0
    for it in last.get("items", []):
        if it.get("cancelled"):
            continue
        dish = by_name.get(it["name"])
        stock = dish.get("stock") if dish else None
        if not dish or (stock is not None and stock <= 0):
            missing.append(it["name"])               # menyudan olib tashlangan yoki tugagan
            continue
        qty = int(it.get("qty") or 1)
        if stock is not None and qty > stock:
            qty = stock
        unit = discounted_price(dish["price"], disc)
        cart[dish["id"]] = cart.get(dish["id"], 0) + qty
        total += unit * qty
        lines.append(f"{dish['name']} \u00d7 {qty} = {fmt_sum(unit * qty)}")

    plan = {"cart": cart, "lines": lines, "missing": missing, "total": money(total)}
    return last, plan

def repeat_address_line(st):
    if st.get("lat") is not None:
        return "\U0001F4CD Joylashuv xaritada yuborilgan"
    addr = st.get("addr") or "\u2014"
    return f"\U0001F4CD {addr}"

def repeat_text(uid, st):
    lang = get_user_lang(uid)
    parts = [t("rep_title", lang), ""]
    parts += st["lines"]
    parts.append("")
    if st.get("missing"):
        parts.append(t("rep_removed", lang, list=", ".join(st["missing"])))
        parts.append("")
    parts.append(t("receipt_total", lang, sum=fmt_sum(st["total"])))
    used = st.get("cb_amount", 0) if st.get("use_cb") else 0
    if used > 0:
        parts.append(t("cb_receipt_line", lang, amt=fmt_sum(used),
                       pay=fmt_sum(max(0, money(st["total"] - used)))).rstrip())
    parts.append(repeat_address_line(st))
    return "\n".join(parts)

def repeat_keyboard(uid, st):
    lang = get_user_lang(uid)
    kb = types.InlineKeyboardMarkup()
    kb.row(types.InlineKeyboardButton(t("btn_rep_ok", lang), callback_data="rep:ok"),
           types.InlineKeyboardButton(t("btn_rep_no", lang), callback_data="rep:no"))
    kb.add(types.InlineKeyboardButton(t("btn_rep_addr", lang), callback_data="rep:addr"))
    bal = cashback_balance(uid)
    if get_cashback_cfg()["active"] and bal > 0:
        key = "btn_rep_cb_off" if st.get("use_cb") else "btn_rep_cb_on"
        kb.add(types.InlineKeyboardButton(t(key, lang), callback_data="rep:cb"))
    return kb

def refresh_repeat_cb(uid, st):
    """Keshbek yoqilgan bo'lsa qancha ishlatilishini qayta hisoblaymiz."""
    if st.get("use_cb") and get_cashback_cfg()["active"]:
        st["cb_amount"] = money(min(cashback_balance(uid), st["total"]))
    else:
        st["cb_amount"] = 0

@bot.message_handler(func=lambda m: (m.content_type == "text" and m.text
                                     and is_repeat_button(m.text)
                                     and m.from_user.id not in checkout_state))
def handle_repeat_button(message):
    uid = message.from_user.id
    add_known_user(message.from_user)
    lang = get_user_lang(uid, getattr(message.from_user, "language_code", None))

    shop = shop_status()
    if not shop["open"] and not is_owner(uid):
        bot.send_message(message.chat.id, closed_message(lang, shop))
        return

    last, plan = build_repeat_plan(uid)
    if not last:
        bot.send_message(message.chat.id, t("rep_none", lang),
                         reply_markup=main_keyboard(uid, message.from_user.username, lang))
        return

    if not plan["cart"] or plan["total"] < REPEAT_MIN_TOTAL:
        text = ""
        if plan["missing"]:
            # qaysi taom tushib qolganini baribir aytamiz
            text += t("rep_removed", lang, list=", ".join(plan["missing"])) + "\n\n"
        text += t("rep_too_small", lang, sum=fmt_sum(plan["total"]),
                  min=fmt_sum(REPEAT_MIN_TOTAL))
        bot.send_message(message.chat.id, text,
                         reply_markup=main_keyboard(uid, message.from_user.username, lang))
        return

    st = {
        "cart": plan["cart"], "lines": plan["lines"], "missing": plan["missing"],
        "total": plan["total"],
        "name": last.get("customer_name") or message.from_user.first_name or "Mijoz",
        "phone": last.get("phone") or "",
        "addr": last.get("address_text"),
        "lat": last.get("latitude"), "lon": last.get("longitude"),
        "note": last.get("note") or "",
        "use_cb": False, "cb_amount": 0,
        "ts": time.time(), "await_addr": False,
    }
    repeat_state[uid] = st
    bot.send_message(message.chat.id, repeat_text(uid, st), reply_markup=repeat_keyboard(uid, st))

def repeat_alive(uid):
    st = repeat_state.get(uid)
    if not st:
        return None
    if time.time() - st.get("ts", 0) > REPEAT_TTL:
        repeat_state.pop(uid, None)
        return None
    return st

@bot.callback_query_handler(func=lambda c: c.data and c.data.startswith("rep:"))
def cb_repeat(call):
    uid = call.from_user.id
    lang = get_user_lang(uid)
    st = repeat_alive(uid)
    if not st:
        bot.answer_callback_query(call.id, t("rep_expired", lang), show_alert=True)
        return
    action = call.data.split(":", 1)[1]

    if action == "no":
        repeat_state.pop(uid, None)
        bot.answer_callback_query(call.id, t("rep_cancelled", lang))
        try:
            bot.edit_message_reply_markup(call.message.chat.id, call.message.message_id,
                                          reply_markup=None)
        except Exception:
            pass
        return

    if action == "cb":
        st["use_cb"] = not st.get("use_cb")
        refresh_repeat_cb(uid, st)
        st["ts"] = time.time()
        bot.answer_callback_query(call.id)
        try:
            bot.edit_message_text(repeat_text(uid, st), call.message.chat.id,
                                  call.message.message_id, reply_markup=repeat_keyboard(uid, st))
        except Exception:
            pass
        return

    if action == "addr":
        st["await_addr"] = True
        st["ts"] = time.time()
        bot.answer_callback_query(call.id)
        bot.send_message(call.message.chat.id, t("rep_ask_addr", lang),
                         reply_markup=location_keyboard(lang))
        return

    if action == "ok":
        shop = shop_status()
        if not shop["open"] and not is_owner(uid):
            bot.answer_callback_query(call.id, t("closed_short", lang), show_alert=True)
            bot.send_message(call.message.chat.id, closed_message(lang, shop))
            return
        repeat_state.pop(uid, None)
        bot.answer_callback_query(call.id, "\u2705")
        try:
            bot.edit_message_reply_markup(call.message.chat.id, call.message.message_id,
                                          reply_markup=None)
        except Exception:
            pass
        order, error = create_order(
            items_cart=st["cart"],
            customer_name=st["name"],
            phone=st["phone"],
            latitude=st["lat"],
            longitude=st["lon"],
            address_text=st["addr"],
            note=st["note"],
            tg_user_id=uid,
            username=call.from_user.username,
            use_cashback=bool(st.get("use_cb")),
        )
        if error:
            bot.send_message(call.message.chat.id, error,
                             reply_markup=main_keyboard(uid, call.from_user.username, lang))

@bot.message_handler(func=lambda m: (m.from_user.id in repeat_state
                                     and repeat_state[m.from_user.id].get("await_addr")),
                     content_types=["text", "location"])
def handle_repeat_address(message):
    uid = message.from_user.id
    lang = get_user_lang(uid)
    st = repeat_alive(uid)
    if not st:
        bot.send_message(message.chat.id, t("rep_expired", lang),
                         reply_markup=main_keyboard(uid, message.from_user.username, lang))
        return

    if message.content_type == "location":
        st["lat"] = message.location.latitude
        st["lon"] = message.location.longitude
        st["addr"] = None
    else:
        text = (message.text or "").strip()
        if is_repeat_button(text) or is_any_bot_button(text):
            return
        if not text:
            bot.send_message(message.chat.id, t("rep_ask_addr", lang))
            return
        st["addr"] = text
        st["lat"] = None
        st["lon"] = None

    st["await_addr"] = False
    st["ts"] = time.time()
    bot.send_message(message.chat.id, t("rep_addr_ok", lang),
                     reply_markup=main_keyboard(uid, message.from_user.username, lang))
    bot.send_message(message.chat.id, repeat_text(uid, st), reply_markup=repeat_keyboard(uid, st))


# ======================================================================
#  UXLAB QOLGAN MIJOZLAR
# ======================================================================

def order_webapp_button(uid, users, lang):
    """Inline "Buyurtma berish" tugmasi — Mini App to'g'ridan-to'g'ri ochiladi."""
    if not WEBAPP_URL:
        return None
    uname = (users.get(str(uid)) or {}).get("username")
    ts, sig = sign_user_params(uid, uname)
    params = f"uid={uid}&uname={urllib.parse.quote(uname or '')}&ts={ts}&sig={sig}&v={ts}"
    return types.InlineKeyboardButton(t("btn_order_now", lang),
                                      web_app=types.WebAppInfo(url=f"{WEBAPP_URL}?{params}"))

def winback_scan():
    """(1-bosqich, 2-bosqich) — hali xabar yuborilmagan uxlab qolgan mijozlar."""
    now = int(time.time())
    last = last_delivery_by_user()
    wb = load_winback()
    users = load_users()
    g1, g2 = [], []
    for uid, ts in last.items():
        if (users.get(str(uid)) or {}).get("blocked"):
            continue
        days = (now - ts) / 86400.0
        rec = wb.get(str(uid)) or {}
        if days >= WINBACK_DAYS_2:
            if not rec.get("s21"):
                g2.append((uid, days))
        elif days >= WINBACK_DAYS_1:
            if not rec.get("s7"):
                g1.append((uid, days))
    return g1, g2

def _winback_failed(uid, err):
    msg = str(err).lower()
    if "blocked" in msg or "deactivated" in msg or "chat not found" in msg:
        mark_user_blocked(uid)
        return True
    print(f"Uxlaganlarga xabar yuborishda xato ({uid}): {err}")
    return False

def wb_who(uid, users=None):
    """Hisobotda mijozni tanib olish uchun: ism, @username va raqami."""
    users = users if users is not None else load_users()
    u = users.get(str(uid)) or {}
    name = (u.get("name") or "").strip() or "ismsiz"
    uname = (u.get("username") or "").strip()
    return f"{name}" + (f" (@{uname})" if uname else "") + f" — {uid}"

def customer_name_of(uid, users=None):
    users = users if users is not None else load_users()
    return ((users.get(str(uid)) or {}).get("name") or "").strip() or "mijoz"

def run_winback(report_to=None):
    """Uxlab qolganlarga xabar yuboradi. Fon oqimida ishlaydi."""
    g1, g2 = winback_scan()
    users = load_users()
    sent1 = sent2 = 0
    ok_list, fail_list = [], []        # hisobotda kimga ketgani ko'rinsin

    for uid, _days in g1:
        lang = get_user_lang(uid)
        kb = types.InlineKeyboardMarkup()
        kb.add(types.InlineKeyboardButton(t("btn_feedback", lang), callback_data="wb:fb"))
        ob = order_webapp_button(uid, users, lang)
        if ob:
            kb.add(ob)
        try:
            bot.send_message(uid, t("wb_7", lang, ism=customer_name_of(uid, users)),
                             reply_markup=kb)
            winback_mark(uid, "s7")
            sent1 += 1
            ok_list.append(f"{WINBACK_DAYS_1}k • " + wb_who(uid, users))
        except Exception as e:
            fail_list.append(wb_who(uid, users) + f" — {e}")
            _winback_failed(uid, e)
        time.sleep(0.06)

    for uid, _days in g2:
        lang = get_user_lang(uid)
        kb = types.InlineKeyboardMarkup()
        ob = order_webapp_button(uid, users, lang)
        if ob:
            kb.add(ob)
        kb.add(types.InlineKeyboardButton(t("btn_feedback", lang), callback_data="wb:fb"))
        # bonusni avval qo'shamiz — xabarda u haqida yozilgan
        cashback_move(uid, WINBACK_BONUS, None, "uxlab qolgan mijozga bonus")
        try:
            bot.send_message(uid, t("wb_21", lang, ism=customer_name_of(uid, users),
                                    bonus=fmt_sum(WINBACK_BONUS), biz=BUSINESS_NAME),
                             reply_markup=kb)
            winback_mark(uid, "s21")
            sent2 += 1
            ok_list.append(f"{WINBACK_DAYS_2}k • " + wb_who(uid, users))
        except Exception as e:
            fail_list.append(wb_who(uid, users) + f" — {e}")
            # xabar yetib bormadi — bonusni qaytarib olamiz, keyingi safar qayta uriniladi
            cashback_move(uid, -WINBACK_BONUS, None, "xabar yetmadi, bonus qaytarildi")
            _winback_failed(uid, e)
        time.sleep(0.06)

    if sent1 or sent2 or report_to:
        text = (f"\U0001F634 Uxlab qolgan mijozlar: "
                f"{WINBACK_DAYS_1} kunlik \u2014 {sent1} ta, "
                f"{WINBACK_DAYS_2} kunlik \u2014 {sent2} ta xabar yuborildi.")
        if sent2:
            text += f"\n\U0001F381 Berilgan bonus: {fmt_sum(sent2 * WINBACK_BONUS)}"
        if ok_list:
            text += "\n\nXabar ketganlar:\n" + "\n".join("  " + x for x in ok_list[:25])
            if len(ok_list) > 25:
                text += f"\n  ...va yana {len(ok_list) - 25} ta"
        if fail_list:
            text += "\n\n⚠️ Yetib bormaganlar:\n" + "\n".join("  " + x for x in fail_list[:15])
        targets = [report_to] if report_to else list(load_admin_ids())
        for admin_id in targets:
            try:
                bot.send_message(admin_id, text)
            except Exception:
                pass
    return sent1, sent2

@bot.callback_query_handler(func=lambda c: c.data == "wb:fb")
def cb_winback_feedback(call):
    """"Fikr bildirish" — mavjud Murojaat tizimiga ulanadi, keyingi xabar adminlarga boradi."""
    lang = get_user_lang(call.from_user.id)
    bot.answer_callback_query(call.id)
    try:
        bot.send_message(call.message.chat.id, t("contact_prompt", lang))
    except Exception:
        pass

def winback_scheduler():
    """Har kuni WINBACK_HOUR da (Riyadh vaqti) uxlab qolganlarni tekshiradi."""
    last_run = None
    while True:
        try:
            now = datetime.now(TIMEZONE)
            if now.hour == WINBACK_HOUR and now.minute == 0 and last_run != now.date():
                last_run = now.date()
                threading.Thread(target=run_winback, daemon=True).start()
        except Exception as e:
            print(f"Uxlaganlar jadvali xatosi: {e}")
        time.sleep(30)

@bot.message_handler(commands=["uxlaganlar"])
def cmd_sleepers(message):
    if not is_owner(message.chat.id):
        return
    parts = (message.text or "").split()
    arg = parts[1].lower() if len(parts) > 1 else ""

    if arg in ("yubor", "send"):
        bot.send_message(message.chat.id, "Yuborilmoqda... Tugagach hisobot keladi.")
        threading.Thread(target=run_winback, args=(message.chat.id,), daemon=True).start()
        return

    if arg in ("sinov", "test"):
        # Mijoz aynan nimani ko'rishini o'zingizga yuboramiz. Bonus berilmaydi,
        # hech kim "yuborilgan" deb belgilanmaydi.
        uid = message.chat.id
        lang = get_user_lang(uid)
        users_t = load_users()
        kb1 = types.InlineKeyboardMarkup()
        kb1.add(types.InlineKeyboardButton(t("btn_feedback", lang), callback_data="wb:fb"))
        ob1 = order_webapp_button(uid, users_t, lang)
        if ob1:
            kb1.add(ob1)
        kb2 = types.InlineKeyboardMarkup()
        ob2 = order_webapp_button(uid, users_t, lang)
        if ob2:
            kb2.add(ob2)
        kb2.add(types.InlineKeyboardButton(t("btn_feedback", lang), callback_data="wb:fb"))
        bot.send_message(uid, f"\U0001F9EA Sinov — {WINBACK_DAYS_1} kunlik xabar:")
        bot.send_message(uid, t("wb_7", lang, ism=customer_name_of(uid, users_t)), reply_markup=kb1)
        bot.send_message(uid, f"\U0001F9EA Sinov — {WINBACK_DAYS_2} kunlik xabar:")
        bot.send_message(uid, t("wb_21", lang, ism=customer_name_of(uid, users_t),
                                bonus=fmt_sum(WINBACK_BONUS), biz=BUSINESS_NAME), reply_markup=kb2)
        return

    if arg in ("royxat", "ro'yxat", "list", "kim"):
        g1, g2 = winback_scan()
        users_l = load_users()
        if not g1 and not g2:
            bot.send_message(message.chat.id, "Hozir xabar kutayotgan mijoz yo'q.")
            return
        txt = "\U0001F634 Xabar kutayotganlar\n"
        if g1:
            txt += f"\n{WINBACK_DAYS_1} kunlik ({len(g1)} ta):\n" + "\n".join(
                f"  {wb_who(u, users_l)} — {d:.0f} kun" for u, d in g1[:30])
        if g2:
            txt += f"\n\n{WINBACK_DAYS_2} kunlik ({len(g2)} ta):\n" + "\n".join(
                f"  {wb_who(u, users_l)} — {d:.0f} kun" for u, d in g2[:30])
        bot.send_message(message.chat.id, txt)
        return

    now = int(time.time())
    last = last_delivery_by_user()
    wb = load_winback()
    users = load_users()
    n1 = n2 = 0
    for uid, ts in last.items():
        days = (now - ts) / 86400.0
        if days >= WINBACK_DAYS_2:
            n2 += 1
        elif days >= WINBACK_DAYS_1:
            n1 += 1
    g1, g2 = winback_scan()
    done1 = sum(1 for r in wb.values() if r.get("s7"))
    done2 = sum(1 for r in wb.values() if r.get("s21"))
    bloklagan = sum(1 for uid in last if (users.get(str(uid)) or {}).get("blocked"))

    bot.send_message(message.chat.id,
        "\U0001F634 Uxlab qolgan mijozlar\n\n"
        f"Buyurtma bergan mijozlar: {len(last)} ta\n\n"
        f"{WINBACK_DAYS_1}\u2013{WINBACK_DAYS_2} kundan beri jim: {n1} ta\n"
        f"   \u2514 xabar kutayotgani: {len(g1)} ta\n"
        f"{WINBACK_DAYS_2}+ kundan beri jim: {n2} ta\n"
        f"   \u2514 xabar kutayotgani: {len(g2)} ta\n\n"
        f"Avval yuborilgan: {WINBACK_DAYS_1} kunlik \u2014 {done1} ta, "
        f"{WINBACK_DAYS_2} kunlik \u2014 {done2} ta\n"
        + (f"Botni bloklagan: {bloklagan} ta\n" if bloklagan else "")
        + f"\nHar kuni soat {WINBACK_HOUR}:00 da o'zi tekshiradi.\n"
        "Hoziroq yuborish: /uxlaganlar yubor\n"
        "Kimlar kutayotganini ko'rish: /uxlaganlar royxat\n"
        "Xabar qanday ko'rinishini sinash: /uxlaganlar sinov")

# ---------- admin: menyuni boshqarish ----------

@bot.message_handler(commands=["add_admin"])
def cmd_add_admin(message):
    if not is_owner(message.chat.id):
        return
    try:
        new_id = int(message.text.split(" ", 1)[1].strip())
    except Exception:
        bot.send_message(message.chat.id, "Format: /add_admin id\nMasalan: /add_admin 123456789\n"
                                           "(ID ni bilish uchun @userinfobot dan foydalaning)")
        return
    add_admin_id(new_id)
    bot.send_message(message.chat.id, f"✅ {new_id} endi admin. U ham botni boshqara oladi (menyu, zaxira, buyurtmalar).")
    try:
        bot.send_message(new_id, "🎉 Siz Miqot Food botiga admin etib tayinlandingiz. /menu yozib boshlang.")
    except Exception:
        bot.send_message(
            message.chat.id,
            f"⚠️ Diqqat: {new_id} ga xabar yuborib bo'lmadi — u hali botga /start bosmagan bo'lishi mumkin.\n"
            "Unga botni ochib bir marta /start bosishni ayting, shundan keyin xabarlar keladi."
        )

@bot.message_handler(commands=["remove_admin"])
def cmd_remove_admin(message):
    if not is_owner(message.chat.id):
        return
    try:
        rem_id = int(message.text.split(" ", 1)[1].strip())
    except Exception:
        bot.send_message(message.chat.id, "Format: /remove_admin id")
        return
    if rem_id == OWNER_CHAT_ID:
        bot.send_message(message.chat.id, "Bosh adminni o'chirib bo'lmaydi.")
        return
    remove_admin_id(rem_id)
    bot.send_message(message.chat.id, f"{rem_id} adminlikdan olib tashlandi.")

@bot.message_handler(commands=["admins"])
def cmd_list_admins(message):
    if not is_owner(message.chat.id):
        return
    admins = load_admin_ids()
    staff = load_staff_ids()
    text = "To'liq adminlar (hammasini boshqara oladi):\n" + "\n".join(str(i) for i in admins)
    if staff:
        text += "\n\nXodimlar (faqat buyurtma xabari + holat o'zgartirish):\n" + "\n".join(str(i) for i in staff)
    else:
        text += "\n\nXodimlar: yo'q"
    bot.send_message(message.chat.id, text)

@bot.message_handler(commands=["add_staff"])
def cmd_add_staff(message):
    if not is_owner(message.chat.id):
        return
    try:
        new_id = int(message.text.split(" ", 1)[1].strip())
    except Exception:
        bot.send_message(message.chat.id, "Format: /add_staff id\nMasalan: /add_staff 123456789\n"
                                           "(ID ni bilish uchun @userinfobot dan foydalaning)")
        return
    add_staff_id(new_id)
    bot.send_message(
        message.chat.id,
        f"✅ {new_id} endi xodim. U buyurtma xabarlarini oladi va holatini "
        "(Tayyorlanmoqda/Yo'lda/Yetkazildi) o'zgartira oladi — lekin menyu, "
        "narx, zaxira yoki adminlarni o'zgartira olmaydi."
    )
    try:
        bot.send_message(new_id, "🎉 Siz Miqot Food botida xodim etib tayinlandingiz. Endi yangi buyurtmalar sizga ham keladi.")
    except Exception:
        bot.send_message(
            message.chat.id,
            f"⚠️ Diqqat: {new_id} ga xabar yuborib bo'lmadi — u hali botga /start bosmagan bo'lishi mumkin.\n"
            "Unga botni ochib bir marta /start bosishni ayting, shundan keyin buyurtma xabarlari keladi."
        )

@bot.message_handler(commands=["remove_staff"])
def cmd_remove_staff(message):
    if not is_owner(message.chat.id):
        return
    try:
        rem_id = int(message.text.split(" ", 1)[1].strip())
    except Exception:
        bot.send_message(message.chat.id, "Format: /remove_staff id")
        return
    remove_staff_id(rem_id)
    bot.send_message(message.chat.id, f"{rem_id} xodimlikdan olib tashlandi.")

@bot.message_handler(commands=["menu"])
def cmd_menu_admin(message):
    if not is_owner(message.chat.id):
        return
    menu = load_menu()
    if not menu:
        bot.send_message(message.chat.id, "Menyu bo'sh. Rasm + tavsif yuborib yoki /add_dish bilan qo'shing.")
        return
    lines = []
    for d in menu:
        line = f"#{d['id']} — {d['name']} — {fmt_sum(d['price'])} | {d.get('category', DEFAULT_CATEGORY)}"
        if d.get("desc"):
            line += f" ({d['desc']})"
        if d.get("photo_id"):
            line += " 🖼"
        stock = d.get("stock")
        if stock is None:
            line += " | cheklanmagan"
        elif stock <= 0:
            line += " | ❌ TUGADI"
        else:
            line += f" | qoldiq: {stock}"
        lines.append(line)
    bot.send_message(
        message.chat.id,
        "Menyu:\n" + "\n".join(lines) +
        "\n\n🏷 Aksiya: /aksiya 17 (yoqish) | /aksiya off (o'chirish)\n"
        "🕒 Ish vaqti: /yopiq | /ochiq | /ish_vaqti 06:00 22:00\n"
        "🖨 Oshxona havolasi (Chrome uchun): /oshxona\n"
        "🧾 Bugungi cheklar holati: /cheklar\n"
        "📒 Nasiya va avans: /hisob\n"
        "📥 Telegramdan buyurtma: mijoz xabarini botga forward qiling\n"
        "📞 Telefon buyurtmasi: /qolda\n"
        "🍱 O'zingiz yig'ing bo'limi: /yigma\n"
        "🔗 Mijozni botga olib o'tish: /havola\n"
        "💼 Shaxsiy akkaunt (Business): /biznes\n"
        "🖨 Chekni qayta chiqarish: /chek 7\n"
        "🎁 Viktorina: /viktorina | g'olib: /gholib\n"
        "📣 E'lon yuborish: /elon matn | mijozlar soni: /mijozlar\n"
        "\n\n🧑‍🍳 Eng oson yo'l: pastdagi \"Menyuni boshqarish\" tugmasi orqali "
        "taomni rasmi bilan birga qo'shing/tahrirlang.\n\n"
        "Zaxira belgilash: /set_stock id soni (masalan: /set_stock 1 10)\n"
        "Barchasini \"Tugadi\" qilish (ishlamagan kun): /reset_stock\n"
        "Cheklovni olib tashlash: /set_stock id -1\n"
        f"Kategoriya o'zgartirish: /set_category id Kategoriya (masalan: /set_category 1 Ovqatlar)\n"
        f"Kategoriyalar: {', '.join(CATEGORIES)}\n\n"
        "Hisobot: /report (bugungi), /yesterday_report (kechagi)\n"
        "Admin qo'shish: /add_admin id | /remove_admin id | /admins\n"
        "Xodim qo'shish (faqat holat o'zgartira oladi): /add_staff id | /remove_staff id\n"
        "Buyurtmani o'chirish (faqat bugungi): /delete_order kunlik_raqami"
    )

# ---------- e'lon yuborish ----------

pending_broadcast = {}   # admin_id -> {"text": ..., "photo": file_id yoki None}

def broadcast_preview_keyboard():
    kb = types.InlineKeyboardMarkup(row_width=2)
    kb.add(types.InlineKeyboardButton("✅ Hammaga yuborish", callback_data="bc:go"),
           types.InlineKeyboardButton("❌ Bekor qilish", callback_data="bc:no"))
    return kb

@bot.message_handler(commands=["elon"])
def cmd_broadcast(message):
    if not is_owner(message.chat.id):
        return
    parts = message.text.split(" ", 1)
    total = len(active_user_ids())
    if len(parts) < 2 or not parts[1].strip():
        bot.send_message(
            message.chat.id,
            "📣 E'lon yuborish\n\n"
            f"Hozir botda {total} ta mijoz bor.\n\n"
            "Format: /elon xabar matni\n\n"
            "Masalan:\n"
            "/elon 🎁 Viktorina boshlandi! 15 ta savol, g'olibga bepul tushlik. "
            "Pastdagi \"🎁 Viktorina\" tugmasini bosing.\n\n"
            "Yuborishdan oldin sizga ko'rinish ko'rsatiladi — tasdiqlaysiz."
        )
        return

    text = parts[1].strip()
    pending_broadcast[message.chat.id] = {"text": text}
    bot.send_message(message.chat.id, "👁 Mijozlar shuni ko'radi:")
    bot.send_message(message.chat.id, text)
    bot.send_message(
        message.chat.id,
        f"📣 Qabul qiluvchilar: {total} ta mijoz.\n"
        "Yuborilgandan keyin qaytarib bo'lmaydi.",
        reply_markup=broadcast_preview_keyboard()
    )

@bot.callback_query_handler(func=lambda c: c.data.startswith("bc:"))
def cb_broadcast(call):
    if not is_owner(call.message.chat.id):
        bot.answer_callback_query(call.id, "Ruxsat yo'q.")
        return
    action = call.data.split(":", 1)[1]
    job = pending_broadcast.pop(call.message.chat.id, None)

    if action == "no" or not job:
        bot.answer_callback_query(call.id, "Bekor qilindi.")
        try:
            bot.edit_message_text("❌ E'lon bekor qilindi.", call.message.chat.id, call.message.message_id)
        except Exception:
            pass
        return

    bot.answer_callback_query(call.id, "Yuborilmoqda...")
    try:
        bot.edit_message_text("📣 Yuborilmoqda... tugagach xabar beraman.",
                              call.message.chat.id, call.message.message_id)
    except Exception:
        pass
    threading.Thread(target=run_broadcast, args=(call.message.chat.id, job["text"]), daemon=True).start()

def run_broadcast(admin_id, text):
    """E'lonni hamma mijozga yuboradi. Telegram cheklovini hisobga olib sekin yuboramiz."""
    ids = active_user_ids()
    users = load_users()
    yuborildi, bloklagan, xato = 0, 0, 0
    for i, uid in enumerate(ids):
        try:
            # Tugmalarni ham birga yuboramiz — mijoz /start bosmasa ham
            # yangi tugmalar (masalan "🎁 Viktorina") darhol paydo bo'ladi
            try:
                uname = (users.get(str(uid)) or {}).get("username")
                kb = main_keyboard(uid, uname)
            except Exception:
                kb = None
            bot.send_message(uid, text, reply_markup=kb)
            yuborildi += 1
        except Exception as e:
            msg = str(e).lower()
            if "blocked" in msg or "user is deactivated" in msg or "chat not found" in msg:
                mark_user_blocked(uid)
                bloklagan += 1
            else:
                xato += 1
                print(f"E'lon yuborishda xato ({uid}): {e}")
        time.sleep(0.06)          # sekundiga ~16 ta — Telegram chegarasidan past
        if (i + 1) % 100 == 0:
            try:
                bot.send_message(admin_id, f"… {i + 1}/{len(ids)} ta yuborildi")
            except Exception:
                pass
    try:
        bot.send_message(
            admin_id,
            f"📣 E'lon tugadi.\n\n"
            f"✅ Yetib bordi: {yuborildi} ta\n"
            + (f"🚫 Botni bloklagan: {bloklagan} ta\n" if bloklagan else "")
            + (f"⚠️ Xato: {xato} ta\n" if xato else "")
            + f"\nKeyingi e'lonlarda bloklaganlar o'tkazib yuboriladi."
        )
    except Exception:
        pass

@bot.message_handler(commands=["mijozlar"])
def cmd_users(message):
    if not is_owner(message.chat.id):
        return
    qoshildi = backfill_users_from_history()
    users = load_users()
    if qoshildi:
        bot.send_message(message.chat.id,
            f"🔄 Eski buyurtmalardan {qoshildi} ta mijoz ro'yxatga qo'shildi.")
    faol = [r for r in users.values() if not r.get("blocked")]
    blok = len(users) - len(faol)
    hafta = int(time.time()) - 7 * 86400
    yangi = len([r for r in users.values() if r.get("first_seen", 0) >= hafta])
    bot.send_message(
        message.chat.id,
        f"👥 Botdagi mijozlar\n\n"
        f"Jami: {len(users)} ta\n"
        f"Faol (e'lon boradi): {len(faol)} ta\n"
        + (f"Bloklagan: {blok} ta\n" if blok else "")
        + f"So'nggi 7 kunda qo'shilgan: {yangi} ta\n\n"
        "E'lon yuborish: /elon xabar matni"
    )

@bot.message_handler(commands=["viktorina"])
def cmd_quiz_admin(message):
    if not is_owner(message.chat.id):
        return
    parts = message.text.split()
    quiz = load_quiz()

    if len(parts) > 1 and parts[1].lower() in ("on", "yoq", "yoqish", "boshla"):
        if not quiz["questions"]:
            bot.send_message(message.chat.id, "Avval savollarni kiriting — \"🧑‍🍳 Menyuni boshqarish\" panelidagi Viktorina bo'limidan.")
            return
        quiz["active"] = True
        quiz["test"] = False
        save_quiz(quiz)
        bot.send_message(message.chat.id, f"🟢 Viktorina HAMMA UCHUN ochildi — {len(quiz['questions'])} ta savol.\n"
                                           "Mijozlarda \"🎁 Viktorina\" tugmasi paydo bo'ladi (ular /start bosgach).")
        return
    if len(parts) > 1 and parts[1].lower() in ("sinov", "test"):
        if not quiz["questions"]:
            bot.send_message(message.chat.id, "Avval savollarni kiriting.")
            return
        quiz["active"] = True
        quiz["test"] = True
        save_quiz(quiz)
        bot.send_message(message.chat.id, "🧪 Sinov rejimi yoqildi — viktorina faqat sizga va xodimlarga ko'rinadi.\n"
                                           "Sinab bo'lgach: /viktorina on — hammaga ochiladi.")
        return
    if len(parts) > 1 and parts[1].lower() in ("off", "ochir", "toxtat", "tugat"):
        quiz["active"] = False; save_quiz(quiz)
        bot.send_message(message.chat.id, "⏹ Viktorina to'xtatildi. Natijalar saqlanib qoldi — /gholib bilan ko'ring.")
        return

    board = quiz_leaderboard()
    if not quiz["active"]:
        holat = "⏹ to'xtatilgan"
    elif quiz["test"]:
        holat = "🧪 sinov rejimi (faqat adminlar ko'radi)"
    else:
        holat = "🟢 hamma uchun ochiq"
    sovga = quiz.get("prize") or ""
    txt = (
        "🎁 Viktorina: " + quiz["title"] + "\n"
        "Holat: " + holat + "\n"
        "Savollar: " + str(len(quiz["questions"])) + " ta\n"
        "Tugatganlar: " + str(len(board)) + " ta\n"
    )
    if sovga:
        txt += "Sovg'a: " + sovga + "\n"
    txt += (
        "\nSinov rejimi: /viktorina sinov\n"
        "Hammaga ochish: /viktorina on\n"
        "To'xtatish: /viktorina off\n"
        "G'olib va to'liq ro'yxat: /gholib\n"
        "Savollarni kiritish: \"🧑‍🍳 Menyuni boshqarish\" paneli → Viktorina"
    )
    bot.send_message(message.chat.id, txt)

@bot.message_handler(commands=["gholib", "golib"])
def cmd_quiz_winners(message):
    if not is_owner(message.chat.id):
        return
    quiz = load_quiz()
    board = quiz_leaderboard()
    if not board:
        bot.send_message(message.chat.id, "Hali hech kim viktorinani tugatmagan.")
        return
    total = len(quiz["questions"]) or 0
    lines = [f"🏆 {quiz['title']} — to'liq ro'yxat", ""]
    for i, r in enumerate(board, start=1):
        who = f"@{r['username']}" if r.get("username") else f"ID {r['uid']}"
        lines.append(f"{i}. {r['name']} ({who}) — {r['correct']}/{total} · {fmt_secs(r['ms'])}")
    w = board[0]
    lines += ["", "— — —",
              f"🥇 G'olib: {w['name']}" + (f" (@{w['username']})" if w.get("username") else ""),
              f"   {w['correct']}/{total} to'g'ri, {fmt_secs(w['ms'])}",
              "", "G'olibga yozish uchun yuqoridagi @ nomiga bosing.",
              "Agar @ nomi bo'lmasa — u viktorinani tugatganda sizga kelgan xabarga Reply qiling."]
    text = "\n".join(lines)
    for i in range(0, len(text), 3800):
        bot.send_message(message.chat.id, text[i:i+3800])

@bot.message_handler(commands=["chek"])
def cmd_reprint(message):
    """Buyurtmani qayta chop etishga qo'yish: /chek 7"""
    if not is_owner(message.chat.id):
        return
    parts = message.text.split()
    if len(parts) < 2 or not parts[1].isdigit():
        bot.send_message(message.chat.id,
            "Format: /chek 7  — bugungi 7-buyurtmani qayta chop etishga qo'yadi.\n"
            "Chek oshxonadagi telefonda o'zi chiqadi.")
        return
    no = int(parts[1])
    orders = load_orders()
    day = today_key()
    target = next((o for o in orders if o.get("day_key") == day and o.get("daily_number") == no), None)
    if not target:
        bot.send_message(message.chat.id, f"Bugungi buyurtmalar orasida #{no} topilmadi.")
        return
    target["printed"] = False
    save_orders(orders)
    bot.send_message(message.chat.id, f"🖨 #{no} qayta chop etishga qo'yildi — oshxona telefonida chiqadi.")

@bot.message_handler(commands=["yopiq", "ochiq", "ish_vaqti"])
def cmd_hours(message):
    if not is_owner(message.chat.id):
        return
    cmd = message.text.split()[0].lstrip("/").split("@")[0].lower()
    parts = message.text.split()

    if cmd == "yopiq":
        set_hours(closed_today=True)
        bot.send_message(message.chat.id, "🔴 Bot yopildi — mijozlarga \"ish vaqtimiz tugadi\" xabari chiqadi.\n"
                                           "Ochish uchun: /ochiq")
        return
    if cmd == "ochiq":
        set_hours(closed_today=False)
        st = shop_status()
        extra = "" if st["open"] else f"\n\n⚠️ Lekin jadval bo'yicha hozir yopiq ({st['open_time']}–{st['close_time']}). Jadvalni o'chirish: /ish_vaqti off"
        bot.send_message(message.chat.id, "🟢 Bot ochildi — buyurtmalar qabul qilinadi." + extra)
        return

    # /ish_vaqti
    h = get_hours()
    st = shop_status()
    if len(parts) == 1:
        holat = "🟢 OCHIQ" if st["open"] else "🔴 YOPIQ"
        jadval = f"yoniq ({h['open']} – {h['close']})" if h["schedule_on"] else "o'chiq (kecha-kunduz)"
        bot.send_message(
            message.chat.id,
            f"Hozirgi holat: {holat}\n"
            f"Bugun yopiq: {'ha' if h['closed_today'] else 'yo‘q'}\n"
            f"Kunlik jadval: {jadval}\n\n"
            "Jadval belgilash: /ish_vaqti 06:00 22:00\n"
            "Jadvalni o'chirish: /ish_vaqti off\n"
            "Bugunga yopish: /yopiq | ochish: /ochiq\n\n"
            "Bularni \"🧑‍🍳 Menyuni boshqarish\" panelidan ham qilish mumkin."
        )
        return
    if parts[1].lower() in ("off", "o'chir", "ochir"):
        set_hours(schedule_on=False)
        bot.send_message(message.chat.id, "🕒 Kunlik jadval o'chirildi — bot kecha-kunduz buyurtma qabul qiladi.")
        return
    if len(parts) >= 3 and valid_hhmm(parts[1]) and valid_hhmm(parts[2]):
        h = set_hours(schedule_on=True, open_time=parts[1], close_time=parts[2])
        st = shop_status()
        bot.send_message(message.chat.id,
            f"🕒 Ish vaqti belgilandi: {h['open']} – {h['close']}\n"
            f"Hozir: {'🟢 ochiq' if st['open'] else '🔴 yopiq'}")
        return
    bot.send_message(message.chat.id, "Format: /ish_vaqti 06:00 22:00\nYoki: /ish_vaqti off")

@bot.message_handler(commands=["aksiya", "sale"])
def cmd_sale(message):
    if not is_owner(message.chat.id):
        return
    parts = message.text.split()
    disc = get_discount()
    if len(parts) == 1:
        holat = f"YONIQ — barcha narx −{disc['percent']}%" if disc["active"] else "o'chiq"
        bot.send_message(
            message.chat.id,
            f"🏷 Aksiya holati: {holat}\n\n"
            "Yoqish: /aksiya 17  (17% chegirma)\n"
            "O'chirish: /aksiya off\n\n"
            "Buni \"🧑‍🍳 Menyuni boshqarish\" panelidan bir bosishda ham qilish mumkin."
        )
        return
    arg = parts[1].strip().lower()
    if arg in ("off", "o'chir", "ochir", "0", "yo'q", "yoq"):
        set_discount(active=False)
        bot.send_message(message.chat.id, "🏷 Aksiya o'chirildi — narxlar odatiyga qaytdi.")
        return
    try:
        pct = int(arg.rstrip("%"))
    except Exception:
        bot.send_message(message.chat.id, "Format: /aksiya 17  yoki  /aksiya off")
        return
    if not (1 <= pct <= 90):
        bot.send_message(message.chat.id, "Chegirma foizi 1 dan 90 gacha bo'lishi kerak.")
        return
    d = set_discount(active=True, percent=pct)
    bot.send_message(message.chat.id, f"🏷 Aksiya yoqildi — barcha taom narxi −{d['percent']}%.\n"
                                       "O'chirish uchun: /aksiya off")

@bot.message_handler(commands=["set_category"])
def cmd_set_category(message):
    if not is_owner(message.chat.id):
        return
    try:
        parts = message.text.split(" ", 1)[1].split(" ", 1)
        dish_id = int(parts[0])
        category_raw = parts[1]
    except Exception:
        bot.send_message(
            message.chat.id,
            "Format: /set_category id Kategoriya\nMasalan: /set_category 1 Ovqatlar\n"
            f"Kategoriyalar: {', '.join(CATEGORIES)}"
        )
        return
    category = match_category(category_raw)
    if category is None:
        bot.send_message(message.chat.id, f"Bunday kategoriya yo'q. Mavjudlari: {', '.join(CATEGORIES)}")
        return
    menu = load_menu()
    dish = next((d for d in menu if d["id"] == dish_id), None)
    if not dish:
        bot.send_message(message.chat.id, f"#{dish_id} topilmadi. /menu bilan tekshiring.")
        return
    dish["category"] = category
    save_menu(menu)
    bot.send_message(message.chat.id, f"{dish['name']} — kategoriyasi \"{category}\"ga o'zgartirildi.")

@bot.message_handler(commands=["set_tarkib", "set_tarkibi"])
def cmd_set_items(message):
    """Taom narxiga nima qo'shib berilishini belgilaydi. /set_tarkib 3 non,salat,suv"""
    if not is_owner(message.chat.id):
        return
    parts = (message.text or "").split(maxsplit=2)
    mavjud = ", ".join(SET_KEYS)
    if len(parts) < 3:
        bot.send_message(message.chat.id,
            "Taom narxiga nima qo'shib berilishini belgilaysiz.\n\n"
            "Foydalanish:\n"
            "/set_tarkib <taom_id> non,salat,suv\n"
            "/set_tarkib <taom_id> yoq — tozalash\n\n"
            f"Mavjud kalitlar: {mavjud}\n"
            "Ro'yxatda yo'q narsani qo'shish uchun Mini App'dagi "
            "«Menyuni boshqarish» bo'limidan foydalaning.\n\n"
            "Taom raqamlarini /menu bilan ko'rasiz.")
        return
    try:
        dish_id = int(parts[1])
    except ValueError:
        bot.send_message(message.chat.id, "Taom raqamini to'g'ri kiriting. Masalan: /set_tarkib 3 non,suv")
        return

    menu = load_menu()
    dish = next((d for d in menu if d["id"] == dish_id), None)
    if not dish:
        bot.send_message(message.chat.id, f"#{dish_id} raqamli taom topilmadi.")
        return

    raw = parts[2].strip()
    if raw.lower() in ("yoq", "yo'q", "-", "tozala", "clear"):
        dish["set_items"] = []
        dish["set_extra"] = ""
        save_menu(menu)
        bot.send_message(message.chat.id, f"✅ «{dish['name']}» endi oddiy taom — set tarkibi olib tashlandi.")
        return

    keys = parse_set_keys(raw)
    noma_lum = [p.strip() for p in raw.replace("+", ",").split(",")
                if p.strip() and p.strip().lower() not in SET_BY_KEY]
    if not keys and not noma_lum:
        bot.send_message(message.chat.id, f"Hech narsa tanilmadi.\nMavjud kalitlar: {mavjud}")
        return
    dish["set_items"] = keys
    dish["set_extra"] = ", ".join(noma_lum)[:80]
    save_menu(menu)

    korinish = set_line(keys, dish["set_extra"], "uz", with_emoji=True) or "—"
    javob = f"✅ «{dish['name']}» set tarkibi:\n{korinish}"
    if noma_lum:
        javob += ("\n\nℹ️ " + ", ".join(noma_lum) + " — ro'yxatda yo'q, "
                  "shuning uchun faqat o'zbekcha yozuv sifatida qo'shildi.")
    bot.send_message(message.chat.id, javob)

@bot.message_handler(commands=["set_stock"])
def cmd_set_stock(message):
    if not is_owner(message.chat.id):
        return
    try:
        parts = message.text.split()
        dish_id = int(parts[1])
        soni = int(parts[2])
    except Exception:
        bot.send_message(message.chat.id, "Format: /set_stock id soni\nMasalan: /set_stock 1 10\nCheklovsiz qilish: /set_stock 1 -1")
        return
    menu = load_menu()
    dish = next((d for d in menu if d["id"] == dish_id), None)
    if not dish:
        bot.send_message(message.chat.id, f"#{dish_id} topilmadi. /menu bilan tekshiring.")
        return
    if soni < 0:
        dish["stock"] = None
        save_menu(menu)
        bot.send_message(message.chat.id, f"{dish['name']} — endi cheklanmagan (istagancha buyurtma qilinadi).")
    else:
        dish["stock"] = soni
        save_menu(menu)
        bot.send_message(message.chat.id, f"{dish['name']} — zaxira {soni} dona qilib belgilandi.")

@bot.message_handler(commands=["reset_stock"])
def cmd_reset_stock(message):
    if not is_owner(message.chat.id):
        return
    menu = load_menu()
    if not menu:
        bot.send_message(message.chat.id, "Menyu bo'sh.")
        return
    for d in menu:
        d["stock"] = 0
    save_menu(menu)
    bot.send_message(
        message.chat.id,
        "✅ Barcha taomlar \"Tugadi\" holatiga qaytarildi.\n"
        "Bugun tayyorlaydigan taomlaringiz uchun /set_stock id soni yozing."
    )

@bot.message_handler(commands=["add_dish"])
def cmd_add_dish(message):
    if not is_owner(message.chat.id):
        return
    try:
        payload = message.text.split(" ", 1)[1]
        name, price, desc, category, cat_warning = parse_dish_caption(payload)
    except Exception:
        bot.send_message(
            message.chat.id,
            "Format: /add_dish Nomi;Narxi;Tavsif;Kategoriya\n"
            f"Kategoriyalar: {', '.join(CATEGORIES)}\n"
            "Kategoriyani yozmasangiz \"Boshqa mahsulotlar\"ga tushadi."
        )
        return
    menu = load_menu()
    new_id = (max([d["id"] for d in menu], default=0)) + 1
    menu.append({"id": new_id, "name": name, "price": price, "desc": desc, "photo_id": None, "local_photo": None, "stock": 0, "category": category})
    save_menu(menu)
    warn = f"\n⚠️ Kategoriya tanilmadi, \"{DEFAULT_CATEGORY}\"ga qo'yildi." if cat_warning else ""
    if set_items:
        warn += "\n🍽 Set: " + set_line(set_items, "", "uz", with_emoji=True)
    bot.send_message(message.chat.id, f"Qo'shildi (rasmsiz): #{new_id} {name} — {fmt_sum(price)} | {category}{warn}\n"
                                       f"Diqqat: zaxira 0 — sotuvga chiqarish uchun /set_stock {new_id} soni yozing.")

@bot.message_handler(content_types=["photo"])
def handle_owner_photo(message):
    if not is_owner(message.chat.id):
        return
    caption = (message.caption or "").strip()

    if caption.lower() == "logo":
        file_id = message.photo[-1].file_id
        try:
            download_telegram_file(file_id, LOGO_PATH)
        except Exception as e:
            bot.send_message(message.chat.id, f"Logotipni saqlashda xato: {e}")
            return
        settings = load_settings()
        settings["logo_photo_id"] = file_id
        save_settings(settings)
        bot.send_message(message.chat.id, "Logotip saqlandi ✅ Endi /start va Mini App'da ko'rinadi.")
        return

    if not caption:
        bot.send_message(
            message.chat.id,
            "Taom rasmini caption bilan yuboring: Nomi;Narxi;Tavsif;Kategoriya;Set\n"
            f"Kategoriyalar: {', '.join(CATEGORIES)}\n"
            f"Set (ixtiyoriy, narxga qo'shib beriladigan): {', '.join(SET_KEYS)}\n"
            "Namuna: Osh;18;Qo'y go'shti bilan;Ovqatlar;non,salat,suv\n"
            "Kategoriyani yozmasangiz \"Boshqa mahsulotlar\"ga tushadi.\n"
            "Yoki logotip sifatida saqlash uchun caption'ga \"logo\" deb yozing."
        )
        return

    try:
        name, price, desc, category, cat_warning, set_items = parse_dish_caption(caption)
    except Exception:
        bot.send_message(message.chat.id, "Caption formati noto'g'ri. Namuna: Osh;35;Palov go'shtli;Ovqatlar")
        return

    photo_id = message.photo[-1].file_id
    menu = load_menu()
    new_id = (max([d["id"] for d in menu], default=0)) + 1
    local_filename = f"{new_id}.jpg"
    try:
        download_telegram_file(photo_id, os.path.join(DISH_PHOTOS_DIR, local_filename))
    except Exception:
        local_filename = None
    menu.append({
        "id": new_id, "name": name, "price": price, "desc": desc,
        "photo_id": photo_id, "local_photo": local_filename, "stock": 0, "category": category,
        "set_items": set_items, "set_extra": ""
    })
    save_menu(menu)
    warn = f"\n⚠️ Kategoriya tanilmadi, \"{DEFAULT_CATEGORY}\"ga qo'yildi." if cat_warning else ""
    if set_items:
        warn += "\n🍽 Set: " + set_line(set_items, "", "uz", with_emoji=True)
    bot.send_message(message.chat.id, f"Qo'shildi (rasm bilan): #{new_id} {name} — {fmt_sum(price)} | {category}{warn}\n"
                                       f"Diqqat: zaxira 0 — sotuvga chiqarish uchun /set_stock {new_id} soni yozing.")

@bot.message_handler(commands=["remove_dish"])
def cmd_remove_dish(message):
    if not is_owner(message.chat.id):
        return
    try:
        dish_id = int(message.text.split(" ", 1)[1].strip())
    except Exception:
        bot.send_message(message.chat.id, "Format: /remove_dish id")
        return
    menu = load_menu()
    menu = [d for d in menu if d["id"] != dish_id]
    save_menu(menu)
    bot.send_message(message.chat.id, f"#{dish_id} o'chirildi.")

@bot.message_handler(commands=["delete_order"])
def cmd_delete_order(message):
    if not is_owner(message.chat.id):
        return
    try:
        daily_number = int(message.text.split(" ", 1)[1].strip())
    except Exception:
        bot.send_message(message.chat.id, "Format: /delete_order kunlik_raqami\nMasalan: /delete_order 3\n"
                                           "(Faqat BUGUNGI buyurtmalar uchun ishlaydi)")
        return
    orders = load_orders()
    day_key = today_key()
    target = next((o for o in orders if o.get("day_key") == day_key and o.get("daily_number") == daily_number), None)
    if not target:
        bot.send_message(message.chat.id, f"Bugungi buyurtmalar orasida #{daily_number} topilmadi.")
        return
    orders = [o for o in orders if o["id"] != target["id"]]
    renumber_day(orders, day_key)
    save_orders(orders)
    bot.send_message(
        message.chat.id,
        f"🗑 Buyurtma #{daily_number} o'chirildi. Qolgan bugungi buyurtmalar qayta raqamlandi — bo'shliq qolmadi."
    )

# ================= MINI APP (Flask) =================

def validate_init_data(init_data):
    """Telegram WebApp initData'ni tekshiradi. Muvaffaqiyatli bo'lsa user dict qaytaradi."""
    try:
        data = {}
        for pair in init_data.split("&"):
            if "=" not in pair:
                continue
            k, v = pair.split("=", 1)
            data[urllib.parse.unquote(k)] = urllib.parse.unquote(v)

        received_hash = data.pop("hash", None)
        if not received_hash:
            print("initData: hash yo'q")
            return None

        data_check_string = "\n".join(f"{k}={v}" for k, v in sorted(data.items()))
        secret_key = hmac.new(b"WebAppData", BOT_TOKEN.encode(), hashlib.sha256).digest()
        computed_hash = hmac.new(secret_key, data_check_string.encode(), hashlib.sha256).hexdigest()

        if not hmac.compare_digest(computed_hash, received_hash):
            print("initData: hash mos kelmadi")
            return None

        user_raw = data.get("user")
        if not user_raw:
            return None
        return json.loads(user_raw)
    except Exception as e:
        print(f"initData validatsiya xatosi: {e}")
        return None

FB_DOMAIN_VERIFICATION = os.environ.get("FB_DOMAIN_VERIFICATION", "8wzj9py65823fj786xfth1evp0esou")

@app.route("/")
def miniapp_index():
    try:
        with open("index.html", encoding="utf-8") as fh:
            html = fh.read()
        if FB_DOMAIN_VERIFICATION and "facebook-domain-verification" not in html:
            tag = f'<meta name="facebook-domain-verification" content="{FB_DOMAIN_VERIFICATION}" />'
            html = re.sub(r"(<head[^>]*>)", lambda m: m.group(1) + "\n" + tag, html, count=1, flags=re.I)
        resp = app.response_class(html, mimetype="text/html")
    except Exception:
        resp = send_from_directory(".", "index.html")
    resp.headers["Cache-Control"] = "no-store, no-cache, must-revalidate, max-age=0"
    resp.headers["Pragma"] = "no-cache"
    return resp

@app.route("/static/dishes/<path:filename>")
def serve_dish_photo(filename):
    return send_from_directory(DISH_PHOTOS_DIR, filename)

@app.route("/static/logo.jpg")
def serve_logo():
    if not os.path.exists(LOGO_PATH):
        return "", 404
    return send_from_directory(os.path.dirname(LOGO_PATH), os.path.basename(LOGO_PATH))

@app.route("/api/menu")
def api_menu():
    menu = load_menu()
    disc = get_discount()
    grouped = group_menu_by_category(menu)
    out = []
    for d in menu:
        unit = discounted_price(d["price"], disc)
        item = {
            "id": d["id"], "name": d["name"], "price": unit,
            "desc": d.get("desc", ""), "stock": d.get("stock"),
            "category": d.get("category", DEFAULT_CATEGORY)
        }
        skeys = dish_set_keys(d)
        if skeys:
            item["set"] = skeys
        if (d.get("set_extra") or "").strip():
            item["set_extra"] = d["set_extra"].strip()
        if unit != d["price"]:
            item["old_price"] = d["price"]
        if d.get("local_photo"):
            item["photo_url"] = f"/static/dishes/{d['local_photo']}"
        out.append(item)
    # kategoriya + mavjudlik bo'yicha saralangan tartibda qaytaramiz
    ordered_ids = [d["id"] for _, dishes in grouped for d in dishes]
    order_index = {did: i for i, did in enumerate(ordered_ids)}
    out.sort(key=lambda it: order_index.get(it["id"], 999999))
    categories_present = [cat for cat, dishes in grouped]
    return jsonify({
        "menu": out,
        "categories": categories_present,
        "category_emoji": CATEGORY_EMOJI,
        "business_name": BUSINESS_NAME,
        "tagline": BUSINESS_TAGLINE,
        "discount": disc,
        "set_catalog": set_catalog_payload(),
        "builder_category": BUILDER_CATEGORY,
        "builder_min": builder_min(),
        "shop": shop_status(),
        "logo_url": "/static/logo.jpg" if os.path.exists(LOGO_PATH) else None
    })

def verify_signed_user(uid, uname, ts, sig):
    if not (uid and ts and sig):
        return None
    payload = f"{uid}:{uname or ''}:{ts}"
    expected = hmac.new(BOT_TOKEN.encode(), payload.encode(), hashlib.sha256).hexdigest()
    if not hmac.compare_digest(expected, sig):
        return None
    return {"id": int(uid), "username": uname or None}

@app.route("/api/lang", methods=["POST"])
def api_set_lang():
    """Mini App'da tanlangan tilni saqlaymiz — bot xabarlari ham shu tilda bo'ladi."""
    body = request.get_json(force=True, silent=True) or {}
    lang = (body.get("lang") or "").strip()
    if lang not in SUPPORTED_LANGS:
        return jsonify({"error": "noma'lum til"}), 400
    user = validate_init_data(body.get("initData", "")) or verify_signed_user(
        body.get("uid"), body.get("uname"), body.get("ts"), body.get("sig"))
    if not user or not user.get("id"):
        return jsonify({"error": "foydalanuvchi aniqlanmadi"}), 400
    set_user_lang(user["id"], lang)
    return jsonify({"ok": True})

@app.route("/api/order", methods=["POST"])
def api_order():
    body = request.get_json(force=True, silent=True) or {}
    init_data = body.get("initData", "")
    user = validate_init_data(init_data) or {}
    verified = bool(user)

    if not user:
        # 1) avval botning o'zi imzolagan uid/uname/ts/sig orqali tekshiramiz (eng ishonchli)
        signed_user = verify_signed_user(
            body.get("uid"), body.get("uname"), body.get("ts"), body.get("sig")
        )
        if signed_user:
            user = signed_user
            verified = True
        else:
            # 2) bo'lmasa, Telegram tomonidan berilgan (imzosiz) ma'lumotdan foydalanamiz
            unsafe_user = body.get("unsafe_user")
            if isinstance(unsafe_user, dict):
                user = unsafe_user

    items_cart = body.get("cart", {})
    phone = (body.get("phone") or "").strip()
    address_text = (body.get("address_text") or "").strip() or None
    latitude = body.get("latitude")
    longitude = body.get("longitude")
    note = (body.get("note") or "").strip()
    customer_name = (body.get("name") or "").strip() or user.get("first_name") or "Mijoz"

    st = shop_status()
    # Admin yopiq paytda ham buyurtma bera oladi (sinab ko'rish uchun)
    if not st["open"] and not (user.get("id") and is_owner(user["id"])):
        lang = get_user_lang(user.get("id")) if user else "uz"
        return jsonify({"error": closed_message(lang, st), "closed": True}), 423

    if not items_cart:
        return jsonify({"error": "Savatingiz bo'sh."}), 400
    # Instagram'dan kelgan mijozni raqam tekshiruvidan OLDIN aniqlaymiz:
    # unda Telegram hisobi bo'lmaydi, lekin bog'lanish yo'li bor — Direct.
    ig_extra = None
    if not user.get("id"):
        try:
            _igsid = ig_identity_from_request(body)
        except Exception:
            _igsid = None
        if _igsid:
            ig_extra = {"source": "instagram", "ig_user_id": _igsid, "ig_username": ig_username(_igsid)}

    # Raqam majburiy emas: raqami bo'lmagan mijoz bilan bot orqali bog'lanamiz.
    # Lekin raqam ham, Telegram hisobi ham, Instagram ham bo'lmasa — iloji yo'q.
    if not phone and not user.get("id") and not ig_extra:
        return jsonify({"error": "Telefon raqamingizni kiriting — aks holda siz bilan bog'lana olmaymiz."}), 400

    # keshbekni faqat shaxsi tasdiqlangan foydalanuvchi ishlata oladi —
    # imzosiz so'rov bilan birovning hisobidan yechib bo'lmaydi
    order, error = create_order(
        extra=ig_extra,
        use_cashback=bool(body.get("use_cashback")) and verified,
        items_cart=items_cart,
        customer_name=customer_name,
        phone=phone,
        latitude=latitude,
        longitude=longitude,
        address_text=address_text,
        note=note,
        tg_user_id=user.get("id"),
        username=user.get("username"),
    )
    if error:
        return jsonify({"error": error}), 409
    if ig_extra:
        threading.Thread(target=ig_send_text, args=(ig_extra["ig_user_id"],
            build_customer_receipt_text(order, "uz")
            + f"\n\n🎁 Telegram botimizdan buyurtma bersangiz har safar 5% keshbek olasiz: {IG_TG_BOT_URL}"),
            daemon=True).start()
    return jsonify({
        "ok": True,
        "order_id": order["daily_number"],
        "total": order["total"],
        "cashback_used": order_cashback_used(order),
        "payable": order_cash_due(order),
        "advance_used": order_advance_used(order),
        "cashback_balance": cashback_balance(user.get("id")) if user.get("id") else 0,
        "account_balance": account_balance(user.get("id")) if user.get("id") else 0,
    })

@app.route("/api/cashback")
def api_cashback():
    """Mini App tepasidagi keshbek balansi."""
    cfg = get_cashback_cfg()
    user = (validate_init_data(request.args.get("initData", ""))
            or verify_signed_user(request.args.get("uid"), request.args.get("uname"),
                                  request.args.get("ts"), request.args.get("sig")))
    # imzosiz so'rovga balans bermaymiz — birovning hisobini ko'rib bo'lmaydi
    uid = user["id"] if user else None
    hist = []
    for h in (account_history(uid, 12) if uid else []):
        hist.append({
            "ts": h.get("ts", 0),
            "delta": money(h.get("delta", 0)),
            "bal": money(h.get("bal", 0)),
            "order_id": h.get("order_id"),
            "note": h.get("note") or "",
        })
    return jsonify({
        "active": cfg["active"],
        "percent": cfg["percent"],
        "balance": cashback_balance(uid) if uid else 0,
        "account": {
            "balance": account_balance(uid) if uid else 0,
            "history": hist,
        },
    })

# ---------- admin paneli (Mini App orqali taom qo'shish) ----------

KITCHEN_PAGE_HTML = """<!doctype html>
<html lang="uz">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1, maximum-scale=1">
<title>Oshxona — chek chiqarish</title>
<style>
  :root{
    --bg:#0f1115; --fg:#f2f0ea; --dim:#9aa0ad; --line:#272c36; --card:#171a21;
    --ok:#22c55e; --warn:#f59e0b; --bad:#ef4444; --gold:#e3b34a;
  }
  *{box-sizing:border-box;}
  body{
    margin:0; background:var(--bg); color:var(--fg); padding-bottom:24px;
    font-family:-apple-system,BlinkMacSystemFont,"Segoe UI",Roboto,sans-serif;
    -webkit-tap-highlight-color:transparent;
  }
  header{
    position:sticky; top:0; z-index:5; padding:12px 14px;
    background:rgba(15,17,21,.95); backdrop-filter:blur(10px);
    border-bottom:1px solid var(--line);
  }
  .row{ display:flex; align-items:center; gap:10px; }
  h1{ font-size:16px; margin:0; flex:1; }
  .dot{ width:10px; height:10px; border-radius:50%; background:var(--bad); flex:none; }
  .dot.on{ background:var(--ok); }
  .sub{ font-size:12px; color:var(--dim); margin-top:3px; }

  .bar{ display:flex; gap:8px; flex-wrap:wrap; margin-top:11px; }
  button{
    font:inherit; font-size:14px; font-weight:600; cursor:pointer;
    padding:10px 14px; border-radius:10px; border:1px solid var(--line);
    background:#1d222c; color:var(--fg);
  }
  button.main{ background:var(--gold); color:#1a1305; border-color:transparent; }
  button.ghost{ background:transparent; color:var(--dim); }
  button:disabled{ opacity:.45; }
  button:focus-visible{ outline:2px solid var(--gold); outline-offset:2px; }

  .opts{ display:flex; gap:14px; align-items:center; flex-wrap:wrap; margin-top:11px; font-size:13px; color:var(--dim); }
  .opts label{ display:flex; align-items:center; gap:7px; }
  .opts input[type=checkbox]{ width:19px; height:19px; accent-color:var(--gold); }
  select{
    font:inherit; font-size:13px; padding:6px 8px; border-radius:8px;
    background:#1d222c; color:var(--fg); border:1px solid var(--line);
  }

  main{ padding:14px; }
  .msg{ font-size:13px; padding:10px 12px; border-radius:10px; margin-bottom:12px; line-height:1.5; }
  .msg.ok{ background:rgba(34,197,94,.12); color:#86efac; }
  .msg.err{ background:rgba(239,68,68,.12); color:#fca5a5; }
  .msg.info{ background:#171a21; color:var(--dim); border:1px solid var(--line); }

  .order{
    background:var(--card); border:1px solid var(--line); border-radius:13px;
    padding:13px 14px; margin-bottom:11px;
  }
  .order .top{ display:flex; align-items:baseline; gap:9px; }
  .order .no{ font-size:19px; font-weight:800; color:var(--gold); }
  .order .who{ flex:1; font-size:14px; font-weight:600; }
  .order .sum{ font-size:14px; font-weight:800; }
  .order ul{ margin:8px 0 10px; padding-inline-start:19px; font-size:13px; color:var(--dim); line-height:1.65; }
  .order .acts{ display:flex; gap:8px; }
  .order .acts button{ flex:1; padding:9px 0; font-size:13.5px; }

  .empty{ text-align:center; color:var(--dim); padding:40px 16px; font-size:14px; line-height:1.6; }
  pre.prev{
    background:#fff; color:#111; padding:10px; border-radius:8px;
    font-family:ui-monospace,Menlo,Consolas,monospace; font-size:11px; line-height:1.35;
    white-space:pre; overflow-x:auto; margin:9px 0 0;
  }
  details{ margin-top:16px; font-size:13px; color:var(--dim); }
  details summary{ cursor:pointer; padding:7px 0; }
  details ol{ padding-inline-start:20px; line-height:1.7; }
  details code{ background:#1d222c; padding:1px 5px; border-radius:4px; }

  .logoprev{
    width:38px; height:38px; border-radius:7px; background:#fff; object-fit:contain;
    border:1px solid #2b313d; vertical-align:middle; margin-inline-start:7px;
    image-rendering:pixelated;
  }

  /* chek chiqdimi — tasdiqlash paneli */
  #confirmBar{
    position:fixed; inset-inline:0; bottom:0; z-index:90;
    background:#171a21; border-top:1px solid var(--gold);
    padding:13px 14px calc(13px + env(safe-area-inset-bottom,0px));
    display:flex; flex-direction:column; gap:10px;
    box-shadow:0 -10px 26px rgba(0,0,0,.5);
  }
  #confirmBar[hidden]{ display:none; }
  #confirmBar .cbq{ font-size:14.5px; font-weight:600; line-height:1.4; }
  #confirmBar .cbrow{ display:flex; gap:9px; }
  #confirmBar button{ flex:1; padding:13px 0; font-size:14px; font-weight:700; border-radius:11px; }

  /* tizim orqali chop etish — faqat chek chiqadi */
  #printArea{ display:none; }
  @media print{
    body > *{ display:none !important; }
    #printArea{
      display:block !important; margin:0; padding:0;
      color:#000; background:#fff;
      font-family:ui-monospace,"Courier New",monospace;
      font-size:11pt; line-height:1.28; white-space:pre;
    }
    #printArea img.plogo{
      display:block; margin:0 auto 1.5mm; width:72%; max-width:100%; height:auto;
    }
    #printArea pre{ margin:0; font:inherit; white-space:pre; }
    #printArea pre:empty{ height:1em; }   /* bo'sh qator ham joy egallasin */
    #printArea.sz-n pre{ font-size:12pt; line-height:1.12; font-weight:600; }
    #printArea.sz-h pre{ font-size:13pt; line-height:1.2; font-weight:600; }
    #printArea.sz-b pre{ font-size:17pt; line-height:1.18; font-weight:700; }
    /* qator uslublari: taom nomi qalin, summa ikki barobar */
    #printArea pre.bl-b{ font-weight:900; }
    #printArea pre.bl-d, #printArea pre.bl-db{
      font-size:2em; line-height:1.05; letter-spacing:-0.02em;
    }
    #printArea pre.bl-db{ font-weight:900; }
    #printArea img.pfoot{
      display:block; margin:1mm auto 0; width:97%; max-width:100%; height:auto;
    }
    #printArea, #printArea pre, #printArea img{
      page-break-inside:avoid; break-inside:avoid;
    }
    #confirmBar{ display:none !important; }
  }
</style>
<style id="pageStyle">@page{ size:80mm auto; margin:2mm; }</style>
</head>
<body>

<header>
  <div class="row">
    <span class="dot" id="dot"></span>
    <h1>Oshxona — chek chiqarish</h1>
    <span id="count" style="font-size:13px;color:var(--dim)"></span>
  </div>
  <div class="sub" id="state">Ulanmoqda...</div>
  <div class="bar">
    <button class="main" id="btConnect">🖨 Printerni ulash</button>
    <button id="btTest">Sinov cheki</button>
    <button class="ghost" id="btChan" hidden>Boshqa kanal</button>
    <button class="ghost" id="btAgain">Qayta chiqarish</button>
  </div>
  <div class="opts">
    <label><input type="checkbox" id="auto" checked> Avtomatik chiqarsin</label>
    <label><input type="checkbox" id="snd" checked> Ovoz</label>
    <label title="Chek tepasida nom yozuvi o'rniga logo rasmi chiqadi">
      <input type="checkbox" id="logo" checked> Logo bilan
      <img id="logoPrev" class="logoprev" alt="" hidden>
    </label>
    <label>Qog'oz
      <select id="w">
        <option value="48" selected>48 belgi (80 mm)</option>
        <option value="46">46 belgi</option>
        <option value="44">44 belgi</option>
        <option value="42">42 belgi (72 mm)</option>
        <option value="40">40 belgi</option>
        <option value="38">38 belgi</option>
        <option value="36">36 belgi</option>
        <option value="32">32 belgi (58 mm)</option>
        <option value="28">28 belgi</option>
      </select>
    </label>
    <label title="Logo chiqmay qolsa yoki chekda oq chiziqlar bo'lsa shuni o'zgartiring">Tezlik
      <select id="spd">
        <option value="0" selected>Tez</option>
        <option value="1">O'rtacha</option>
        <option value="3">Sekin</option>
      </select>
    </label>
    <label>Usul
      <select id="mode">
        <option value="bt" selected>Bevosita Bluetooth</option>
        <option value="sys">Tizim orqali (RawBT / kompyuter)</option>
      </select>
    </label>
  </div>
</header>

<div id="printArea" aria-hidden="true"></div>

<div id="confirmBar" hidden>
  <div class="cbq" id="cbText"></div>
  <div class="cbrow">
    <button class="main" id="cbYes">✅ Ha, chiqdi</button>
    <button class="ghost" id="cbNo">❌ Chiqmadi</button>
  </div>
</div>

<main>
  <div class="msg info" id="hint">
    Printerni yoqing, telefon Bluetooth'ini yoqing, so'ng <b>“Printerni ulash”</b>ni bosing.
  </div>
  <div id="list"></div>

  <details id="diagBox" hidden>
    <summary>Texnik ma'lumot (printer kanallari)</summary>
    <pre id="diag" style="font-size:11px;white-space:pre-wrap;line-height:1.5"></pre>
  </details>

  <details>
    <summary>Printer ulanmasa nima qilish kerak</summary>
    <p><b>Avval shuni sinang:</b> “Printerni ulash” → ro'yxatdan printeringizni tanlang → “Sinov cheki”.
       Chiqsa — tamom, boshqa hech narsa kerak emas.</p>
    <p><b>Printer ro'yxatda ko'rinmasa</b> (stol printerlarida ko'p uchraydi — ular eski turdagi
       Bluetooth ishlatadi, brauzer uni ko'rmaydi):</p>
    <ol>
      <li>Telefon sozlamasida printerni odatdagidek Bluetooth orqali ulang (juftlang).</li>
      <li>Play Market'dan <b>RawBT</b> ilovasini o'rnating va unda shu printerni tanlang.</li>
      <li>Shu sahifada yuqoridan <b>Usul → “Tizim orqali (RawBT)”</b> ni tanlang.</li>
      <li>Endi “Chiqarish” bosganingizda chop etish oynasi ochiladi — RawBT'ni tanlaysiz.</li>
    </ol>
    <p>Tizim rejimida har bir chek uchun bir marta tasdiqlash kerak bo'ladi.
       Bevosita rejimda esa cheklar o'zi chiqaveradi.</p>
    <p>iPhone'da bevosita ulanish umuman ishlamaydi — u yerda “Matnni nusxalash” orqali
       printer ilovasiga joylashtirasiz. Oshxonaga Android qo'ygan ma'qul.</p>
  </details>
<p style="text-align:center;font-size:11px;color:var(--dim);margin:18px 0 6px">
  Kod versiyasi: __VER__
</p>

</main>

<script>
(function(){
  var AUTH = new URLSearchParams(location.search);
  var url = function(p){ return p + (p.indexOf('?')>=0?'&':'?') + AUTH.toString(); };
  var $ = function(id){ return document.getElementById(id); };

  var dev = null, chr = null;      // Bluetooth qurilma va yozish kanali
  var printing = false;
  var seen = {};                   // ko'rsatilgan buyurtmalar
  var failed = {};                 // chop etilmaganlar

  function say(text, kind){
    var m = $('hint');
    m.className = 'msg ' + (kind || 'info');
    m.innerHTML = text;
  }
  // Telegram ichidagi brauzer Bluetooth'ga ruxsat bermaydi — tashqi Chrome kerak.
  function openInChrome(){
    var u = location.href;
    try{
      var tg = window.Telegram && window.Telegram.WebApp;
      if (tg && tg.openLink){ tg.openLink(u, { try_instant_view: false }); return; }
    }catch(e){}
    if (/Android/i.test(navigator.userAgent)){
      var bare = u.replace("https://", "").replace("http://", "");
      location.href = "intent://" + bare + "#Intent;scheme=https;package=com.android.chrome;end";
      return;
    }
    window.open(u, "_blank");
  }

  function copyLink(){
    var u = location.href;
    if (navigator.clipboard && navigator.clipboard.writeText){
      navigator.clipboard.writeText(u).then(function(){
        say("Havola nusxalandi. Chrome'ni oching va manzil qatoriga qo‘ying.", 'ok');
      }).catch(function(){ window.prompt("Havolani nusxalang:", u); });
    } else {
      window.prompt("Havolani nusxalang:", u);
    }
  }

  function sayNeedChrome(){
    var bcss = 'margin:8px 6px 0 0;padding:9px 13px;border-radius:9px';
    say('Bluetooth bu yerda ishlamaydi \u2014 sahifa Telegram ichidagi brauzerda ochilgan. ' +
        'Uni Chrome\u2019da ochsangiz printer ulanadi.<br>' +
        '<button type=button id=goChrome style="' + bcss + ';font-weight:700">' +
        'Chrome\u2019da ochish</button>' +
        '<button type=button id=cpLink style="' + bcss + '">' +
        'Havolani nusxalash</button>', 'err');
    var g = document.getElementById('goChrome');
    if (g) g.onclick = openInChrome;
    var c = document.getElementById('cpLink');
    if (c) c.onclick = copyLink;
  }

  function setState(txt, ok){
    $('state').textContent = txt;
    $('dot').classList.toggle('on', !!ok);
  }

  /* ---------- ovoz (fayl kerak emas, o'zi hosil qiladi) ---------- */
  var actx = null;
  function beep(){
    if (!$('snd').checked) return;
    try{
      actx = actx || new (window.AudioContext || window.webkitAudioContext)();
      if (actx.state === 'suspended') actx.resume();
      [0, 180].forEach(function(delay){
        var o = actx.createOscillator(), g = actx.createGain();
        o.type = 'sine'; o.frequency.value = 880;
        g.gain.setValueAtTime(0.0001, actx.currentTime + delay/1000);
        g.gain.exponentialRampToValueAtTime(0.35, actx.currentTime + delay/1000 + 0.02);
        g.gain.exponentialRampToValueAtTime(0.0001, actx.currentTime + delay/1000 + 0.16);
        o.connect(g); g.connect(actx.destination);
        o.start(actx.currentTime + delay/1000);
        o.stop(actx.currentTime + delay/1000 + 0.18);
      });
    }catch(e){}
  }

  /* ---------- Bluetooth printer ---------- */
  // Arzon termoprinterlarda uchraydigan xizmat raqamlari
  var SERVICES = [
    '000018f0-0000-1000-8000-00805f9b34fb',
    '0000ffe0-0000-1000-8000-00805f9b34fb',
    '0000ff00-0000-1000-8000-00805f9b34fb',
    '49535343-fe7d-4ae5-8fa9-9fafd205e455',
    'e7810a71-73ae-499d-8c15-faa9aef0c3f2'
  ];

  function btSupported(){ return !!(navigator.bluetooth && navigator.bluetooth.requestDevice); }

  var chrList = [];     // printerdagi barcha yozish kanallari
  var chrIndex = 0;

  function renderChannels(){
    var nom = (dev && dev.name) ? dev.name : 'nomsiz';
    var qism = chrList.length > 1 ? (' · kanal ' + (chrIndex + 1) + '/' + chrList.length) : '';
    setState('Printer ulandi: ' + nom + qism, true);
    var btn = $('btChan');
    if (btn) btn.hidden = chrList.length < 2;
    var box = $('diagBox');
    if (box){
      box.hidden = !chrList.length;
      var rows = chrList.map(function(x, i){
        return (i === chrIndex ? '▶ ' : '  ') + (i + 1) + ') ' + x.uuid +
               '\\n     xizmat: ' + x.svc +
               '\\n     yozish: ' + (x.wnr ? 'javobsiz ' : '') + (x.w ? 'javobli' : '');
      });
      $('diag').textContent = 'Qurilma: ' + nom + '\\nPaket: ' + CHUNK + ' bayt\\n\\n' + rows.join('\\n');
    }
  }

  async function nextChannel(){
    if (chrList.length < 2){
      say('Bu printerda boshqa kanal yo‘q.', 'err');
      return;
    }
    chrIndex = (chrIndex + 1) % chrList.length;
    chr = chrList[chrIndex].c;
    renderChannels();
    say('Kanal ' + (chrIndex + 1) + '/' + chrList.length +
        ' ga o‘tdik. Endi «Sinov cheki» ni bosing.', 'info');
  }

  async function connect(){
    if (!btSupported()){
      sayNeedChrome();
      return;
    }
    try{
      say('Printer tanlanmoqda...', 'info');
      dev = await navigator.bluetooth.requestDevice({
        filters: SERVICES.map(function(s){ return { services:[s] }; }),
        optionalServices: SERVICES
      });
      dev.addEventListener('gattserverdisconnected', function(){
        chr = null;
        setState('Printer uzildi', false);
        say("Printer uzildi. Qayta ulash uchun “Printerni ulash”ni bosing.", 'err');
      });
      var server = await dev.gatt.connect();
      chr = null;
      chrList = [];
      var svcs = await server.getPrimaryServices();
      for (var i=0; i<svcs.length; i++){
        var cs = await svcs[i].getCharacteristics();
        for (var j=0; j<cs.length; j++){
          var pr = cs[j].properties;
          if (pr.write || pr.writeWithoutResponse){
            chrList.push({ c: cs[j], svc: svcs[i].uuid, uuid: cs[j].uuid,
                           wnr: !!pr.writeWithoutResponse, w: !!pr.write });
          }
        }
      }
      if (!chrList.length) throw new Error('yozish kanali topilmadi');
      // ba'zi printerlarda bir nechta yozish kanali bo'ladi, faqat bittasi chop etadi
      chrIndex = 0;
      chr = chrList[0].c;
      renderChannels();
      say('✅ Printer ulandi. Avval «Sinov cheki» ni bosib ko‘ring.', 'ok');
      flushFailed();
    }catch(e){
      chr = null;
      setState('Printer ulanmagan', false);
      if (e && e.name === 'NotFoundError'){
        say('Printer tanlanmadi. Printer yoqiqmi va Bluetooth ochiqmi — tekshiring.', 'err');
      } else {
        say('Ulanmadi: ' + (e && e.message ? e.message : e) + ". Pastdagi “boshqa yo‘l”ni ko‘ring.", 'err');
      }
    }
  }

  /* ---------- logo: rasmni printer tushunadigan nuqtalarga aylantiramiz ---------- */
  var hasLogo = false;            // serverda logo bormi
  var logoCache = {};             // kenglik -> {bytes, url}

  // Bitta belgi 12 nuqta eni — shundan qog'ozning nuqtalardagi kengligi chiqadi.
  function paperCols(){ return parseInt($('w').value, 10) || 48; }
  function dots(){ return paperCols() * 12; }

  // Oddiy o'lcham: harflar mutanosib, bo'yiga cho'zilmaydi.
  // Kattaligi brauzerda CSS orqali (sz-n) o'rtacha qilib berilgan.
  function fsize(){ return 'n'; }
  function effWidth(){ return Math.max(16, paperCols()); }
  function sizeBytes(){
    var s = fsize();
    if (s === 'h') return new Uint8Array([0x1d, 0x21, 0x01]);   // bo'yi x2
    if (s === 'b') return new Uint8Array([0x1d, 0x21, 0x11]);   // bo'yi va eni x2
    return new Uint8Array([0x1d, 0x21, 0x00]);                  // oddiy
  }
  function logoOn(){ var c = $('logo'); return !!(c && c.checked && hasLogo); }

  function loadImage(src){
    return new Promise(function(res, rej){
      var im = new Image();
      im.onload = function(){ res(im); };
      im.onerror = function(){ rej(new Error('logo yuklanmadi')); };
      im.src = src;
    });
  }

  var footCache = {};             // pastki yozuv rasmi — kenglik bo'yicha

  async function buildLogo(width){
    return buildRaster('/static/logo.jpg', width, 520, logoCache, true);
  }

  // Pastki yozuv printerning o'z shriftida emas, rasm bo'lib chiqadi.
  async function buildFoot(width){
    return buildRaster('/static/chek_pastki.png', width, 140, footCache, false);
  }

  async function buildRaster(src, width, maxH, cache, preview){
    if (cache[width]) return cache[width];
    var im = await loadImage(url(src));
    var w = width;
    var h = Math.round(im.height * (w / im.width));
    if (h > maxH){ h = maxH; w = Math.round(im.width * (h / im.height)); }
    w = Math.floor(w / 8) * 8;
    if (w < 8) w = 8;
    if (h < 1) h = 1;

    var cv = document.createElement('canvas');
    cv.width = w; cv.height = h;
    var cx = cv.getContext('2d');
    cx.fillStyle = '#fff'; cx.fillRect(0, 0, w, h);
    cx.drawImage(im, 0, 0, w, h);

    var img = cx.getImageData(0, 0, w, h);
    var d = img.data;
    var g = new Float32Array(w * h);
    var sum = 0;
    for (var i = 0, p = 0; i < d.length; i += 4, p++){
      var a = d[i+3] / 255;
      var v = 0.299*d[i] + 0.587*d[i+1] + 0.114*d[i+2];
      v = v * a + 255 * (1 - a);                     // shaffof joy — oq qog'oz
      g[p] = v; sum += v;
    }
    // fon to'q bo'lsa (masalan oltin logo ko'k fonda) ag'daramiz, aks holda qop-qora dog' chiqadi
    if (sum / (w * h) < 128){
      for (var q = 0; q < g.length; q++) g[q] = 255 - g[q];
    }

    // kontrastni cho'zamiz: fon oppoq, logo qop-qora bo'lsin.
    // Busiz fon kulrang qolib, chekda kir dog'dek nuqtalar bosilib ketadi.
    var hist = new Uint32Array(256);
    for (var hq = 0; hq < g.length; hq++){
      var hv = Math.round(g[hq]);
      hist[hv < 0 ? 0 : (hv > 255 ? 255 : hv)]++;
    }
    var cut = Math.max(1, Math.floor(g.length * 0.02));   // chetdagi 2% shovqinni hisobga olmaymiz
    var lo = 0, hi2 = 255, acc = 0, z;
    for (z = 0; z < 256; z++){ acc += hist[z]; if (acc >= cut){ lo = z; break; } }
    acc = 0;
    for (z = 255; z >= 0; z--){ acc += hist[z]; if (acc >= cut){ hi2 = z; break; } }
    if (hi2 - lo > 10){
      var sc = 255 / (hi2 - lo);
      for (var sq = 0; sq < g.length; sq++){
        var vv = (g[sq] - lo) * sc;
        g[sq] = vv < 0 ? 0 : (vv > 255 ? 255 : vv);
      }
    }
    // JPEG shovqini fonda mayda nuqta qoldirmasin — deyarli oqni butunlay oq qilamiz
    var dark = 0;
    for (var wq = 0; wq < g.length; wq++){
      if (g[wq] > 215) g[wq] = 255;
      if (g[wq] < 128) dark++;
    }
    // surat ko'rinishidagi logo juda qora chiqsa, qog'oz qizib ketadi — biroz yoritamiz
    if (dark > g.length * 0.45){
      for (var yq = 0; yq < g.length; yq++){
        g[yq] = 255 * Math.pow(g[yq] / 255, 0.6);
      }
    }

    // Logomi yoki suratmi? Yassi grafikada piksellarning aksari deyarli oq yoki
    // deyarli qora bo'ladi. Shunga qarab usulni tanlaymiz.
    var flat = 0;
    for (var fq = 0; fq < g.length; fq++){
      if (g[fq] > 225 || g[fq] < 40) flat++;
    }
    var isLogo = flat > g.length * 0.62;

    // Yozuvli logoni keskinlashtiramiz — mayda harflar ezilib ketmasin.
    if (isLogo){
      var sh = new Float32Array(g.length);
      for (var sy = 0; sy < h; sy++){
        for (var sx = 0; sx < w; sx++){
          var si = sy * w + sx;
          var c0 = g[si];
          var up = sy > 0 ? g[si - w] : c0;
          var dn = sy + 1 < h ? g[si + w] : c0;
          var lf = sx > 0 ? g[si - 1] : c0;
          var rt = sx + 1 < w ? g[si + 1] : c0;
          var v2 = c0 * 1.8 - (up + dn + lf + rt) * 0.2;
          sh[si] = v2 < 0 ? 0 : (v2 > 255 ? 255 : v2);
        }
      }
      g = sh;
    }

    var bpr = w / 8;
    var bits = new Uint8Array(bpr * h);
    if (isLogo){
      // Keskin chegara: harf chetlari toza chiqadi, nuqtalar bulg'amaydi.
      for (var ty = 0; ty < h; ty++){
        for (var tx = 0; tx < w; tx++){
          if (g[ty * w + tx] < 172) bits[ty*bpr + (tx >> 3)] |= (0x80 >> (tx & 7));
        }
      }
    } else {
      // Surat: Floyd-Steinberg bilan kulrangni nuqtalarga taqsimlaymiz
      for (var y = 0; y < h; y++){
        for (var x = 0; x < w; x++){
          var idx = y * w + x;
          var old = g[idx];
          var nv = old < 128 ? 0 : 255;
          var err = old - nv;
          if (nv === 0) bits[y*bpr + (x >> 3)] |= (0x80 >> (x & 7));
          if (x + 1 < w) g[idx+1] += err * 7 / 16;
          if (y + 1 < h){
            if (x > 0) g[idx+w-1] += err * 3 / 16;
            g[idx+w] += err * 5 / 16;
            if (x + 1 < w) g[idx+w+1] += err * 1 / 16;
          }
        }
      }
    }

    // ko'rib turish uchun o'sha nuqtalarni qaytarib chizamiz
    for (var yy = 0; yy < h; yy++){
      for (var xx = 0; xx < w; xx++){
        var on = bits[yy*bpr + (xx >> 3)] & (0x80 >> (xx & 7));
        var o4 = (yy * w + xx) * 4;
        var c = on ? 0 : 255;
        d[o4] = c; d[o4+1] = c; d[o4+2] = c; d[o4+3] = 255;
      }
    }
    cx.putImageData(img, 0, 0);

    // GS v 0 — ESC/POS rastr buyrug'i.
    // Butun logoni bitta buyruq qilib yuborsak, Bluetooth kanali yetkazib
    // ulgurmaydi: printer o'rtada och qolib siltiydi va chiziqlar uzilib chiqadi.
    // Shuning uchun uni 24 qatorli bo'laklarga bo'lamiz — har bo'lak mustaqil
    // buyruq, printer uni to'liq olgandan keyingina bosadi.
    // Rasmning tepasi va pastidagi oq joyni kesamiz: logo faylida ko'rinmas
    // chekka bo'lsa, chekda bo'sh joy bo'lib bosiladi va qog'oz behuda ketadi.
    function rowDark(r){
      for (var q = 0; q < bpr; q++) if (bits[r * bpr + q]) return true;
      return false;
    }
    var y0 = 0, y1 = h - 1;
    while (y0 < h && !rowDark(y0)) y0++;
    while (y1 > y0 && !rowDark(y1)) y1--;
    if (y0 > y1){ y0 = 0; y1 = h - 1; }        // butunlay oq — tegmaymiz
    var MARGIN = 4;                            // ozgina nafas qolsin
    y0 = Math.max(0, y0 - MARGIN);
    y1 = Math.min(h - 1, y1 + MARGIN);

    var BAND = 64;
    var bands = [];
    for (var by = y0; by <= y1; by += BAND){
      var bh = Math.min(BAND, y1 - by + 1);
      var seg = bits.subarray(by * bpr, (by + bh) * bpr);
      var hd = new Uint8Array([0x1d, 0x76, 0x30, 0x00,
                               bpr & 0xff, (bpr >> 8) & 0xff,
                               bh & 0xff, (bh >> 8) & 0xff]);
      var one = new Uint8Array(hd.length + seg.length);
      one.set(hd, 0); one.set(seg, hd.length);
      bands.push(one);
    }

    cache[width] = { bands: bands, url: cv.toDataURL('image/png') };
    if (preview){
      var pv = $('logoPrev');
      if (pv){ pv.src = cache[width].url; pv.hidden = false; }
    }
    return cache[width];
  }

  function joinBytes(parts){
    var n = 0, i;
    for (i = 0; i < parts.length; i++) n += parts[i].length;
    var out = new Uint8Array(n), at = 0;
    for (i = 0; i < parts.length; i++){ out.set(parts[i], at); at += parts[i].length; }
    return out;
  }

  // Har bir bo'lak alohida yuboriladi, orasida printer nafas oladi.

  function baseSize(){
    var s = fsize();
    if (s === 'h') return 0x01;
    if (s === 'b') return 0x11;
    return 0x00;
  }

  // Qator uslubi: n oddiy, b qalin, d ikki barobar, db ikki barobar qalin
  function styleBytes(st){
    var size = (st === 'd' || st === 'db') ? 0x11 : baseSize();
    var bold = (st === 'b' || st === 'db') ? 0x01 : 0x00;
    return new Uint8Array([0x1d, 0x21, size, 0x1b, 0x45, bold]);
  }

  function centered(bands){
    var out = [new Uint8Array([0x1b, 0x61, 0x01])];
    for (var i = 0; i < bands.length; i++) out.push(bands[i]);
    out.push(new Uint8Array([0x0a, 0x1b, 0x61, 0x00]));
    return out;
  }

  // blocks — [{t:matn, s:uslub}]. Bir xil uslubdagi qatorlar bitta buyruqqa
  // yig'iladi: har qator uchun alohida yuborish printerni sekinlashtiradi.
  function escposBlocks(blocks, logo, foot){
    var enc = new TextEncoder();
    var segs = [new Uint8Array([0x1b,0x40, 0x1b,0x74,0x00])];   // reset + kodlash jadvali
    if (logo && logo.bands && logo.bands.length){
      segs = segs.concat(centered(logo.bands));
    }
    var buf = [], cur = null;
    function flush(){
      if (!buf.length) return;
      segs.push(styleBytes(cur));
      segs.push(enc.encode(buf.join("\\n") + "\\n"));
      buf = [];
    }
    for (var i = 0; i < blocks.length; i++){
      var bl = blocks[i] || {};
      var txt = bl.t == null ? '' : String(bl.t);
      if (bl.s === 'foot'){
        flush(); cur = null;
        if (foot && foot.bands && foot.bands.length){
          segs = segs.concat(centered(foot.bands));
        } else {                       // rasm yuklanmasa — oddiy matn bilan
          segs.push(styleBytes('n'));
          segs.push(enc.encode(txt + "\\n"));
        }
        continue;
      }
      var st = (bl.s === 'hr' || !bl.s) ? 'n' : bl.s;
      if (st !== cur){ flush(); cur = st; }
      buf.push(txt);
    }
    flush();
    segs.push(new Uint8Array([0x1b,0x45,0x00, 0x1d,0x21,0x00]));            // uslubni qaytaramiz
    segs.push(new Uint8Array([0x0a,0x0a,0x0a,0x0a, 0x1d,0x56,0x42,0x00]));  // bo'sh joy + kesish
    return segs;
  }

  // Eski chaqiriqlar uchun: oddiy matnni bitta blok qilib yuboramiz.
  function escpos(text, logo){
    return escposBlocks([{t: String(text == null ? '' : text), s: 'n'}], logo, null);
  }

  // Paket o'lchami. Kattasi tezroq, lekin ba'zi printerlar qabul qilmaydi.
  // Shuning uchun kattadan boshlaymiz va xatolik chiqsa o'zimiz pasayamiz.
  var CHUNK_STEPS = [182, 100, 60, 20];
  var chunkIx = 0;
  function baseIx(){
    var s = $('spd');
    var v = s ? parseInt(s.value, 10) : 0;
    return (v >= 0 && v < CHUNK_STEPS.length) ? v : 0;
  }
  function chunkSize(){ return CHUNK_STEPS[Math.max(chunkIx, baseIx())]; }
  function slower(){
    var cur = Math.max(chunkIx, baseIx());
    if (cur < CHUNK_STEPS.length - 1){ chunkIx = cur + 1; return true; }
    return false;
  }
  var CHUNK = 20;                      // eski nom — moslik uchun

  function wait(ms){ return new Promise(function(r){ setTimeout(r, ms); }); }

  async function writeOne(part){
    var cur = chrList[chrIndex] || {};
    if (cur.wnr && chr.writeValueWithoutResponse) return chr.writeValueWithoutResponse(part);
    if (chr.writeValue) return chr.writeValue(part);
    return chr.writeValueWithResponse(part);
  }

  // Bitta bo'lakni yuboramiz. Paket kattaligi qabul qilinmasa, pasayib qayta boshlaymiz.
  async function sendRaw(bytes){
    for (;;){
      var size = chunkSize();
      try{
        for (var i = 0; i < bytes.length; i += size){
          await writeOne(bytes.slice(i, i + size));
          // Kichik paketda nafas kerak, kattasida await o'zi tutib turadi.
          if (size <= 20) await wait(6);
        }
        return;
      }catch(e){
        if (!slower()) throw e;        // eng kichigida ham bo'lmadi — xatolikni ko'rsatamiz
        await wait(120);               // printer o'ziga kelsin va boshidan yuboramiz
      }
    }
  }

  // segs — bo'laklar ro'yxati (yoki bitta Uint8Array).
  // Rasm bo'laklari orasida kutmaymiz: pauza qog'ozda oq chiziq qoldiradi.
  async function sendBytes(segs){
    if (!chr) throw new Error('printer ulanmagan');
    if (!Array.isArray(segs)) segs = [segs];
    for (var s = 0; s < segs.length; s++) await sendRaw(segs[s]);
  }

  // Chop etish varaqini qog'ozga moslaymiz. Busiz brauzer A4 deb o'ylab,
  // uzun chekni ikkinchi varaqqa o'tkazib yuboradi.
  function applyPageSize(){
    var mm = Math.round(paperCols() * 1.5) + 6;     // 1 belgi ≈ 1.5 mm
    var st = document.getElementById('pageStyle');
    if (st) st.textContent = '@page{ size:' + mm + 'mm auto; margin:2mm; }';
  }

  function systemPrint(text, logo, blocks, foot){
    applyPageSize();
    // Chop etish oynasi ochiladi — RawBT, printer yoki kompyuterdagi printer tanlanadi.
    // Oyna yopilgunicha kutamiz, chunki brauzer chop etilgan-etilmaganini aytmaydi.
    var area = document.getElementById('printArea');
    area.className = 'sz-' + fsize();
    area.innerHTML = '';
    if (logo){
      var im = document.createElement('img');
      im.className = 'plogo';
      // Printer drayveri o'zi to'g'ri nuqtalaydi — asl surat aniqroq chiqadi.
      im.src = url('/static/logo.jpg');
      area.appendChild(im);
    }
    if (blocks && blocks.length){
      blocks.forEach(function(bl){
        var t = bl.t == null ? '' : String(bl.t);
        if (bl.s === 'foot'){
          var fi = document.createElement('img');
          fi.className = 'pfoot';
          fi.src = url('/static/chek_pastki.png');
          fi.alt = t;
          area.appendChild(fi);
          return;
        }
        var ln = document.createElement('pre');
        ln.className = 'bl-' + (bl.s || 'n');
        ln.textContent = t;
        area.appendChild(ln);
      });
    } else {
      var pre = document.createElement('pre');
      pre.textContent = text;
      area.appendChild(pre);
    }

    return new Promise(function(resolve){
      var done = false;
      function fin(){
        if (done) return;
        done = true;
        window.removeEventListener('afterprint', fin);
        clearTimeout(guard);
        setTimeout(resolve, 150);
      }
      window.addEventListener('afterprint', fin);
      var guard = setTimeout(fin, 60000);
      try{ window.print(); }catch(e){ fin(); }
    });
  }

  /* ---------- chek chiqdimi? ---------- */
  var confirmResolve = null;

  function askPrinted(no){
    if (confirmResolve){ var old = confirmResolve; confirmResolve = null; old(false); }
    return new Promise(function(resolve){
      confirmResolve = resolve;
      $('cbText').textContent = (no ? ('#' + no + ' cheki') : 'Sinov cheki') +
                                " qog'ozga chiqdimi?";
      $('confirmBar').hidden = false;
    });
  }

  function closeConfirm(val){
    $('confirmBar').hidden = true;
    var r = confirmResolve;
    confirmResolve = null;
    if (r) r(val);
  }
  $('cbYes').addEventListener('click', function(){ closeConfirm(true); });
  $('cbNo').addEventListener('click', function(){ closeConfirm(false); });

  function mode(){ return $('mode').value; }

  ['w','logo'].forEach(function(id){
    var el = document.getElementById(id);
    if (!el) return;
    el.addEventListener('change', function(){
      logoCache = {};                       // yangi kenglikka qayta tayyorlanadi
      seen = {};                            // cheklar yangi matn bilan qayta kelsin
      var list = document.getElementById('list');
      if (list) list.innerHTML = '';
      try{
        localStorage.setItem('miqot_logo', $('logo').checked ? '1' : '0');
        localStorage.setItem('miqot_w', $('w').value);
      }catch(e){}
      if (logoOn()) buildLogo(dots()).catch(function(){});
      poll();
    });
  });
  try{
    var savedLogo = localStorage.getItem('miqot_logo');
    if (savedLogo === '0') $('logo').checked = false;
    var savedW = localStorage.getItem('miqot_w');
    if (savedW && $('w')) $('w').value = savedW;
  }catch(e){}

  async function printText(text, no, blocks){
    var logo = null;
    if (logoOn()){
      try{
        logo = await buildLogo(dots());
      }catch(e){
        logo = null;
        say("Logo yuklanmadi — chek nom yozuvi bilan chiqadi.", 'info');
      }
    }
    // Pastki yozuv rasmi. Yuklanmasa chek baribir chiqadi — oddiy matn bo'lib.
    var foot = null;
    if (blocks && blocks.length){
      try{ foot = await buildFoot(dots()); }catch(e){ foot = null; }
    }
    if (mode() === 'sys'){
      // Brauzer chop etish muvaffaqiyatli bo'ldimi deb aytmaydi — shuning uchun o'zingizdan so'raymiz.
      await systemPrint(text, logo, blocks, foot);
      return await askPrinted(no);
    }
    if (!chr) throw new Error('printer ulanmagan');
    if (blocks && blocks.length) await sendBytes(escposBlocks(blocks, logo, foot));
    else await sendBytes(escpos(text, logo));
    return true;
  }

  /* ---------- buyurtmalar ---------- */
  async function markDone(ids){
    try{
      await fetch(url('/api/print/done'), {
        method:'POST', headers:{'Content-Type':'application/json'},
        body: JSON.stringify({ ids: ids })
      });
    }catch(e){}
  }

  async function printOrder(o, manual){
    if (printing && !manual) return false;
    printing = true;
    try{
      var ok = await printText(o.receipt, o.no, o.blocks);
      if (!ok){
        // chiqmadi — buyurtma ro'yxatda qoladi, yo'qolib ketmaydi
        failed[o.id] = o;
        say("⚠️ #" + o.no + " cheki chiqmadi. Buyurtma ro'yxatda qoldi — " +
            "printerni tekshirib, qaytadan «Chiqarish» bosing.", 'err');
        return false;
      }
      await markDone([o.id]);
      delete failed[o.id];
      var card = document.querySelector('[data-oid="' + o.id + '"]');
      if (card) card.remove();
      say('✅ #' + o.no + ' cheki chiqdi.', 'ok');
      return true;
    }catch(e){
      failed[o.id] = o;
      say('❌ #' + o.no + ' chiqmadi: ' + (e && e.message ? e.message : e), 'err');
      return false;
    }finally{
      printing = false;
      renderCount();
    }
  }

  async function flushFailed(){
    var list = Object.keys(failed).map(function(k){ return failed[k]; });
    for (var i=0; i<list.length; i++){ await printOrder(list[i], true); }
  }

  function card(o){
    var el = document.createElement('div');
    el.className = 'order';
    el.setAttribute('data-oid', o.id);

    var top = document.createElement('div');
    top.className = 'top';
    var no = document.createElement('span'); no.className='no'; no.textContent = '#' + o.no;
    var who = document.createElement('span'); who.className='who'; who.textContent = o.name || '';
    var sum = document.createElement('span'); sum.className='sum'; sum.textContent = (o.total||0) + ' SAR';
    top.appendChild(no); top.appendChild(who); top.appendChild(sum);
    el.appendChild(top);

    var ul = document.createElement('ul');
    (o.items||[]).forEach(function(t){ var li=document.createElement('li'); li.textContent=t; ul.appendChild(li); });
    el.appendChild(ul);

    var acts = document.createElement('div'); acts.className='acts';
    var bp = document.createElement('button'); bp.className='main'; bp.textContent='🖨 Chiqarish';
    bp.addEventListener('click', function(){ printOrder(o, true); });
    var bc = document.createElement('button'); bc.textContent='Matnni nusxalash';
    bc.addEventListener('click', function(){
      if (navigator.clipboard && navigator.clipboard.writeText){
        navigator.clipboard.writeText(o.receipt).then(function(){
          bc.textContent = '✅ Nusxalandi';
          setTimeout(function(){ bc.textContent = 'Matnni nusxalash'; }, 1800);
        }).catch(function(){ showPreview(el, o); });
      } else { showPreview(el, o); }
    });
    var bs = document.createElement('button'); bs.className='ghost'; bs.textContent='O‘tkazib yuborish';
    bs.addEventListener('click', function(){ markDone([o.id]); el.remove(); renderCount(); });
    acts.appendChild(bp); acts.appendChild(bc); acts.appendChild(bs);
    el.appendChild(acts);
    return el;
  }

  function showPreview(el, o){
    if (el.querySelector('pre.prev')) return;
    var pre = document.createElement('pre'); pre.className='prev'; pre.textContent = o.receipt;
    el.appendChild(pre);
  }

  function renderCount(){
    var n = document.querySelectorAll('.order').length;
    $('count').textContent = n ? (n + ' ta kutyapti') : '';
  }

  var offline = 0;
  async function poll(){
    try{
      var r = await fetch(url('/api/print/pending?w=' + effWidth() +
                              (logoOn() ? '&logo=1' : '')), { cache:'no-store' });
      if (!r.ok){
        setState(r.status === 403 ? 'Ruxsat yo‘q — botdan qaytadan oching' : 'Server javob bermadi', false);
        return;
      }
      offline = 0;
      var data = await r.json();
      var hadLogo = hasLogo;
      hasLogo = !!data.has_logo;
      if (hasLogo && !hadLogo){ buildLogo(dots()).catch(function(){}); }
      if (!hasLogo){
        var pv = $('logoPrev');
        if (pv) pv.hidden = true;
      }
      if (mode() === 'sys') setState('Tizim orqali: har chek uchun chop etish oynasi ochiladi', true);
      else if (!chr) setState('Printer ulanmagan — buyurtmalar ko‘rinib turadi', false);
      else setState('Printer ulandi: ' + (dev && dev.name ? dev.name : 'tayyor'), true);

      var list = $('list');
      var fresh = [];
      (data.orders || []).forEach(function(o){
        if (seen[o.id]) return;
        seen[o.id] = true;
        list.appendChild(card(o));
        fresh.push(o);
      });
      if (fresh.length){
        beep();
        renderCount();
        if ($('auto').checked && chr && mode() === 'bt'){
          (async function(){ for (var i=0;i<fresh.length;i++){ await printOrder(fresh[i], false); } })();
        }
      }
      if (!document.querySelectorAll('.order').length && !list.querySelector('.empty')){
        list.innerHTML = '<div class="empty">Hozircha yangi buyurtma yo‘q.<br>Kelganda o‘zi chiqadi.</div>';
        renderCount();
      } else if (document.querySelectorAll('.order').length){
        var e = list.querySelector('.empty'); if (e) e.remove();
      }
    }catch(e){
      offline++;
      if (offline > 1) setState('Internet aloqasi yo‘q', false);
    }
  }

  /* ---------- tugmalar ---------- */
  $('btConnect').addEventListener('click', connect);

  $('btChan').addEventListener('click', nextChannel);

  // Sinov cheki ataylab qisqa va LOGOSIZ — muammo matndami yoki logodami, shundan bilinadi.
  $('btTest').addEventListener('click', async function(){
    // O'lchagich chek: qog'ozga nechta belgi sig'ishini ko'z bilan tekshirish uchun.
    var w = effWidth();
    var ruler = '';
    for (var i = 1; i <= w; i++) ruler += String(i % 10);
    var t = ['SINOV ' + w, ruler, 'Yuqoridagi raqamlar', 'bitta qatorga sigsa -', 'qogoz togri tanlangan.', ''].join(String.fromCharCode(10));
    if (mode() === 'bt' && !chr){ say('Avval printerni ulang.', 'err'); return; }
    try{
      if (mode() === 'sys'){
        await systemPrint(t, null);
        var okk = await askPrinted(null);
        say(okk ? '\u2705 Chiqdi. Raqamlar bitta qatorga sigdimi?'
                : '\u274c Chiqmadi. Chop etish oynasida printerni tekshiring.',
            okk ? 'ok' : 'err');
        return;
      }
      await sendBytes(escpos(t, null));
      var ok = await askPrinted(null);
      if (ok){
        say('\u2705 Chiqdi. Agar raqamlar qatori qog\u2018ozdan chiqib ketgan bo\u2018lsa, ' +
            '\u00abQog\u2018oz\u00bb dan kichikroq o\u2018lcham tanlang.', 'ok');
      } else if (chrList.length > 1){
        say('Chiqmadi. \u00abBoshqa kanal\u00bb ni bosib, yana sinab ko\u2018ring \u2014 ' +
            'bu printerda ' + chrList.length + ' ta kanal bor.', 'err');
      } else {
        say('Chiqmadi. Printerda qog\u2018oz borligini tekshiring. Yordam bermasa, ' +
            '\u00abUsul\u00bb ni \u00abTizim orqali\u00bb ga o\u2018zgartiring.', 'err');
      }
    }
    catch(e){ say('\u274c Chiqmadi: ' + e.message, 'err'); }
  });

  $('btAgain').addEventListener('click', async function(){
    var no = window.prompt('Qaysi buyurtma? Kunlik raqamini yozing (masalan: 7)');
    if (!no) return;
    try{
      var r = await fetch(url('/api/print/again'), {
        method:'POST', headers:{'Content-Type':'application/json'},
        body: JSON.stringify({ no: parseInt(no, 10) })
      });
      var d = await r.json().catch(function(){ return {}; });
      if (r.ok){ say('#' + no + ' navbatga qo‘yildi.', 'ok'); }
      else { say(d.error || 'Topilmadi.', 'err'); }
    }catch(e){ say('Aloqa uzildi.', 'err'); }
  });

  $('mode').addEventListener('change', function(){
    var sys = mode() === 'sys';
    $('btConnect').disabled = sys;
    $('auto').disabled = sys;
    if (sys){
      $('auto').checked = false;
      say("Tizim rejimi: har bir chek uchun chop etish oynasi ochiladi \u2014 " +
          "telefonda <b>RawBT</b>ni, kompyuterda printeringizni tanlaysiz.<br>" +
          "Chop etgandan keyin pastdan <b>\u00abHa, chiqdi\u00bb</b> ni bosing, " +
          "shunda buyurtma ro\u2019yxatdan o\u2018chadi.", 'info');
    } else {
      $('auto').checked = true;
      if (!btSupported()) sayNeedChrome();
      else say("Bevosita rejim: printerni ulasangiz cheklar o‘zi chiqadi.", 'info');
    }
    poll();
  });

  $('w').addEventListener('change', function(){
    seen = {};                                   // yangi kenglikda qayta olamiz
    $('list').innerHTML = '';
    poll();
  });

  // ekran o'chib qolmasin
  if (navigator.wakeLock && navigator.wakeLock.request){
    var lock = null;
    var keep = async function(){
      try{ lock = await navigator.wakeLock.request('screen'); }catch(e){}
    };
    keep();
    document.addEventListener('visibilitychange', function(){
      if (document.visibilityState === 'visible') keep();
    });
  }

  if (!btSupported()) sayNeedChrome();

  poll();
  setInterval(poll, 5000);
})();
</script>
</body>
</html>"""

ADMIN_PAGE_HTML = """<!doctype html>
<html lang="uz">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1, maximum-scale=1">
<title>Menyuni boshqarish</title>
<script src="https://telegram.org/js/telegram-web-app.js"></script>
<style>
  :root { --bg:#ffffff; --fg:#111418; --muted:#6b7280; --line:#e5e7eb; --accent:#16a34a; --danger:#dc2626; --card:#f9fafb; }
  @media (prefers-color-scheme: dark) {
    :root { --bg:#14171a; --fg:#f3f4f6; --muted:#9ca3af; --line:#2b3138; --accent:#22c55e; --danger:#ef4444; --card:#1c2126; }
  }
  * { box-sizing:border-box; -webkit-tap-highlight-color:transparent; }
  body { margin:0; padding:16px 16px 48px; background:var(--bg); color:var(--fg);
         font-family:-apple-system,BlinkMacSystemFont,"Segoe UI",Roboto,sans-serif; font-size:16px; }
  h1 { font-size:20px; margin:0 0 4px; }
  h2 { font-size:16px; margin:0 0 12px; }
  .sub { color:var(--muted); font-size:13px; margin:0 0 18px; }
  .card { background:var(--card); border:1px solid var(--line); border-radius:14px; padding:14px; margin-bottom:18px; }
  label { display:block; font-size:13px; color:var(--muted); margin-bottom:10px; }
  input, select, textarea { width:100%; margin-top:5px; padding:11px 12px; font-size:16px; color:var(--fg);
    background:var(--bg); border:1px solid var(--line); border-radius:10px; font-family:inherit; }
  textarea { resize:vertical; }
  button { flex:1; padding:13px 14px; font-size:16px; font-weight:600; border:0; border-radius:10px;
    background:var(--accent); color:#fff; cursor:pointer; }
  button.ghost { background:transparent; color:var(--muted); border:1px solid var(--line); }
  button.small { flex:none; padding:8px 12px; font-size:14px; font-weight:500; }
  button.danger { background:var(--danger); }
  .row { display:flex; gap:10px; margin-top:6px; }
  #preview { width:100%; max-height:190px; object-fit:cover; border-radius:10px; margin-bottom:12px; }
  .msg { font-size:14px; margin:12px 0 0; min-height:20px; }
  label.chk { display:flex; align-items:center; gap:9px; font-size:15px; color:var(--fg); margin:-4px 0 14px; }
  label.chk input { width:20px; height:20px; margin:0; flex:none; accent-color:var(--accent); }
  .msg.ok { color:var(--accent); } .msg.err { color:var(--danger); }
  .cat { font-size:13px; color:var(--muted); text-transform:uppercase; letter-spacing:.04em; margin:20px 0 8px; }
  .dish { display:flex; gap:12px; align-items:center; background:var(--card); border:1px solid var(--line);
    border-radius:12px; padding:10px; margin-bottom:10px; }
  .dish img, .dish .noimg { width:58px; height:58px; border-radius:9px; object-fit:cover; flex:none;
    background:var(--line); display:flex; align-items:center; justify-content:center; font-size:22px; }
  .dish .info { flex:1; min-width:0; }
  .dish .nm { font-weight:600; font-size:15px; }
  .dish .meta { font-size:13px; color:var(--muted); margin-top:2px; }
  .out { color:var(--danger); }
  .acts { display:flex; gap:8px; margin-top:8px; }
  .empty { color:var(--muted); text-align:center; padding:26px 0; }
  .card.sale { border-color:var(--accent); }
  .card.sale.on { background:linear-gradient(135deg, rgba(22,163,74,0.12), transparent); }
  .saleNote { font-size:13px; color:var(--muted); margin:0 0 14px; line-height:1.5; }
  .saleRow { display:flex; gap:12px; align-items:flex-end; }
  .pctWrap { flex:1; margin:0; }
  .pctBox { display:flex; align-items:center; gap:6px; }
  .pctBox input { margin-top:5px; }
  .pctBox span { font-size:17px; color:var(--muted); padding-top:5px; }
  .saleBtn { flex:none; min-width:116px; padding:11px 14px; }
  .saleBtn.off { background:var(--accent); }
  .saleBtn.on { background:var(--danger); }
  .saleState { font-size:14px; font-weight:600; margin:13px 0 0; }
  .saleState.on { color:var(--accent); }
  .saleState.off { color:var(--muted); }
  .dish .sale-tag { display:inline-block; margin-top:3px; font-size:12px; font-weight:700; color:var(--accent); }
  .card.quiz.on { background:linear-gradient(135deg, rgba(22,163,74,0.1), transparent); border-color:var(--accent); }
  .qcount { font-size:13px; color:var(--muted); margin:-4px 0 14px; }
  .qcount.bad { color:var(--danger); }
  #quizResults { margin-top:14px; }
  #quizResults .qrow {
    display:flex; gap:10px; align-items:baseline; padding:7px 0;
    border-bottom:1px solid var(--line); font-size:14px;
  }
  #quizResults .qrow:last-child { border-bottom:none; }
  #quizResults .qp { font-weight:700; min-width:26px; color:var(--accent); }
  #quizResults .qn { flex:1; min-width:0; overflow:hidden; text-overflow:ellipsis; white-space:nowrap; }
  #quizResults .qs { font-variant-numeric:tabular-nums; color:var(--muted); font-size:13px; white-space:nowrap; }
  .card.hours.shut { border-color:var(--danger); background:linear-gradient(135deg, rgba(220,38,38,0.1), transparent); }
  .timeRow { display:flex; gap:12px; margin:4px 0 16px; }
  .timeRow label { flex:1; margin:0; }
  .timeRow.off { opacity:0.42; pointer-events:none; }
  .card.hours .saleBtn { width:100%; }

  /* set tarkibi */
  .setbox {
    margin:14px 0 4px; padding:13px; border-radius:12px;
    background:rgba(201,143,46,0.08); border:1px solid rgba(201,143,46,0.32);
  }
  .setbox .sb-t { font-size:13.5px; font-weight:700; color:#c98f2e; margin-bottom:3px; }
  .setbox .sb-s { font-size:12px; color:var(--muted); margin-bottom:11px; line-height:1.5; }
  .setbox .sb-s b { color:#c98f2e; }
  .sb-chips { display:flex; flex-wrap:wrap; gap:8px; margin-bottom:10px; }
  .sb-chip {
    display:flex; align-items:center; gap:6px; padding:8px 12px; border-radius:999px;
    background:var(--bg); border:1px solid var(--line); font-size:13px; font-weight:600;
    color:var(--fg); cursor:pointer; user-select:none;
  }
  .sb-chip .bx {
    width:16px; height:16px; border-radius:4px; border:1.5px solid var(--muted);
    flex:none; display:flex; align-items:center; justify-content:center;
  }
  .sb-chip.on { background:rgba(201,143,46,0.18); border-color:#c98f2e; }
  .sb-chip.on .bx { background:#c98f2e; border-color:#c98f2e; }
  .sb-chip.on .bx::after { content:'✓'; font-size:11px; color:#fff; font-weight:900; line-height:1; }
  .setbox input { margin:0; }
  .dish .set-tag { font-size:12px; color:#c98f2e; font-weight:600; margin-top:3px; }
</style>
</head>
<body>
<h1>🧑‍🍳 Menyuni boshqarish</h1>
<p class="sub">Taomni rasmi bilan shu yerdan qo'shing — Telegram'ga qaytish shart emas.</p>

<section class="card quiz" id="quizCard">
  <h2>🎁 Viktorina</h2>
  <p class="saleNote">Savollarni shu yerga yozasiz. Har bir savol alohida blok, bloklar orasida bo'sh qator.
     Birinchi qator — savol, keyingilari — variantlar. To'g'ri javob oldiga <b>*</b> qo'ying.</p>

  <label>Nomi<input id="q_title" placeholder="Miqot Food viktorinasi"></label>
  <label>Sovg'a (mijozlarga ko'rinadi)<input id="q_prize" placeholder="G'olibga bepul tushlik"></label>
  <label>Savollar
    <textarea id="q_text" rows="11" placeholder="Miqot Food qaysi shaharda joylashgan?&#10;*Makka&#10;Madina&#10;Jidda&#10;&#10;Osh qaysi go'shtdan tayyorlanadi?&#10;*Mol&#10;Baliq&#10;Tovuq"></textarea>
  </label>
  <p class="qcount" id="q_count">Savollar: 0 ta</p>

  <label class="chk"><input type="checkbox" id="q_test" checked> 🧪 Sinov rejimi — faqat men ko'raman</label>
  <p class="qcount" id="q_testnote">Sinab bo'lgach belgini olib tashlang — shundan keyin mijozlarga ko'rinadi.</p>

  <div class="saleRow">
    <button id="quizSave" class="saleBtn off" style="flex:1">Saqlash</button>
    <button id="quizToggle" class="saleBtn off" style="flex:1">Boshlash</button>
  </div>
  <p class="saleState" id="quizState">Hozir: to'xtatilgan</p>
  <div class="saleRow" style="margin-top:10px">
    <button id="quizBoard" class="small ghost" style="flex:1">Natijalarni ko'rish</button>
    <button id="quizReset" class="small danger" style="flex:1">Natijalarni tozalash</button>
  </div>
  <div id="quizResults"></div>
</section>

<section class="card hours" id="hoursCard">
  <h2>🕒 Ish vaqti</h2>
  <p class="saleNote">Yopiq paytda mijozlarga "ish vaqtimiz tugadi" xabari chiqadi va buyurtma qabul qilinmaydi. Siz admin sifatida baribir buyurtma bera olasiz.</p>

  <label class="chk"><input type="checkbox" id="h_closed"> Bugun yopiq (dam olish kuni)</label>

  <label class="chk"><input type="checkbox" id="h_sched"> Kunlik jadval bo'yicha ishlash</label>
  <div class="timeRow" id="timeRow">
    <label>Ochilish<input id="h_open" type="time" value="06:00"></label>
    <label>Yopilish<input id="h_close" type="time" value="22:00"></label>
  </div>

  <button id="hoursSave" class="saleBtn off">Saqlash</button>
  <p class="saleState" id="hoursState">Hozir: ochiq</p>
</section>

<section class="card sale" id="saleCard">
  <h2>🏷 Juma aksiyasi</h2>
  <p class="saleNote">Yoqsangiz barcha taom narxi shu foizga tushadi. O'chirsangiz — darhol odatiy narxga qaytadi.</p>
  <div class="saleRow">
    <label class="pctWrap">Chegirma foizi
      <div class="pctBox"><input id="s_percent" type="number" min="1" max="90" inputmode="numeric" value="17"><span>%</span></div>
    </label>
    <button id="saleToggle" class="saleBtn off">Yoqish</button>
  </div>
  <p class="saleState" id="saleState">Hozir: o'chiq</p>
</section>

<section class="card">
  <h2 id="formTitle">➕ Yangi taom</h2>
  <img id="preview" hidden alt="">
  <label>Nomi<input id="f_name" placeholder="Masalan: Lavash"></label>
  <label>Narxi (SAR)<input id="f_price" type="number" step="0.5" inputmode="decimal" placeholder="25"></label>
  <label>Tavsif<textarea id="f_desc" rows="2" placeholder="Qisqacha izoh (majburiy emas)"></textarea></label>
  <label>Kategoriya<select id="f_cat"></select></label>
  <label>Zaxira — bugun nechta bor (0 = tugadi)<input id="f_stock" type="number" value="0" inputmode="numeric"></label>
  <label class="chk"><input type="checkbox" id="f_unlimited"> Cheksiz — zaxira hisoblanmasin</label>

  <div class="setbox">
    <div class="sb-t">🍽 Set tarkibi</div>
    <div class="sb-s">Shu narxga yana nima qo'shib beriladi? Hech narsa belgilanmasa, taom oddiy
      ko'rinadi. Belgilansa, menyuda oltin <b>SET</b> nishoni chiqadi.</div>
    <div class="sb-chips" id="f_setchips"></div>
    <input id="f_setextra" placeholder="Boshqa — masalan: ko'kat (ixtiyoriy)">
  </div>

  <label>Rasm<input id="f_photo" type="file" accept="image/*"></label>
  <div class="row">
    <button id="saveBtn">Saqlash</button>
    <button id="cancelBtn" class="ghost" hidden>Bekor qilish</button>
  </div>
  <p class="msg" id="msg"></p>
</section>

<section id="list"><p class="empty">Yuklanmoqda…</p></section>

<script>
const tg = window.Telegram && window.Telegram.WebApp;
if (tg) { tg.ready(); tg.expand(); }
const AUTH = new URLSearchParams(location.search);
const CATS = __CATEGORIES__;
const EMOJI = __EMOJI__;
let setCatalog = [];
let chosenSet = [];
let editingId = null;

const $ = (id) => document.getElementById(id);
const url = (p) => p + (p.includes('?') ? '&' : '?') + AUTH.toString();

CATS.forEach(c => { const o = document.createElement('option'); o.value = c; o.textContent = (EMOJI[c]||'') + ' ' + c; $('f_cat').appendChild(o); });

function say(text, kind) { const m = $('msg'); m.textContent = text; m.className = 'msg ' + (kind||''); }

$('f_photo').addEventListener('change', e => {
  const f = e.target.files[0];
  if (!f) { $('preview').hidden = true; return; }
  $('preview').src = URL.createObjectURL(f); $('preview').hidden = false;
});

$('f_unlimited').addEventListener('change', e => {
  $('f_stock').disabled = e.target.checked;
  if (e.target.checked) $('f_stock').value = '';
});

function renderSetChips() {
  const box = $('f_setchips');
  if (!box) return;
  box.innerHTML = '';
  setCatalog.forEach(function (it) {
    const el = document.createElement('div');
    el.className = 'sb-chip' + (chosenSet.indexOf(it.key) >= 0 ? ' on' : '');
    const bx = document.createElement('span');
    bx.className = 'bx';
    el.appendChild(bx);
    const nom = (it.names && it.names.uz) || it.key;
    el.appendChild(document.createTextNode(it.emoji + ' ' + nom));
    el.addEventListener('click', function () {
      const i = chosenSet.indexOf(it.key);
      if (i >= 0) chosenSet.splice(i, 1); else chosenSet.push(it.key);
      renderSetChips();
      if (tg && tg.HapticFeedback) tg.HapticFeedback.impactOccurred('light');
    });
    box.appendChild(el);
  });
}

function setTagText(d) {
  const out = [];
  (d.set || []).forEach(function (k) {
    const f = setCatalog.filter(function (x) { return x.key === k; })[0];
    if (f) out.push(f.emoji + ' ' + ((f.names && f.names.uz) || k));
  });
  String(d.set_extra || '').split(',').forEach(function (p) {
    p = p.trim();
    if (p) out.push(p);
  });
  return out.length ? 'SET: ' + out.join(' · ') : '';
}

function resetForm() {
  editingId = null;
  $('formTitle').textContent = '➕ Yangi taom';
  $('f_name').value = ''; $('f_price').value = ''; $('f_desc').value = '';
  $('f_stock').value = '0'; $('f_photo').value = ''; $('f_cat').selectedIndex = 0;
  $('f_unlimited').checked = false; $('f_stock').disabled = false;
  chosenSet = []; $('f_setextra').value = ''; renderSetChips();
  $('preview').hidden = true; $('cancelBtn').hidden = true; say('');
}
$('cancelBtn').addEventListener('click', resetForm);

/* ---------- viktorina ---------- */
var quiz = { active:false, test:true, title:'', prize:'', text:'', count:0 };

function countQ(text){
  var blocks = (text || '').trim().split(/\\n\\s*\\n/).filter(function(b){ return b.trim(); });
  var good = 0, bad = 0;
  blocks.forEach(function(b){
    var lines = b.split('\\n').map(function(x){ return x.trim(); }).filter(Boolean);
    var stars = lines.slice(1).filter(function(x){ return x.charAt(0) === '*'; }).length;
    if (lines.length >= 3 && stars === 1) good++; else bad++;
  });
  return { good: good, bad: bad };
}

function renderQuizCount(){
  var c = countQ($('q_text').value);
  var el = $('q_count');
  el.textContent = 'Savollar: ' + c.good + ' ta' + (c.bad ? '  ·  ' + c.bad + ' ta blok noto\u2018g\u2018ri' : '');
  el.className = 'qcount' + (c.bad ? ' bad' : '');
}

function renderQuiz(){
  $('q_title').value = quiz.title || '';
  $('q_prize').value = quiz.prize || '';
  $('q_test').checked = quiz.test !== false;
  if (document.activeElement !== $('q_text')) $('q_text').value = quiz.text || '';
  renderQuizCount();
  var btn = $('quizToggle'), st = $('quizState'), card = $('quizCard');
  if (quiz.active){
    btn.textContent = "To\u2018xtatish"; btn.className = 'saleBtn on';
    if (quiz.test){
      st.textContent = '🧪 Sinov rejimi — faqat siz ko\u2018rasiz (' + quiz.count + ' ta savol)';
      st.className = 'saleState'; st.style.color = 'var(--warn, #f59e0b)';
    } else {
      st.textContent = '🟢 Hamma uchun ochiq — ' + quiz.count + ' ta savol';
      st.className = 'saleState on'; st.style.color = '';
    }
    card.classList.add('on');
  } else {
    btn.textContent = 'Boshlash'; btn.className = 'saleBtn off';
    st.textContent = "⏹ Hozir: to\u2018xtatilgan";
    st.className = 'saleState off'; st.style.color = '';
    card.classList.remove('on');
  }
}

$('q_text').addEventListener('input', renderQuizCount);

async function saveQuiz(active){
  var c = countQ($('q_text').value);
  if (active && c.good === 0){ say('Avval kamida bitta savol yozing.', 'err'); return; }
  if (active && c.bad){ say(c.bad + " ta blok noto\u2018g\u2018ri — har savolda bitta * belgilangan to\u2018g\u2018ri javob bo\u2018lsin.", 'err'); return; }
  $('quizSave').disabled = true; $('quizToggle').disabled = true;
  try {
    var r = await fetch(url('/api/admin/quiz'), {
      method:'POST', headers:{'Content-Type':'application/json'},
      body: JSON.stringify({ title: $('q_title').value, prize: $('q_prize').value,
                             text: $('q_text').value, active: active,
                             test: $('q_test').checked })
    });
    var d = await r.json().catch(function(){ return {}; });
    if (r.ok){
      quiz = d.quiz || quiz;
      renderQuiz();
      var m = '✅ Saqlandi.';
      if (active === true) m = quiz.test ? '🧪 Sinov rejimida boshlandi — faqat siz ko\u2018rasiz.'
                                         : '🟢 Viktorina hamma uchun ochildi!';
      if (active === false) m = "⏹ Viktorina to\u2018xtatildi.";
      say(m, 'ok');
      if (tg && tg.HapticFeedback) tg.HapticFeedback.notificationOccurred('success');
    } else { say(d.error || "Saqlab bo\u2018lmadi.", 'err'); }
  } catch(e){ say("Aloqa uzildi.", 'err'); }
  $('quizSave').disabled = false; $('quizToggle').disabled = false;
}

$('quizSave').addEventListener('click', function(){ saveQuiz(null); });
$('quizToggle').addEventListener('click', function(){ saveQuiz(!quiz.active); });

$('quizBoard').addEventListener('click', async function(){
  var box = $('quizResults');
  box.innerHTML = '';
  try {
    var r = await fetch(url('/api/admin/quiz/results'));
    var d = await r.json();
    var rows = d.board || [];
    if (!rows.length){
      var p = document.createElement('p');
      p.className = 'qcount'; p.textContent = 'Hali hech kim tugatmagan.';
      box.appendChild(p); return;
    }
    rows.forEach(function(x, i){
      var row = document.createElement('div'); row.className = 'qrow';
      var a = document.createElement('span'); a.className = 'qp'; a.textContent = (i+1) + '.';
      var b = document.createElement('span'); b.className = 'qn';
      b.textContent = x.name + (x.username ? ' (@' + x.username + ')' : '');
      var c = document.createElement('span'); c.className = 'qs';
      c.textContent = x.correct + '/' + (d.total || 0) + ' · ' + x.time;
      row.appendChild(a); row.appendChild(b); row.appendChild(c);
      box.appendChild(row);
    });
  } catch(e){ say('Natijalarni olib bo\u2018lmadi.', 'err'); }
});

$('quizReset').addEventListener('click', async function(){
  if (!confirm("Barcha natijalar o\u2018chadi va hamma qaytadan qatnasha oladi. Davom etamizmi?")) return;
  try {
    var r = await fetch(url('/api/admin/quiz/results'), { method:'DELETE' });
    if (r.ok){ $('quizResults').innerHTML = ''; say('✅ Natijalar tozalandi.', 'ok'); }
    else { say("Tozalab bo\u2018lmadi.", 'err'); }
  } catch(e){ say('Aloqa uzildi.', 'err'); }
});

/* ---------- ish vaqti ---------- */
let hours = { closed_today:false, schedule_on:false, open:'06:00', close:'22:00' };
let shopOpen = true;

function renderHours() {
  $('h_closed').checked = !!hours.closed_today;
  $('h_sched').checked = !!hours.schedule_on;
  $('h_open').value = hours.open || '06:00';
  $('h_close').value = hours.close || '22:00';
  $('timeRow').className = 'timeRow' + (hours.schedule_on ? '' : ' off');

  const st = $('hoursState');
  const card = $('hoursCard');
  if (!shopOpen) {
    st.textContent = hours.closed_today
      ? '🔴 Hozir: YOPIQ (bugun dam olish kuni)'
      : '🔴 Hozir: YOPIQ (ish vaqtidan tashqari)';
    st.className = 'saleState off';
    card.classList.add('shut');
  } else {
    st.textContent = hours.schedule_on
      ? '🟢 Hozir: ochiq — jadval ' + hours.open + ' – ' + hours.close
      : '🟢 Hozir: ochiq — kecha-kunduz';
    st.className = 'saleState on';
    card.classList.remove('shut');
  }
}

$('h_sched').addEventListener('change', (e)=>{
  $('timeRow').className = 'timeRow' + (e.target.checked ? '' : ' off');
});

async function saveHours() {
  $('hoursSave').disabled = true;
  try {
    const r = await fetch(url('/api/admin/hours'), {
      method:'POST', headers:{'Content-Type':'application/json'},
      body: JSON.stringify({
        closed_today: $('h_closed').checked,
        schedule_on: $('h_sched').checked,
        open: $('h_open').value,
        close: $('h_close').value
      })
    });
    const data = await r.json().catch(()=>({}));
    if (r.ok) {
      hours = data.hours || hours;
      shopOpen = data.shop ? data.shop.open : true;
      renderHours();
      say(shopOpen ? '✅ Saqlandi — hozir buyurtma qabul qilinyapti.'
                   : '✅ Saqlandi — hozir buyurtma qabul qilinmaydi.', 'ok');
      if (tg && tg.HapticFeedback) tg.HapticFeedback.notificationOccurred('success');
    } else { say(data.error || 'Saqlab bo‘lmadi.', 'err'); }
  } catch (e) { say('Aloqa uzildi. Qaytadan urinib ko‘ring.', 'err'); }
  $('hoursSave').disabled = false;
}
$('hoursSave').addEventListener('click', saveHours);

/* ---------- aksiya ---------- */
let sale = { active:false, percent:17 };

function renderSale() {
  $('s_percent').value = sale.percent || 17;
  const btn = $('saleToggle');
  const st = $('saleState');
  const card = $('saleCard');
  if (sale.active) {
    btn.textContent = "O'chirish";
    btn.className = 'saleBtn on';
    st.textContent = 'Hozir: YONIQ — barcha narx −' + sale.percent + '%';
    st.className = 'saleState on';
    card.classList.add('on');
  } else {
    btn.textContent = 'Yoqish';
    btn.className = 'saleBtn off';
    st.textContent = "Hozir: o'chiq — odatiy narxlar";
    st.className = 'saleState off';
    card.classList.remove('on');
  }
}

async function saveSale(active) {
  let pct = parseInt($('s_percent').value, 10);
  if (isNaN(pct) || pct < 1 || pct > 90) {
    if (active) { say('Chegirma foizi 1 dan 90 gacha bo‘lsin.', 'err'); return; }
    pct = sale.percent || 17;
  }
  $('saleToggle').disabled = true;
  try {
    const r = await fetch(url('/api/admin/discount'), {
      method:'POST', headers:{'Content-Type':'application/json'},
      body: JSON.stringify({ active: active, percent: pct })
    });
    const data = await r.json().catch(()=>({}));
    if (r.ok) {
      sale = data.discount || sale;
      renderSale();
      say(active ? ('✅ Aksiya yoqildi — barcha narx −' + sale.percent + '%') : '✅ Aksiya o‘chirildi, narxlar odatiyga qaytdi.', 'ok');
      if (tg && tg.HapticFeedback) tg.HapticFeedback.notificationOccurred('success');
      load();
    } else {
      say(data.error || 'Saqlab bo‘lmadi.', 'err');
    }
  } catch (e) { say('Aloqa uzildi. Qaytadan urinib ko‘ring.', 'err'); }
  $('saleToggle').disabled = false;
}

$('saleToggle').addEventListener('click', ()=> saveSale(!sale.active));

async function load() {
  try {
    const rq = await fetch(url('/api/admin/quiz'));
    if (rq.ok) { quiz = (await rq.json()).quiz || quiz; }
  } catch (e) {}
  renderQuiz();
  try {
    const rh = await fetch(url('/api/admin/hours'));
    if (rh.ok) { const d = await rh.json(); hours = d.hours || hours; shopOpen = d.shop ? d.shop.open : true; }
  } catch (e) {}
  renderHours();
  try {
    const rs = await fetch(url('/api/admin/discount'));
    if (rs.ok) { sale = (await rs.json()).discount || sale; }
  } catch (e) {}
  renderSale();
  try {
    const r = await fetch(url('/api/admin/dishes'));
    if (!r.ok) {
      $('list').innerHTML = '';
      const p = document.createElement('p');
      p.className = 'empty';
      p.textContent = "Ruxsat yo'q yoki sessiya eskirgan. Telegram'da /start bosib, tugmani qaytadan oching.";
      $('list').appendChild(p);
      return;
    }
    const dd = await r.json();
    setCatalog = dd.set_catalog || [];
    renderSetChips();
    render(dd.dishes || []);
  } catch (e) {
    $('list').innerHTML = '';
    const p = document.createElement('p');
    p.className = 'empty';
    p.textContent = "Aloqa uzildi. Qaytadan urinib ko'ring.";
    $('list').appendChild(p);
  }
}

function render(dishes) {
  const box = $('list');
  box.innerHTML = '';
  window.__dishes = dishes;
  if (!dishes.length) {
    const p = document.createElement('p');
    p.className = 'empty'; p.textContent = "Menyu hozircha bo'sh.";
    box.appendChild(p);
    return;
  }
  CATS.forEach(cat => {
    const items = dishes.filter(d => d.category === cat);
    if (!items.length) return;
    const head = document.createElement('p');
    head.className = 'cat';
    head.textContent = (EMOJI[cat] || '') + ' ' + cat;
    box.appendChild(head);
    items.forEach(d => box.appendChild(dishRow(d)));
  });
}

function dishRow(d) {
  const row = document.createElement('div');
  row.className = 'dish';

  if (d.photo_url) {
    const img = document.createElement('img');
    img.src = d.photo_url; img.alt = '';
    row.appendChild(img);
  } else {
    const ph = document.createElement('div');
    ph.className = 'noimg'; ph.textContent = '🍽';
    row.appendChild(ph);
  }

  const info = document.createElement('div');
  info.className = 'info';

  const nm = document.createElement('div');
  nm.className = 'nm'; nm.textContent = d.name;
  info.appendChild(nm);

  const meta = document.createElement('div');
  meta.className = 'meta';
  meta.textContent = d.price + ' SAR · ';
  const st = document.createElement('span');
  if (d.stock === null) { st.textContent = 'cheklanmagan'; }
  else if (d.stock <= 0) { st.textContent = 'tugadi'; st.className = 'out'; }
  else { st.textContent = d.stock + ' dona'; }
  meta.appendChild(st);
  info.appendChild(meta);

  const stag = setTagText(d);
  if (stag) {
    const sl = document.createElement('div');
    sl.className = 'set-tag';
    sl.textContent = stag;
    info.appendChild(sl);
  }

  if (sale.active) {
    const tag = document.createElement('div');
    tag.className = 'sale-tag';
    tag.textContent = '🏷 Aksiyada: ' + Math.round(d.price * (100 - sale.percent) / 100) + ' SAR';
    info.appendChild(tag);
  }

  const acts = document.createElement('div');
  acts.className = 'acts';

  const edit = document.createElement('button');
  edit.className = 'small ghost'; edit.textContent = 'Tahrirlash';
  edit.addEventListener('click', () => startEdit(d.id));
  acts.appendChild(edit);

  const rm = document.createElement('button');
  rm.className = 'small danger'; rm.textContent = "O'chirish";
  rm.addEventListener('click', () => del(d.id, d.name));
  acts.appendChild(rm);

  info.appendChild(acts);
  row.appendChild(info);
  return row;
}

function startEdit(id) {
  const d = (window.__dishes||[]).find(x => x.id === id);
  if (!d) return;
  editingId = id;
  $('formTitle').textContent = '✏️ Tahrirlash: ' + d.name;
  $('f_name').value = d.name; $('f_price').value = d.price; $('f_desc').value = d.desc || '';
  $('f_stock').value = d.stock === null ? '' : d.stock;
  $('f_unlimited').checked = d.stock === null;
  $('f_stock').disabled = d.stock === null;
  $('f_cat').value = d.category; $('f_photo').value = '';
  chosenSet = (d.set || []).slice();
  $('f_setextra').value = d.set_extra || '';
  renderSetChips();
  if (d.photo_url) { $('preview').src = d.photo_url; $('preview').hidden = false; } else { $('preview').hidden = true; }
  $('cancelBtn').hidden = false;
  window.scrollTo({top:0, behavior:'smooth'});
  say("Rasmni o'zgartirmoqchi bo'lsangiz yangisini tanlang, aks holda eskisi qoladi.");
}

async function del(id, name) {
  if (!confirm('«' + name + "» o'chirilsinmi?")) return;
  const r = await fetch(url('/api/admin/dish/' + id + '/delete'), { method: 'POST' });
  if (r.ok) { say("O'chirildi.", 'ok'); resetForm(); load(); } else { say("O'chirib bo'lmadi.", 'err'); }
}

$('saveBtn').addEventListener('click', async () => {
  const name = $('f_name').value.trim();
  const price = $('f_price').value.trim();
  if (!name) { say('Taom nomini yozing.', 'err'); return; }
  if (price === '' || isNaN(price)) { say('Narxni raqam bilan yozing.', 'err'); return; }
  const fd = new FormData();
  fd.append('name', name);
  fd.append('price', price);
  fd.append('desc', $('f_desc').value.trim());
  fd.append('category', $('f_cat').value);
  fd.append('stock', $('f_unlimited').checked ? '-1' : ($('f_stock').value.trim() || '0'));
  fd.append('set', chosenSet.join(','));
  fd.append('set_extra', $('f_setextra').value.trim());
  const file = $('f_photo').files[0];
  if (file) fd.append('photo', file);
  $('saveBtn').disabled = true; say('Saqlanmoqda…');
  try {
    const path = editingId ? '/api/admin/dish/' + editingId : '/api/admin/dish';
    const r = await fetch(url(path), { method: 'POST', body: fd });
    const data = await r.json().catch(() => ({}));
    if (r.ok) {
      say(editingId ? 'Yangilandi ✅' : "Qo'shildi ✅", 'ok');
      if (tg && tg.HapticFeedback) tg.HapticFeedback.notificationOccurred('success');
      resetForm(); load();
    } else { say(data.error || "Saqlab bo'lmadi.", 'err'); }
  } catch (e) { say("Aloqa uzildi. Qaytadan urinib ko'ring.", 'err'); }
  $('saveBtn').disabled = false;
});

load();
</script>
<p style="text-align:center;font-size:11px;color:var(--muted);margin:20px 0 10px">
  Kod versiyasi: __VER__
</p>

</body>
</html>"""

def admin_from_request():
    """So'rovdagi imzolangan uid/ts/sig ni tekshiradi va admin ekanini aniqlaydi."""
    src = request.args
    user = verify_signed_user(src.get("uid"), src.get("uname"), src.get("ts"), src.get("sig"))
    if not user or not is_owner(user["id"]):
        return None
    return user

@app.route("/admin")
def admin_page():
    if not admin_from_request():
        return "<h3 style='font-family:sans-serif;padding:24px'>Ruxsat yo'q.<br><br>" \
               "Telegram'da botga <b>/start</b> yuboring va \"🧑‍🍳 Menyuni boshqarish\" " \
               "tugmasini qaytadan bosing.</h3>", 403
    html = (ADMIN_PAGE_HTML
            .replace("__CATEGORIES__", json.dumps(CATEGORIES, ensure_ascii=False))
            .replace("__EMOJI__", json.dumps(CATEGORY_EMOJI, ensure_ascii=False))
            .replace("__VER__", APP_VERSION))
    return no_cache(html)

TGORDER_PAGE_HTML = """<!doctype html>
<html lang="uz">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1, viewport-fit=cover">
<meta name="theme-color" content="#0a1230">
<title>Telegram buyurtmasi</title>
<script src="https://telegram.org/js/telegram-web-app.js"></script>
<style>
  :root{ --bg:#0a1230; --card:#141c3d; --line:#26305c; --ink:#eef1ff;
         --dim:#9aa4cc; --gold:#f2c14e; --ok:#43d17c; --err:#ff6b6b; }
  *{ box-sizing:border-box; -webkit-tap-highlight-color:transparent; }
  body{ margin:0; background:var(--bg); color:var(--ink);
        font:15px/1.45 -apple-system,Segoe UI,Roboto,sans-serif; padding-bottom:110px; }
  header{ position:sticky; top:0; z-index:5; background:var(--bg);
          border-bottom:1px solid var(--line); padding:12px 14px; }
  h1{ font-size:16px; margin:0 0 2px; }
  .sub{ font-size:12px; color:var(--dim); }
  .wrap{ padding:12px 14px; }
  .card{ background:var(--card); border:1px solid var(--line);
         border-radius:13px; padding:12px; margin-bottom:12px; }
  label{ display:block; font-size:12px; color:var(--dim); margin:9px 0 4px; }
  input, textarea{ width:100%; padding:10px 11px; border-radius:9px;
     border:1px solid var(--line); background:#0e1535; color:var(--ink); font:inherit; }
  textarea{ min-height:58px; resize:vertical; }
  .catname{ font-size:13px; color:var(--gold); margin:16px 0 7px; font-weight:700; }
  .dish{ display:flex; align-items:center; gap:10px; padding:9px 0;
         border-bottom:1px solid var(--line); }
  .dish:last-child{ border-bottom:0; }
  .dname{ flex:1; min-width:0; }
  .dname b{ display:block; font-weight:600; font-size:14px; }
  .dname span{ font-size:12px; color:var(--dim); }
  .qty{ display:flex; align-items:center; gap:8px; }
  .qty button{ width:32px; height:32px; border-radius:9px; border:1px solid var(--line);
     background:#0e1535; color:var(--ink); font-size:17px; font-weight:700; }
  .qty b{ min-width:20px; text-align:center; font-size:15px; }
  .out{ opacity:.45; }
  .msg{ padding:10px 12px; border-radius:10px; font-size:13px; margin-bottom:10px; }
  .msg.info{ background:#16204a; color:var(--dim); }
  .msg.err{ background:#3a1620; color:var(--err); }
  .msg.ok{ background:#102c1d; color:var(--ok); }
  .freerow{ margin-top:8px; }
  .freerow.two{ display:flex; gap:8px; }
  .freerow.two input{ flex:1; min-width:0; }
  .freerow button{ flex:0 0 108px; border-radius:9px; border:0; background:var(--gold);
                   color:#1a1200; font-weight:700; font-size:14px; }
  .fitem{ display:flex; align-items:center; gap:10px; padding:9px 0;
          border-bottom:1px solid var(--line); }
  .fitem:last-child{ border-bottom:0; }
  .fitem .t{ flex:1; min-width:0; font-size:14px; }
  .fitem .t span{ display:block; font-size:12px; color:var(--dim); }
  .fitem button{ width:32px; height:32px; border-radius:9px; border:1px solid var(--line);
                 background:#0e1535; color:var(--err); font-size:16px; }
  .bottom{ position:fixed; left:0; right:0; bottom:0; background:var(--card);
     border-top:1px solid var(--line); padding:11px 14px calc(11px + env(safe-area-inset-bottom)); }
  .sum{ display:flex; justify-content:space-between; font-size:15px; margin-bottom:9px; }
  .sum b{ color:var(--gold); }
  .go{ width:100%; padding:14px; border-radius:11px; border:0; font-size:15px;
       font-weight:700; background:var(--gold); color:#1a1200; }
  .go[disabled]{ opacity:.5; }
  .note{ font-size:11.5px; color:var(--dim); margin-top:8px; text-align:center; }
  a{ color:var(--gold); }
</style>
</head>
<body>

<header>
  <h1 id="ttl">Telegramdan tushgan buyurtma</h1>
  <div class="sub" id="who">Yuklanmoqda...</div>
</header>

<div class="wrap">
  <div id="msg" class="msg info">Menyu yuklanmoqda...</div>

  <div class="card">
    <label>Mijoz ismi</label>
    <input id="f_name" placeholder="Ism">
    <label>Telefon</label>
    <input id="f_phone" placeholder="05xxxxxxxx" inputmode="tel">
    <label>Manzil</label>
    <textarea id="f_addr" placeholder="Manzil yoki mo'ljal"></textarea>
    <div id="locbox" class="sub" style="margin-top:7px"></div>
    <label>Izoh (oshxona uchun)</label>
    <textarea id="f_note" placeholder="Masalan: achchiq qilmang"></textarea>
  </div>

  <div class="card">
    <div class="catname" style="margin-top:0">Qo‘lda qo‘shish (kg, maxsus buyurtma)</div>
    <div class="freerow">
      <input id="c_name" placeholder="Nomi — masalan: Osh">
    </div>
    <div class="freerow two">
      <input id="c_qty" inputmode="decimal" placeholder="Miqdor (1 yoki 0.5)">
      <input id="c_unit" placeholder="Birlik — kg">
    </div>
    <div class="freerow two">
      <input id="c_price" inputmode="decimal" placeholder="Birlik narxi (SAR)">
      <button type="button" id="c_add">Qo‘shish</button>
    </div>
    <div id="c_list"></div>
  </div>

  <div class="card" id="menu"></div>
</div>

<div class="bottom">
  <div class="sum"><span id="cnt">0 ta taom</span><b id="total">0</b></div>
  <button class="go" id="go" disabled>Buyurtmani yaratish</button>
  <div class="note">Bu buyurtmaga keshbek yozilmaydi</div>
</div>

<script>
(function(){
  var tg = window.Telegram && window.Telegram.WebApp;
  try{ if (tg){ tg.ready(); tg.expand(); } }catch(e){}

  var Q = new URLSearchParams(location.search);
  function auth(){
    var p = new URLSearchParams();
    ['draft','uid','uname','ts','sig'].forEach(function(k){
      if (Q.get(k) !== null) p.set(k, Q.get(k));
    });
    return p.toString();
  }
  function $(id){ return document.getElementById(id); }
  function say(text, kind){
    var m = $('msg');
    m.className = 'msg ' + (kind || 'info');
    m.textContent = text;
  }
  function esc(s){
    return String(s === null || s === undefined ? '' : s)
      .replace(/&/g,'&amp;').replace(/</g,'&lt;').replace(/>/g,'&gt;');
  }

  var MENU = [], CART = {}, CUR = 'SAR', draft = {}, FREE = [];

  function fmt(n){
    var v = Math.round(n * 100) / 100;
    return (v % 1 === 0 ? v.toFixed(0) : v.toFixed(2)) + ' ' + CUR;
  }

  function fq(q){
    return (Math.abs(q - Math.round(q)) < 1e-9)
      ? String(Math.round(q))
      : String(Math.round(q * 1000) / 1000);
  }

  function renderFree(){
    if (!FREE.length){ $('c_list').innerHTML = ''; return; }
    $('c_list').innerHTML = FREE.map(function(f, i){
      return '<div class="fitem"><div class="t">' + esc(f.name) +
             '<span>' + fq(f.qty) + (f.unit ? ' ' + esc(f.unit) : '') +
             ' \u00d7 ' + fmt(f.price) + ' = ' + fmt(f.qty * f.price) + '</span></div>' +
             '<button type="button" data-rm="' + i + '">\u00d7</button></div>';
    }).join('');
  }

  function renderTotals(){
    var n = 0, s = 0;
    MENU.forEach(function(d){
      var q = CART[d.id] || 0;
      n += q; s += q * d.price;
    });
    FREE.forEach(function(f){ n += 1; s += f.qty * f.price; });
    $('cnt').textContent = n + ' ta qator';
    $('total').textContent = fmt(s);
    $('go').disabled = (n === 0);
  }

  function setQty(id, delta){
    var d = MENU.filter(function(x){ return x.id === id; })[0];
    if (!d) return;
    var q = (CART[id] || 0) + delta;
    if (q < 0) q = 0;
    if (d.stock !== null && d.stock !== undefined && q > d.stock) q = d.stock;
    CART[id] = q;
    var el = document.querySelector('[data-q="' + id + '"]');
    if (el) el.textContent = q;
    renderTotals();
  }

  function renderMenu(){
    var byCat = {}, order = [];
    MENU.forEach(function(d){
      var c = d.category || 'Boshqa';
      if (!byCat[c]){ byCat[c] = []; order.push(c); }
      byCat[c].push(d);
    });
    var html = '';
    order.forEach(function(c){
      html += '<div class="catname">' + esc(c) + '</div>';
      byCat[c].forEach(function(d){
        var tugagan = (d.stock !== null && d.stock !== undefined && d.stock <= 0);
        html += '<div class="dish' + (tugagan ? ' out' : '') + '">' +
                  '<div class="dname"><b>' + esc(d.name) + '</b><span>' + fmt(d.price) +
                  (tugagan ? ' \u2014 tugagan' :
                    (d.stock !== null && d.stock !== undefined ? ' \u2014 ' + d.stock + ' dona' : '')) +
                  '</span></div>' +
                  '<div class="qty">' +
                    '<button type="button" data-m="' + d.id + '">\u2212</button>' +
                    '<b data-q="' + d.id + '">0</b>' +
                    '<button type="button" data-p="' + d.id + '"' + (tugagan ? ' disabled' : '') + '>+</button>' +
                  '</div></div>';
      });
    });
    $('menu').innerHTML = html || '<div class="sub">Menyu bo\u2018sh.</div>';
    $('menu').addEventListener('click', function(e){
      var t = e.target;
      if (t.dataset && t.dataset.p) setQty(parseInt(t.dataset.p, 10), 1);
      else if (t.dataset && t.dataset.m) setQty(parseInt(t.dataset.m, 10), -1);
    });
  }

  function fillDraft(){
    $('f_name').value = draft.name || '';
    $('f_phone').value = draft.phone || '';
    $('f_addr').value = draft.address || '';
    $('f_note').value = '';
    if (draft.manual) $('ttl').textContent = 'Telefon buyurtmasi';
    var kim = draft.name || (draft.manual ? 'ism va manzilni to\u2018ldiring' : 'mijoz');
    if (draft.username) kim += ' (@' + draft.username + ')';
    $('who').textContent = kim;
    var box = $('locbox'), parts = [];
    if (draft.lat !== null && draft.lat !== undefined){
      parts.push('\U0001F4CD Joylashuv olindi: ' + Number(draft.lat).toFixed(5) +
                 ', ' + Number(draft.lon).toFixed(5));
    }
    if (draft.map_link){
      parts.push('\U0001F517 <a href="' + esc(draft.map_link) + '" target="_blank">xarita havolasi</a>');
    }
    if (draft.tme){
      parts.push('\U0001F4AC <a href="' + esc(draft.tme) + '" target="_blank">mijozga yozish</a>');
    }
    box.innerHTML = parts.join('<br>');
  }

  async function load(){
    try{
      var r = await fetch('/api/tgorder/data?' + auth());
      var data = await r.json();
      if (!r.ok){ say(data.error || 'Xatolik', 'err'); return; }
      MENU = data.menu || [];
      draft = data.draft || {};
      CUR = data.currency || 'SAR';
      fillDraft();
      renderMenu();
      renderTotals();
      say('Taomlarni tanlang, keyin pastdagi tugmani bosing.', 'info');
    }catch(e){
      say('Server bilan aloqa yo\u2018q: ' + (e && e.message ? e.message : e), 'err');
    }
  }

  $('c_add').addEventListener('click', function(){
    var nm = $('c_name').value.trim();
    var q = parseFloat(($('c_qty').value || '1').replace(',', '.'));
    var p = parseFloat(($('c_price').value || '').replace(',', '.'));
    if (!nm){ $('c_name').focus(); return; }
    if (!(q > 0)){ $('c_qty').focus(); return; }
    if (!(p >= 0)){ $('c_price').focus(); return; }
    FREE.push({ name: nm, qty: q, price: p, unit: $('c_unit').value.trim() });
    $('c_name').value = ''; $('c_qty').value = ''; $('c_price').value = '';
    renderFree(); renderTotals();
    say('Qo\u2018shildi: ' + nm, 'ok');
  });

  $('c_list').addEventListener('click', function(e){
    var i = e.target && e.target.dataset ? e.target.dataset.rm : null;
    if (i === null || i === undefined) return;
    FREE.splice(parseInt(i, 10), 1);
    renderFree(); renderTotals();
  });

  $('go').addEventListener('click', async function(){
    var cart = {};
    Object.keys(CART).forEach(function(k){ if (CART[k] > 0) cart[k] = CART[k]; });
    if (!Object.keys(cart).length && !FREE.length){ say('Savat bo\u2018sh.', 'err'); return; }
    $('go').disabled = true;
    say('Yuborilmoqda...', 'info');
    try{
      var r = await fetch('/api/tgorder/create?' + auth(), {
        method: 'POST',
        headers: { 'Content-Type': 'application/json' },
        body: JSON.stringify({
          cart: cart,
          custom: FREE,
          name: $('f_name').value.trim(),
          phone: $('f_phone').value.trim(),
          address: $('f_addr').value.trim(),
          note: $('f_note').value.trim()
        })
      });
      var data = await r.json();
      if (!r.ok || data.error){
        say(data.error || 'Xatolik', 'err');
        $('go').disabled = false;
        return;
      }
      say('\u2705 Buyurtma #' + data.no + ' yaratildi.', 'ok');
      setTimeout(function(){ try{ tg && tg.close(); }catch(e){} }, 1200);
    }catch(e){
      say('Yuborilmadi: ' + (e && e.message ? e.message : e), 'err');
      $('go').disabled = false;
    }
  });

  load();
})();
</script>
</body>
</html>
"""

# ---------- nasiya va avans sahifasi ----------

@app.route("/hisob")
def hisob_page():
    if not admin_from_request():
        return ("<h3 style='font-family:sans-serif;padding:24px'>Ruxsat yo'q.<br><br>"
                "Botda /hisob yuboring va chiqqan tugmani bosing.</h3>"), 403
    return no_cache(HISOB_PAGE_HTML)

def _hisob_holder_payload():
    users = load_users()
    out = []
    for uid, bal, name, uname in account_holders():
        out.append({"uid": uid, "bal": bal, "name": name, "uname": uname})
    return out

@app.route("/api/hisob/data")
def api_hisob_data():
    if not admin_from_request():
        return jsonify({"error": "Ruxsat yo'q"}), 403
    tot = account_totals()
    return jsonify({"holders": _hisob_holder_payload(),
                    "debt": tot["debt"], "debtors": tot["debtors"],
                    "advance": tot["advance"], "advanced": tot["advanced"]})

@app.route("/api/hisob/find")
def api_hisob_find():
    if not admin_from_request():
        return jsonify({"error": "Ruxsat yo'q"}), 403
    q = (request.args.get("q") or "").strip().lstrip("@").lower()
    if len(q) < 2:
        return jsonify({"found": []})
    found = []
    for uid, u in load_users().items():
        name = (u.get("name") or "").strip()
        uname = (u.get("username") or "").strip()
        if q in name.lower() or q in uname.lower() or q == str(uid):
            found.append({"uid": int(uid), "bal": account_balance(uid),
                          "name": name, "uname": uname})
        if len(found) >= 40:
            break
    found.sort(key=lambda r: (r["bal"], r["name"].lower()))
    return jsonify({"found": found})

@app.route("/api/hisob/one")
def api_hisob_one():
    if not admin_from_request():
        return jsonify({"error": "Ruxsat yo'q"}), 403
    # "uid" admin imzosi uchun band — mijozni "cid" bilan olamiz
    try:
        uid = int(request.args.get("cid"))
    except Exception:
        return jsonify({"error": "Mijoz ko'rsatilmagan"}), 400
    u = (load_users().get(str(uid)) or {})
    rec = (load_account().get(str(uid)) or {})
    hist = []
    for h in (rec.get("history") or [])[-15:]:
        hist.append({
            "delta": money(h.get("delta", 0)),
            "note": h.get("note") or "",
            "when": datetime.fromtimestamp(h.get("ts", 0), TIMEZONE).strftime("%d.%m %H:%M"),
        })
    return jsonify({"uid": uid, "bal": account_balance(uid),
                    "name": (u.get("name") or "").strip(),
                    "uname": u.get("username") or "", "history": hist})

@app.route("/api/hisob/move", methods=["POST"])
def api_hisob_move():
    if not admin_from_request():
        return jsonify({"error": "Ruxsat yo'q"}), 403
    body = request.get_json(force=True, silent=True) or {}
    try:
        uid = int(body.get("uid"))
        delta = money(float(body.get("delta")))
    except Exception:
        return jsonify({"error": "Noto'g'ri ma'lumot"}), 400
    if delta == 0:
        return jsonify({"error": "Summa noldan farqli bo'lsin"}), 400
    if abs(delta) > 100000:
        return jsonify({"error": "Summa juda katta"}), 400
    note = (body.get("note") or "").strip()[:120]
    bal = account_move(uid, delta, None,
                       note or ("to'lov" if delta > 0 else "qarz qo'shildi"))
    if delta > 0:
        try:
            lang = get_user_lang(uid)
            bot.send_message(uid, t("acct_paid", lang,
                                    amt=fmt_sum(delta), bal=fmt_signed(bal)))
        except Exception:
            pass
    return jsonify({"ok": True, "bal": bal})

# ---------- Telegramdan tushgan buyurtma ----------

HISOB_PAGE_HTML = """<!doctype html>
<html lang="uz">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1, viewport-fit=cover">
<meta name="theme-color" content="#0a1230">
<title>Nasiya va avans</title>
<script src="https://telegram.org/js/telegram-web-app.js"></script>
<style>
  :root{ --bg:#0a1230; --card:#141c3d; --line:#26305c; --ink:#eef1ff;
         --dim:#9aa4cc; --gold:#f2c14e; --ok:#43d17c; --err:#ff6b6b; }
  *{ box-sizing:border-box; -webkit-tap-highlight-color:transparent; }
  body{ margin:0; background:var(--bg); color:var(--ink);
        font:15px/1.45 -apple-system,Segoe UI,Roboto,sans-serif; padding-bottom:24px; }
  header{ position:sticky; top:0; z-index:5; background:var(--bg);
          border-bottom:1px solid var(--line); padding:12px 14px; }
  h1{ font-size:16px; margin:0 0 8px; }
  .tot{ display:flex; gap:10px; }
  .tot div{ flex:1; background:var(--card); border:1px solid var(--line);
            border-radius:11px; padding:9px 11px; }
  .tot b{ display:block; font-size:16px; margin-top:2px; }
  .tot .d b{ color:var(--err); }
  .tot .a b{ color:var(--ok); }
  .tot span{ font-size:11.5px; color:var(--dim); }
  .wrap{ padding:12px 14px; }
  .msg{ padding:10px 12px; border-radius:10px; font-size:13px; margin-bottom:11px; }
  .msg.info{ background:#16204a; color:var(--dim); }
  .msg.err{ background:#3a1620; color:var(--err); }
  .msg.ok{ background:#102c1d; color:var(--ok); }
  input{ width:100%; padding:11px 12px; border-radius:10px; border:1px solid var(--line);
         background:#0e1535; color:var(--ink); font:inherit; }
  .sect{ font-size:12.5px; color:var(--gold); font-weight:700; margin:18px 0 8px; }
  .row{ display:flex; align-items:center; gap:10px; background:var(--card);
        border:1px solid var(--line); border-radius:11px; padding:11px 12px; margin-bottom:8px; }
  .row .nm{ flex:1; min-width:0; }
  .row .nm b{ display:block; font-weight:600; font-size:14.5px;
              overflow:hidden; text-overflow:ellipsis; white-space:nowrap; }
  .row .nm span{ font-size:11.5px; color:var(--dim); }
  .row .bl{ font-weight:700; font-size:15px; white-space:nowrap; }
  .minus{ color:var(--err); } .plus{ color:var(--ok); }
  .empty{ color:var(--dim); font-size:13.5px; padding:10px 2px; }
  dialog{ border:0; background:transparent; padding:0; max-width:460px; width:94%; }
  dialog::backdrop{ background:rgba(4,8,24,.75); }
  .sheet{ background:var(--card); border:1px solid var(--line);
          border-radius:16px; padding:15px; color:var(--ink); }
  .sheet h2{ font-size:16px; margin:0 0 2px; }
  .sheet .who{ font-size:12px; color:var(--dim); margin-bottom:12px; }
  .bal{ font-size:22px; font-weight:700; margin-bottom:12px; }
  .acts{ display:flex; gap:9px; margin:12px 0 4px; }
  .acts button{ flex:1; padding:12px 0; border-radius:10px; border:0;
                font-size:14px; font-weight:700; }
  .pay{ background:var(--ok); color:#06240f; }
  .debt{ background:#3a1620; color:var(--err); border:1px solid #5a2430 !important; }
  .close{ width:100%; margin-top:10px; padding:11px; border-radius:10px;
          border:1px solid var(--line); background:transparent; color:var(--dim); font:inherit; }
  .hist{ margin-top:12px; border-top:1px solid var(--line); padding-top:10px; }
  .hist div{ font-size:12px; color:var(--dim); padding:3px 0; }
  .hist .d{ color:var(--err); } .hist .p{ color:var(--ok); }
  label{ display:block; font-size:12px; color:var(--dim); margin:10px 0 4px; }
</style>
</head>
<body>

<header>
  <h1>Nasiya va avans</h1>
  <div class="tot">
    <div class="d"><span>Nasiya</span><b id="t_debt">—</b></div>
    <div class="a"><span>Avans</span><b id="t_adv">—</b></div>
  </div>
</header>

<div class="wrap">
  <div id="msg" class="msg info">Yuklanmoqda...</div>
  <input id="q" placeholder="Mijozni qidirish — ism yoki @username" autocomplete="off">
  <div id="list"></div>
</div>

<dialog id="dlg"><div class="sheet">
  <h2 id="d_name">—</h2>
  <div class="who" id="d_who"></div>
  <div class="bal" id="d_bal">—</div>
  <label>Summa (SAR)</label>
  <input id="d_amt" inputmode="decimal" placeholder="0">
  <label>Izoh (ixtiyoriy)</label>
  <input id="d_note" placeholder="masalan: eski nasiya">
  <div class="acts">
    <button class="pay" id="b_pay">To‘lov qabul qilish</button>
    <button class="debt" id="b_debt">Qarz qo‘shish</button>
  </div>
  <div class="hist" id="d_hist"></div>
  <button class="close" id="b_close">Yopish</button>
</div></dialog>

<script>
(function(){
  var tg = window.Telegram && window.Telegram.WebApp;
  try{ if (tg){ tg.ready(); tg.expand(); } }catch(e){}

  var Q = new URLSearchParams(location.search);
  function auth(){
    var p = new URLSearchParams();
    ['uid','uname','ts','sig'].forEach(function(k){
      if (Q.get(k) !== null) p.set(k, Q.get(k));
    });
    return p.toString();
  }
  function $(id){ return document.getElementById(id); }
  function say(t, k){ var m = $('msg'); m.className = 'msg ' + (k || 'info'); m.textContent = t; }
  function esc(s){
    return String(s === null || s === undefined ? '' : s)
      .replace(/&/g,'&amp;').replace(/</g,'&lt;').replace(/>/g,'&gt;');
  }
  function fmt(n){
    var v = Math.round(Math.abs(n) * 100) / 100;
    return (v % 1 === 0 ? v.toFixed(0) : v.toFixed(2)) + ' SAR';
  }
  function signed(n){
    if (n < 0) return '\u2212' + fmt(n);
    if (n > 0) return '+' + fmt(n);
    return fmt(0);
  }

  var holders = [], current = null, timer = null;

  function rowHtml(h){
    var cls = h.bal < 0 ? 'minus' : 'plus';
    var sub = h.uname ? '@' + esc(h.uname) : ('ID ' + h.uid);
    return '<div class="row" data-uid="' + h.uid + '">' +
             '<div class="nm"><b>' + esc(h.name || 'Ismsiz') + '</b><span>' + sub + '</span></div>' +
             '<div class="bl ' + cls + '">' + signed(h.bal) + '</div>' +
           '</div>';
  }

  function render(){
    var qarz = holders.filter(function(h){ return h.bal < 0; });
    var avans = holders.filter(function(h){ return h.bal > 0; });
    var html = '';
    if (qarz.length){
      html += '<div class="sect">Qarzdorlar (' + qarz.length + ')</div>' +
              qarz.map(rowHtml).join('');
    }
    if (avans.length){
      html += '<div class="sect">Avansi borlar (' + avans.length + ')</div>' +
              avans.map(rowHtml).join('');
    }
    if (!qarz.length && !avans.length){
      html = '<div class="empty">Nol bo\u2018lmagan hisob yo\u2018q. Mijozni qidirib, qarz yoki avans kiritishingiz mumkin.</div>';
    }
    $('list').innerHTML = html;
  }

  function renderFound(list){
    if (!list.length){ $('list').innerHTML = '<div class="empty">Topilmadi.</div>'; return; }
    $('list').innerHTML = '<div class="sect">Topildi (' + list.length + ')</div>' +
                          list.map(rowHtml).join('');
  }

  async function load(){
    try{
      var r = await fetch('/api/hisob/data?' + auth());
      var d = await r.json();
      if (!r.ok){ say(d.error || 'Xatolik', 'err'); return; }
      holders = d.holders || [];
      $('t_debt').textContent = fmt(d.debt) + ' \u00b7 ' + d.debtors + ' ta';
      $('t_adv').textContent = fmt(d.advance) + ' \u00b7 ' + d.advanced + ' ta';
      render();
      say('Mijozni bosing \u2014 to\u2018lov qabul qilasiz yoki qarz qo\u2018shasiz.', 'info');
    }catch(e){ say('Aloqa yo\u2018q: ' + (e && e.message ? e.message : e), 'err'); }
  }

  async function openOne(uid){
    try{
      var r = await fetch('/api/hisob/one?cid=' + encodeURIComponent(uid) + '&' + auth());
      var d = await r.json();
      if (!r.ok){ say(d.error || 'Xatolik', 'err'); return; }
      current = d;
      $('d_name').textContent = d.name || 'Ismsiz';
      $('d_who').textContent = (d.uname ? '@' + d.uname + ' \u00b7 ' : '') + 'ID ' + d.uid;
      $('d_bal').textContent = signed(d.bal);
      $('d_bal').className = 'bal ' + (d.bal < 0 ? 'minus' : (d.bal > 0 ? 'plus' : ''));
      $('d_amt').value = ''; $('d_note').value = '';
      var h = (d.history || []).slice().reverse().map(function(x){
        return '<div><span class="' + (x.delta < 0 ? 'd' : 'p') + '">' + signed(x.delta) +
               '</span> \u00b7 ' + esc(x.when) + (x.note ? ' \u00b7 ' + esc(x.note) : '') + '</div>';
      }).join('');
      $('d_hist').innerHTML = h || '<div>Harakat yo\u2018q.</div>';
      $('dlg').showModal();
    }catch(e){ say('Aloqa yo\u2018q', 'err'); }
  }

  async function move(sign){
    if (!current) return;
    var v = parseFloat(($('d_amt').value || '').replace(',', '.'));
    if (!(v > 0)){ $('d_amt').focus(); return; }
    $('b_pay').disabled = $('b_debt').disabled = true;
    try{
      var r = await fetch('/api/hisob/move?' + auth(), {
        method: 'POST', headers: { 'Content-Type': 'application/json' },
        body: JSON.stringify({ uid: current.uid, delta: sign * v, note: $('d_note').value.trim() })
      });
      var d = await r.json();
      if (!r.ok || d.error){ say(d.error || 'Xatolik', 'err'); return; }
      $('dlg').close();
      var nomi = current.name || 'Mijoz';
      $('q').value = '';
      await load();
      // xabarni oxirida qo'yamiz, aks holda load() uni o'chirib yuboradi
      say('\u2705 ' + nomi + ': ' + signed(sign * v) +
          ' \u2014 yangi balans ' + signed(d.bal), 'ok');
    }catch(e){ say('Yuborilmadi', 'err'); }
    finally{ $('b_pay').disabled = $('b_debt').disabled = false; }
  }

  $('list').addEventListener('click', function(e){
    var row = e.target.closest ? e.target.closest('.row') : null;
    if (row && row.dataset.uid) openOne(row.dataset.uid);
  });
  $('b_pay').addEventListener('click', function(){ move(1); });
  $('b_debt').addEventListener('click', function(){ move(-1); });
  $('b_close').addEventListener('click', function(){ $('dlg').close(); });

  $('q').addEventListener('input', function(){
    clearTimeout(timer);
    var v = $('q').value.trim();
    timer = setTimeout(async function(){
      if (v.length < 2){ render(); return; }
      try{
        var r = await fetch('/api/hisob/find?q=' + encodeURIComponent(v) + '&' + auth());
        var d = await r.json();
        if (r.ok) renderFound(d.found || []);
      }catch(e){}
    }, 280);
  });

  load();
})();
</script>
</body>
</html>
"""

@app.route("/tgorder")
def tgorder_page():
    if not admin_from_request():
        return ("<h3 style='font-family:sans-serif;padding:24px'>Ruxsat yo'q.<br><br>"
                "Botdagi buyurtma qoralamasidan \"Savatni yig'ish\" tugmasini bosing.</h3>"), 403
    return no_cache(TGORDER_PAGE_HTML)

@app.route("/api/tgorder/data")
def api_tgorder_data():
    if not admin_from_request():
        return jsonify({"error": "Ruxsat yo'q"}), 403
    token = request.args.get("draft") or ""
    d = tgdraft_get(token)
    if not d:
        return jsonify({"error": "Qoralama topilmadi yoki eskirdi. Mijoz xabarini qaytadan forward qiling."}), 404

    disc = get_discount()
    menu = []
    for x in load_menu():
        if x.get("hidden"):
            continue
        menu.append({
            "id": x["id"],
            "name": x["name"],
            "price": discounted_price(x["price"], disc),
            "stock": x.get("stock"),
            "category": x.get("category", DEFAULT_CATEGORY),
        })
    sira = {c: i for i, c in enumerate(CATEGORIES)}
    menu.sort(key=lambda m: (sira.get(m["category"], 99), m["name"].lower()))
    return jsonify({"draft": d, "menu": menu, "currency": "SAR"})

@app.route("/api/tgorder/create", methods=["POST"])
def api_tgorder_create():
    admin = admin_from_request()
    if not admin:
        return jsonify({"error": "Ruxsat yo'q"}), 403
    token = request.args.get("draft") or ""
    d = tgdraft_get(token)
    if not d:
        return jsonify({"error": "Qoralama topilmadi yoki eskirdi."}), 404

    body = request.get_json(force=True, silent=True) or {}
    raw_cart = body.get("cart") or {}
    cart = {}
    for k, v in raw_cart.items():
        try:
            dish_id, qty = int(k), int(v)
        except Exception:
            continue
        if qty > 0:
            cart[dish_id] = qty
    # menyuda yo'q qatorlar: kg bilan sotiladigan narsalar va maxsus buyurtmalar
    custom = []
    for c in (body.get("custom") or [])[:25]:
        try:
            nm = str(c.get("name") or "").strip()[:60]
            q = round(float(c.get("qty") or 0), 3)
            p = money(float(c.get("price")))
        except Exception:
            continue
        if nm and q > 0 and p >= 0:
            custom.append({"name": nm, "qty": q, "price": p,
                           "unit": str(c.get("unit") or "").strip()[:8]})

    if not cart and not custom:
        return jsonify({"error": "Savat bo'sh."}), 400

    name = (body.get("name") or d.get("name") or "Mijoz").strip()[:60]
    phone = (body.get("phone") or d.get("phone") or "").strip()[:30]
    address = (body.get("address") or d.get("address") or "").strip()[:300]
    note = (body.get("note") or "").strip()[:300]
    lat, lon = d.get("lat"), d.get("lon")
    if lat is None and not address:
        address = (d.get("map_link") or d.get("text") or "\u2014")[:300]

    extra = {
        "source": "qolda" if d.get("manual") else "telegram",
        "no_cashback": True,            # qo'lda kiritilgan \u2014 keshbek yo'q
        "entered_by": admin["id"],
    }
    if d.get("tme"):
        extra["tme"] = d["tme"]
    if d.get("map_link"):
        extra["map_link"] = d["map_link"]

    order, error = create_order(
        cart, name, phone, lat, lon, address, note,
        d.get("user_id"), d.get("username"),
        use_cashback=False, extra=extra, custom_items=custom)
    if error:
        return jsonify({"error": error}), 400

    d["used"] = True
    tgdraft_drop(token)
    return jsonify({"ok": True, "id": order["id"], "no": order.get("daily_number")})

# ---------- oshxona printeri uchun API ----------

@app.route("/kitchen")
def kitchen_page():
    if not admin_from_request():
        return ("<h3 style='font-family:sans-serif;padding:24px;line-height:1.6'>Ruxsat yo'q.<br><br>"
                "Telegramda botga <b>/start</b> yuboring va \"🖨 Oshxona\" tugmasini bosing.</h3>"), 403
    return no_cache(KITCHEN_PAGE_HTML.replace("__VER__", APP_VERSION))

@app.route("/api/print/pending")
def api_print_pending():
    """Hali chop etilmagan buyurtmalar. Oshxona sahifasi shuni so'rab turadi."""
    if not admin_from_request():
        return jsonify({"error": "Ruxsat yo'q"}), 403
    try:
        width = int(request.args.get("w") or RECEIPT_WIDTH)
    except Exception:
        width = RECEIPT_WIDTH
    width = max(10, min(64, width))
    # logo rasm sifatida chiqsa, chek matnida nom yozuvi takrorlanmasin
    with_logo = request.args.get("logo") == "1"

    today = today_key()
    out = []
    for o in load_orders():
        if o.get("printed"):
            continue
        if is_cancelled(o):
            continue
        if o.get("day_key") != today:      # eski buyurtmalar o'z-o'zidan chiqmasin
            continue
        out.append({
            "id": o["id"],
            "no": o.get("daily_number"),
            "name": o.get("customer_name"),
            "total": o.get("total"),
            "items": [f"{it['name']} x{fmt_qty(it)}" for it in o.get("items", []) if not it.get("cancelled")],
            "receipt": build_receipt_text(o, width, header=not with_logo),
            "blocks": build_receipt_blocks(o, width, header=not with_logo),
        })
    out.sort(key=lambda x: x["id"])
    return jsonify({"orders": out, "shop": shop_status(),
                    "has_logo": os.path.exists(LOGO_PATH)})

@app.route("/api/print/done", methods=["POST"])
def api_print_done():
    """Chop etilgan buyurtmalarni belgilaymiz — qayta chiqmasligi uchun."""
    if not admin_from_request():
        return jsonify({"error": "Ruxsat yo'q"}), 403
    body = request.get_json(force=True, silent=True) or {}
    ids = body.get("ids") or []
    if not isinstance(ids, list):
        return jsonify({"error": "ids ro'yxat bo'lishi kerak"}), 400
    ids = set(int(i) for i in ids if str(i).lstrip("-").isdigit())
    orders = load_orders()
    n = 0
    for o in orders:
        if o["id"] in ids and not o.get("printed"):
            o["printed"] = True
            n += 1
    if n:
        save_orders(orders)
    return jsonify({"ok": True, "marked": n})

@app.route("/api/print/again", methods=["POST"])
def api_print_again():
    """Bugungi buyurtmani qayta chop etishga qo'yadi (kunlik raqami bo'yicha)."""
    if not admin_from_request():
        return jsonify({"error": "Ruxsat yo'q"}), 403
    body = request.get_json(force=True, silent=True) or {}
    try:
        no = int(body.get("no"))
    except Exception:
        return jsonify({"error": "Kunlik raqamni kiriting"}), 400
    orders = load_orders()
    day = today_key()
    target = next((o for o in orders if o.get("day_key") == day and o.get("daily_number") == no), None)
    if not target:
        return jsonify({"error": f"Bugungi buyurtmalar orasida #{no} topilmadi"}), 404
    target["printed"] = False
    save_orders(orders)
    return jsonify({"ok": True})

@app.route("/api/admin/quiz", methods=["GET", "POST"])
def api_admin_quiz():
    if not admin_from_request():
        return jsonify({"error": "Ruxsat yo'q"}), 403
    if request.method == "GET":
        q = load_quiz()
        return jsonify({"quiz": {"active": q["active"], "test": q["test"], "title": q["title"],
                                 "prize": q["prize"], "text": quiz_to_text(q),
                                 "count": len(q["questions"])}})

    body = request.get_json(force=True, silent=True) or {}
    q = load_quiz()
    q["title"] = (body.get("title") or "").strip() or "Viktorina"
    q["prize"] = (body.get("prize") or "").strip()

    if "text" in body:
        questions, errors = parse_quiz_text(body.get("text"))
        if errors:
            return jsonify({"error": "; ".join(errors[:3])}), 400
        q["questions"] = questions

    if "test" in body:
        q["test"] = bool(body.get("test"))

    active = body.get("active")
    if active is not None:
        if active and not q["questions"]:
            return jsonify({"error": "Avval savollarni kiriting."}), 400
        q["active"] = bool(active)

    save_quiz(q)
    for admin_id in load_admin_ids():
        try:
            if active is True:
                rejim = "🧪 sinov rejimida (faqat adminlar)" if q["test"] else "🟢 hamma uchun"
                bot.send_message(admin_id, f"🎁 Viktorina boshlandi {rejim} — {len(q['questions'])} ta savol.")
            elif active is False:
                bot.send_message(admin_id, "⏹ Viktorina to'xtatildi.")
        except Exception:
            pass
    return jsonify({"ok": True, "quiz": {"active": q["active"], "test": q["test"], "title": q["title"],
                                          "prize": q["prize"], "text": quiz_to_text(q),
                                          "count": len(q["questions"])}})

@app.route("/api/admin/quiz/results", methods=["GET", "DELETE"])
def api_admin_quiz_results():
    if not admin_from_request():
        return jsonify({"error": "Ruxsat yo'q"}), 403
    if request.method == "DELETE":
        save_quiz_results({})
        return jsonify({"ok": True})
    quiz = load_quiz()
    board = [{"name": r["name"], "username": r["username"], "correct": r["correct"],
              "time": fmt_secs(r["ms"]), "uid": r["uid"]} for r in quiz_leaderboard()]
    return jsonify({"board": board, "total": len(quiz["questions"])})

@app.route("/api/admin/hours", methods=["GET", "POST"])
def api_admin_hours():
    if not admin_from_request():
        return jsonify({"error": "Ruxsat yo'q"}), 403
    if request.method == "GET":
        return jsonify({"hours": get_hours(), "shop": shop_status()})
    body = request.get_json(force=True, silent=True) or {}
    open_t = body.get("open")
    close_t = body.get("close")
    if body.get("schedule_on"):
        if not (valid_hhmm(open_t) and valid_hhmm(close_t)):
            return jsonify({"error": "Vaqtni HH:MM ko'rinishida kiriting."}), 400
    was_open = shop_status()["open"]
    h = set_hours(closed_today=body.get("closed_today"), schedule_on=body.get("schedule_on"),
                  open_time=open_t, close_time=close_t)
    st = shop_status()
    if st["open"] != was_open:
        msg = ("🟢 Bot buyurtma qabul qila boshladi."
               if st["open"] else "🔴 Bot buyurtma qabul qilishni to'xtatdi — mijozlarga yopiq xabari chiqadi.")
        for admin_id in load_admin_ids():
            try:
                bot.send_message(admin_id, msg)
            except Exception:
                pass
    return jsonify({"ok": True, "hours": h, "shop": st})

@app.route("/api/admin/discount", methods=["GET", "POST"])
def api_admin_discount():
    if not admin_from_request():
        return jsonify({"error": "Ruxsat yo'q"}), 403
    if request.method == "GET":
        return jsonify({"discount": get_discount()})
    body = request.get_json(force=True, silent=True) or {}
    percent = body.get("percent")
    active = body.get("active")
    if active and (percent is None or not (1 <= int(percent) <= 90)):
        return jsonify({"error": "Chegirma foizi 1 dan 90 gacha bo'lishi kerak."}), 400
    disc = set_discount(active=active, percent=percent)
    # adminlarga xabar beramiz — kim yoqqani/o'chirgani bilinib tursin
    msg = (f"🏷 Aksiya YOQILDI — barcha taom narxi −{disc['percent']}%"
           if disc["active"] else "🏷 Aksiya o'chirildi — narxlar odatiyga qaytdi.")
    for admin_id in load_admin_ids():
        try:
            bot.send_message(admin_id, msg)
        except Exception:
            pass
    return jsonify({"ok": True, "discount": disc})

@app.route("/api/admin/dishes")
def api_admin_dishes():
    if not admin_from_request():
        return jsonify({"error": "Ruxsat yo'q"}), 403
    out = []
    for d in load_menu():
        item = {
            "id": d["id"], "name": d["name"], "price": d["price"],
            "desc": d.get("desc", ""), "stock": d.get("stock"),
            "category": d.get("category", DEFAULT_CATEGORY),
            "set": dish_set_keys(d),
            "set_extra": (d.get("set_extra") or "").strip(),
        }
        if d.get("local_photo"):
            item["photo_url"] = f"/static/dishes/{d['local_photo']}"
        out.append(item)
    return jsonify({"dishes": out, "set_catalog": set_catalog_payload()})

def read_dish_form():
    """Formadan kelgan maydonlarni o'qiydi. Xato bo'lsa (None, xabar) qaytaradi."""
    name = (request.form.get("name") or "").strip()
    if not name:
        return None, "Taom nomi bo'sh."
    try:
        price = float((request.form.get("price") or "").strip())
    except Exception:
        return None, "Narx noto'g'ri."
    if price < 0:
        return None, "Narx manfiy bo'lishi mumkin emas."
    desc = (request.form.get("desc") or "").strip()
    category = match_category(request.form.get("category") or "") or DEFAULT_CATEGORY
    stock_raw = (request.form.get("stock") or "0").strip()
    try:
        stock = int(float(stock_raw))
    except Exception:
        stock = 0
    stock = None if stock < 0 else stock
    set_items = parse_set_keys(request.form.get("set") or "")
    set_extra = (request.form.get("set_extra") or "").strip()[:80]
    return {"name": name, "price": price, "desc": desc, "category": category,
            "stock": stock, "set_items": set_items, "set_extra": set_extra}, None

def save_uploaded_photo(dish_id):
    """Yuklangan rasmni saqlaydi va fayl nomini qaytaradi. Rasm bo'lmasa None."""
    file = request.files.get("photo")
    if not file or not file.filename:
        return None
    ext = os.path.splitext(file.filename)[1].lower()
    if ext not in (".jpg", ".jpeg", ".png", ".webp"):
        ext = ".jpg"
    filename = f"{dish_id}-{int(time.time())}{ext}"
    file.save(os.path.join(DISH_PHOTOS_DIR, filename))
    return filename

def delete_local_photo(filename):
    if not filename:
        return
    try:
        os.remove(os.path.join(DISH_PHOTOS_DIR, filename))
    except Exception:
        pass

@app.route("/api/admin/dish", methods=["POST"])
def api_admin_add_dish():
    admin = admin_from_request()
    if not admin:
        return jsonify({"error": "Ruxsat yo'q"}), 403
    fields, err = read_dish_form()
    if err:
        return jsonify({"error": err}), 400
    menu = load_menu()
    new_id = (max([d["id"] for d in menu], default=0)) + 1
    try:
        local_photo = save_uploaded_photo(new_id)
    except Exception as e:
        print(f"Rasmni saqlashda xato: {e}")
        return jsonify({"error": "Rasmni saqlab bo'lmadi."}), 500
    menu.append({
        "id": new_id, "name": fields["name"], "price": fields["price"], "desc": fields["desc"],
        "photo_id": None, "local_photo": local_photo,
        "stock": fields["stock"], "category": fields["category"],
        "set_items": fields["set_items"], "set_extra": fields["set_extra"],
    })
    save_menu(menu)
    return jsonify({"ok": True, "id": new_id})

@app.route("/api/admin/dish/<int:dish_id>", methods=["POST"])
def api_admin_update_dish(dish_id):
    admin = admin_from_request()
    if not admin:
        return jsonify({"error": "Ruxsat yo'q"}), 403
    fields, err = read_dish_form()
    if err:
        return jsonify({"error": err}), 400
    menu = load_menu()
    dish = next((d for d in menu if d["id"] == dish_id), None)
    if not dish:
        return jsonify({"error": "Taom topilmadi."}), 404
    try:
        new_photo = save_uploaded_photo(dish_id)
    except Exception as e:
        print(f"Rasmni saqlashda xato: {e}")
        return jsonify({"error": "Rasmni saqlab bo'lmadi."}), 500
    if new_photo:
        delete_local_photo(dish.get("local_photo"))
        dish["local_photo"] = new_photo
        dish["photo_id"] = None  # yangi rasm Telegram'da ham qaytadan yuklanadi
    dish["name"] = fields["name"]
    dish["price"] = fields["price"]
    dish["desc"] = fields["desc"]
    dish["category"] = fields["category"]
    dish["stock"] = fields["stock"]
    dish["set_items"] = fields["set_items"]
    dish["set_extra"] = fields["set_extra"]
    save_menu(menu)
    return jsonify({"ok": True})

@app.route("/api/admin/dish/<int:dish_id>/delete", methods=["POST"])
def api_admin_delete_dish(dish_id):
    admin = admin_from_request()
    if not admin:
        return jsonify({"error": "Ruxsat yo'q"}), 403
    menu = load_menu()
    dish = next((d for d in menu if d["id"] == dish_id), None)
    if not dish:
        return jsonify({"error": "Taom topilmadi."}), 404
    delete_local_photo(dish.get("local_photo"))
    menu = [d for d in menu if d["id"] != dish_id]
    save_menu(menu)
    return jsonify({"ok": True})

# ---------- kunlik hisobot ----------

def build_daily_report_text(target_date):
    """target_date — datetime.date. O'sha kunning barcha buyurtmalari bo'yicha hisobot matnini quradi."""
    orders = load_orders()
    day_orders = [
        o for o in orders
        if datetime.fromtimestamp(o["created_at"], TIMEZONE).date() == target_date
    ]
    if not day_orders:
        return (
            f"📊 Kunlik hisobot — {target_date.strftime('%d.%m.%Y')}\n\n"
            f"Bugun buyurtma tushmadi."
        )

    # Bekor qilingan buyurtmalar savdoga qo'shilmaydi
    live_orders = [o for o in day_orders if not is_cancelled(o)]
    cancelled_orders = [o for o in day_orders if is_cancelled(o)]

    if not live_orders:
        return (
            f"📊 Kunlik hisobot — {target_date.strftime('%d.%m.%Y')}\n\n"
            f"Bugun haqiqiy buyurtma bo'lmadi.\n"
            f"❌ Bekor qilinganlar: {len(cancelled_orders)} ta"
        )

    total_revenue = money(sum(o["total"] for o in live_orders))
    cb_spent = money(sum(order_cashback_used(o) for o in live_orders))
    cb_given = money(sum(o.get("cashback_earned") or 0
                         for o in live_orders if o.get("cashback_credited")))
    cash_in = money(total_revenue - cb_spent)
    dish_counts = {}
    cancelled_items = 0
    for o in live_orders:
        for it in o["items"]:
            if it.get("cancelled"):          # buyurtma ichidan olib tashlangan taom
                cancelled_items += 1
                continue
            dish_counts[it["name"]] = dish_counts.get(it["name"], 0) + it["qty"]

    sorted_dishes = sorted(dish_counts.items(), key=lambda x: -x[1])
    dish_lines = "\n".join(f"  • {name} — {qty} dona" for name, qty in sorted_dishes) or "  —"

    status_counts = {}
    for o in live_orders:
        status_counts[o["status"]] = status_counts.get(o["status"], 0) + 1
    status_lines = "\n".join(f"  • {s}: {c}" for s, c in status_counts.items())

    text = (
        f"📊 Kunlik hisobot — {target_date.strftime('%d.%m.%Y')}\n\n"
        f"🧾 Buyurtmalar soni: {len(live_orders)}\n"
        f"💰 Jami savdo: {fmt_sum(total_revenue)}\n"
        + (f"💳 Keshbek bilan to'landi: −{fmt_sum(cb_spent)}\n"
           f"💵 Naqd tushum: {fmt_sum(cash_in)}\n" if cb_spent > 0 else "")
        + (f"🎁 Bugun yozilgan keshbek: {fmt_sum(cb_given)}\n" if cb_given > 0 else "")
        + f"\n🍽 Sotilgan taomlar:\n{dish_lines}\n\n"
        f"📦 Holatlar bo'yicha:\n{status_lines}"
    )
    if cancelled_orders or cancelled_items:
        text += "\n\n— — —"
        if cancelled_orders:
            yoqotilgan = sum(o.get("total", 0) for o in cancelled_orders)
            text += (f"\n❌ Bekor qilingan buyurtmalar: {len(cancelled_orders)} ta"
                     f" ({fmt_sum(yoqotilgan)}) — savdoga qo'shilmadi")
        if cancelled_items:
            text += f"\n➖ Buyurtmalardan olib tashlangan taomlar: {cancelled_items} ta"
    return text

def send_daily_report(target_date):
    text = build_daily_report_text(target_date)
    for admin_id in load_admin_ids():
        try:
            bot.send_message(admin_id, text)
        except Exception:
            pass

@bot.message_handler(commands=["report"])
def cmd_report(message):
    if not is_owner(message.chat.id):
        return
    today = datetime.now(TIMEZONE).date()
    bot.send_message(message.chat.id, build_daily_report_text(today))

@bot.message_handler(commands=["yigma", "builder"])
def cmd_builder_min(message):
    """«O'zingiz yig'ing» bo'limining eng kam summasi."""
    if not is_owner(message.chat.id):
        return
    parts = (message.text or "").split()
    if len(parts) > 1:
        try:
            v = float(parts[1].replace(",", "."))
        except Exception:
            bot.send_message(message.chat.id, "Masalan: /yigma 30")
            return
        if v < 0 or v > 1000:
            bot.send_message(message.chat.id, "0 dan 1000 gacha bo'lsin.")
            return
        set_builder_min(v)
        if v == 0:
            bot.send_message(message.chat.id,
                "✅ Chegara olib tashlandi — istalgan summada buyurtma qabul qilinadi.")
        else:
            bot.send_message(message.chat.id,
                f"✅ Endi «{BUILDER_CATEGORY}» bo'limidan yig'ilgan taom "
                f"{fmt_sum(v)} dan kam bo'lsa qabul qilinmaydi.")
        return

    nechta = sum(1 for d in load_menu()
                 if (d.get("category") or DEFAULT_CATEGORY) == BUILDER_CATEGORY)
    bot.send_message(message.chat.id,
        f"\U0001F371 {BUILDER_CATEGORY}\n\n"
        f"Eng kam summa: {fmt_sum(builder_min())}\n"
        f"Bo'limdagi mahsulotlar: {nechta} ta\n\n"
        "Mijoz shu bo'limdan o'zi taom yig'adi. Agar butun buyurtma shu bo'limdan "
        "iborat bo'lsa, jami shu summadan kam bo'lmasligi kerak. Boshqa taom ham "
        "olingan bo'lsa, chegara qo'llanmaydi.\n\n"
        "O'zgartirish: /yigma 30\n"
        "O'chirish: /yigma 0\n\n"
        "Mahsulot qo'shish: «Menyuni boshqarish» → kategoriya "
        f"«{BUILDER_CATEGORY}».")

@bot.message_handler(commands=["qolda", "tel", "manual"])
def cmd_manual_order(message):
    """Telefon orqali kelgan buyurtmani darhol yozib qo'yish.

    Forward kerak emas — bo'sh qoralama ochiladi, savatni o'zingiz yig'asiz.
    """
    if not is_staff_or_admin(message.chat.id):
        return
    if not WEBAPP_URL:
        bot.send_message(message.chat.id, "WEBAPP_URL sozlanmagan.")
        return
    admin_id = message.chat.id
    token = hashlib.md5(f"qolda:{admin_id}:{time.time()}".encode()).hexdigest()[:12]
    izoh = (message.text or "").split(maxsplit=1)
    d = {"admin_id": admin_id, "manual": True}
    if len(izoh) > 1 and izoh[1].strip():
        d["text"] = izoh[1].strip()[:900]
        tel = extract_phone(izoh[1])
        if tel:
            d["phone"] = tel
    tgdraft_put(token, d)
    bot.send_message(admin_id,
        "\U0001F4DE Telefon buyurtmasi\n\n"
        "Pastdagi tugmani bosing: mijoz ma'lumotini yozasiz va savatni yig'asiz.\n"
        "Kilogramm bilan sotiladigan narsalar uchun sahifada "
        "\u00abQo'lda qo'shish\u00bb bo'limi bor — nomi, miqdori va narxini yozasiz.\n\n"
        "\u26A0\ufe0f Bu buyurtmaga keshbek yozilmaydi.",
        reply_markup=tgdraft_kb(token, admin_id,
                                message.from_user.username if message.from_user else None))

@bot.message_handler(commands=["cheklar", "checks"])
def cmd_checks(message):
    """Bugungi buyurtmalar oshxona ro‘yxatida bormi — shuni ko‘rsatadi.

    Oshxona sahifasiga faqat printed=False bo‘lgan buyurtmalar tushadi.
    Shuning uchun “buyurtma keldi, lekin chek yo‘q” bo‘lsa, sabab shu yerdan ko‘rinadi.
    """
    if not is_owner(message.chat.id):
        return
    parts = (message.text or "").split()
    arg = parts[1].lower() if len(parts) > 1 else ""
    day = today_key()

    if arg in ("qayta", "again", "reset"):
        only = None
        if len(parts) > 2 and parts[2].lstrip("#").isdigit():
            only = int(parts[2].lstrip("#"))
        with DATA_LOCK:
            orders = load_orders()
            n = 0
            for o in orders:
                if o.get("day_key") != day or is_cancelled(o):
                    continue
                if only is not None and o.get("daily_number") != only:
                    continue
                if o.get("printed"):
                    o["printed"] = False
                    n += 1
            if n:
                save_orders(orders)
        if n:
            bot.send_message(message.chat.id,
                f"♻️ {n} ta buyurtma oshxona ro‘yxatiga qaytarildi. "
                "Oshxona sahifasini oching — cheklar ko‘rinadi.")
        else:
            bot.send_message(message.chat.id, "Qaytariladigan buyurtma topilmadi.")
        return

    today_orders = [o for o in load_orders() if o.get("day_key") == day]
    if not today_orders:
        bot.send_message(message.chat.id,
            f"Bugun ({day}) hali buyurtma yo‘q.\n\n"
            "Eslatma: oshxona ro‘yxatida faqat <b>bugungi</b> buyurtmalar ko‘rinadi. "
            "Kechagisini ko‘rish uchun oshxona sahifasidagi «Qayta chiqarish» ishlamaydi — "
            "u ham faqat bugungi raqamlar bilan ishlaydi.", parse_mode="HTML")
        return

    today_orders.sort(key=lambda o: o.get("daily_number") or 0)
    rows, waiting = [], 0
    for o in today_orders:
        if is_cancelled(o):
            mark = "❌ bekor"
        elif o.get("printed"):
            mark = "✅ chiqarilgan"
        else:
            mark = "⏳ navbatda"
            waiting += 1
        rows.append(f"#{o.get('daily_number')} {o.get('customer_name') or '-'} "
                    f"— {fmt_sum(o.get('total', 0))} — {mark}")

    txt = (f"\U0001F9FE Bugungi cheklar ({day})\n\n" + "\n".join(rows) +
           f"\n\nOshxona ro‘yxatida ko‘rinadigani: {waiting} ta")
    if waiting == 0:
        txt += ("\n\n⚠️ Hammasi “chiqarilgan” deb belgilangan, shuning uchun "
                "oshxona bo‘limi bo‘sh ko‘rinadi.\n"
                "Qaytarish: /cheklar qayta  (yoki bittasi: /cheklar qayta 3)")
    bot.send_message(message.chat.id, txt)

# ======================================================================
#  TELEGRAM BUSINESS — shaxsiy akkauntdagi mijozlarga botning javobi
#
#  Telegram Premium bo'lsa, bot egasining SHAXSIY chatiga ulanadi va
#  mijoz yozganda tugmali javob yuboradi. Egasi istalgan paytda
#  suhbatga o'zi qo'shiladi — bot unga xalaqit qilmaydi.
# ======================================================================

BIZ_DEFAULT_TEXT = (
    "Assalomu alaykum! 🕌\n"
    "{biz} — halol, lazzatli, barakali ne'mat.\n\n"
    "Menyu, narxlar va yetkazib berish — hammasi quyidagi tugmada. "
    "Savolingiz bo'lsa shu yerga yozavering, javob beramiz."
)

def biz_cfg():
    s = load_settings()
    return {
        "conn": s.get("biz_conn"),
        "owner": s.get("biz_owner"),
        "on": bool(s.get("biz_on", True)),
        "text": s.get("biz_text") or BIZ_DEFAULT_TEXT,
        "cooldown": int(s.get("biz_cooldown", 6)),      # soat
    }

def biz_set(**kw):
    with DATA_LOCK:
        s = load_settings()
        s.update(kw)
        save_settings(s)

def biz_seen_ok(uid, hours):
    """Shu mijozga yaqinda javob berilganmi. Berilmagan bo'lsa True va belgilaydi."""
    now = int(time.time())
    with DATA_LOCK:
        data = load_json(BIZSEEN_FILE, {})
        oxirgi = int(data.get(str(uid), 0))
        if now - oxirgi < hours * 3600:
            return False
        data[str(uid)] = now
        # ro'yxat cheksiz o'smasin
        if len(data) > 3000:
            eski = sorted(data.items(), key=lambda x: x[1])[:1000]
            for k, _ in eski:
                data.pop(k, None)
        save_json(BIZSEEN_FILE, data)
    return True

def biz_keyboard():
    """Mijoz ko'radigan tugma. Business chatda web_app emas, havola ishlaydi."""
    kb = types.InlineKeyboardMarkup()
    links = start_links("dm")
    url = links.get("app") or links.get("start")
    if url:
        kb.add(types.InlineKeyboardButton("🍽 Menyu va buyurtma berish", url=url))
    return kb if url else None

def biz_reply_text():
    return biz_cfg()["text"].replace("{biz}", BUSINESS_NAME)

BIZ_SUPPORTED = hasattr(bot, "business_message_handler")

if hasattr(bot, "business_connection_handler"):
    @bot.business_connection_handler(func=lambda c: True)
    def on_business_connection(conn):
        """Egasi botni o'z akkauntiga uladi yoki uzdi."""
        try:
            faol = getattr(conn, "is_enabled", None)
            if faol is None:
                faol = getattr(conn, "rights", None) is not None
            uid = getattr(getattr(conn, "user", None), "id", None)
            biz_set(biz_conn=conn.id if faol else None, biz_owner=uid)
            if uid:
                bot.send_message(uid,
                    ("✅ Bot shaxsiy akkauntingizga ulandi.\n\n"
                     "Endi mijoz sizga yozganda bot tugmali javob yuboradi. "
                     "Sozlash: /biznes") if faol else
                    "ℹ️ Bot shaxsiy akkauntingizdan uzildi.")
        except Exception as e:
            print(f"Business ulanishida xato: {e}")

if BIZ_SUPPORTED:
    @bot.business_message_handler(func=lambda m: True)
    def on_business_message(message):
        """Mijoz egasining shaxsiy chatiga yozdi."""
        try:
            cfg = biz_cfg()
            if not cfg["on"]:
                return
            conn = getattr(message, "business_connection_id", None)
            if not conn:
                return
            uid = getattr(message.from_user, "id", None)
            if not uid:
                return
            if getattr(message.from_user, "is_bot", False):
                return
            # Shaxsiy chatda chat.id \u2014 mijozning id si. Agar xabarni
            # yozgan odam mijoz bo'lmasa, demak buni egasining o'zi yozgan.
            # Shunda javob bermaymiz va egasining id sini eslab qolamiz.
            if uid != getattr(message.chat, "id", None):
                if not cfg.get("owner"):
                    biz_set(biz_owner=uid)
                return
            if cfg.get("owner") and uid == cfg["owner"]:
                return
            # ulanish id sini bilmasak, shu xabardan olib qo'yamiz
            if not cfg.get("conn"):
                biz_set(biz_conn=conn)
            if not biz_seen_ok(uid, cfg["cooldown"]):
                return
            add_known_user(message.from_user)
            bot.send_message(message.chat.id, biz_reply_text(),
                             reply_markup=biz_keyboard(),
                             business_connection_id=conn)
        except Exception as e:
            print(f"Business xabariga javobda xato: {e}")

@bot.message_handler(commands=["biznes", "business"])
def cmd_business(message):
    """Shaxsiy akkauntdagi avtomatik javobni boshqarish."""
    if not is_owner(message.chat.id):
        return
    parts = (message.text or "").split(maxsplit=1)
    arg = (parts[1].strip() if len(parts) > 1 else "")
    past = arg.lower()

    if past in ("on", "yoq", "yoqish"):
        biz_set(biz_on=True)
        bot.send_message(message.chat.id, "✅ Shaxsiy chatdagi avtomatik javob yoqildi.")
        return
    if past in ("off", "ochir", "o'chir", "o‘chir"):
        biz_set(biz_on=False)
        bot.send_message(message.chat.id, "⏸ Avtomatik javob o'chirildi.")
        return
    if past.startswith("matn"):
        yangi = arg[4:].strip()
        if not yangi:
            bot.send_message(message.chat.id,
                "Matnni ham yozing:\n/biznes matn Assalomu alaykum! ...\n\n"
                "{biz} deb yozsangiz, o'rniga biznes nomi qo'yiladi.")
            return
        biz_set(biz_text=yangi[:900])
        bot.send_message(message.chat.id, "✅ Matn saqlandi. Hozirgi ko'rinishi:")
        bot.send_message(message.chat.id, biz_reply_text(), reply_markup=biz_keyboard())
        return
    if past.startswith("soat"):
        try:
            h = int(arg.split()[1])
        except Exception:
            bot.send_message(message.chat.id, "Masalan: /biznes soat 6")
            return
        biz_set(biz_cooldown=max(0, min(168, h)))
        bot.send_message(message.chat.id,
            f"✅ Bitta mijozga {max(0, min(168, h))} soatda bir marta javob beriladi.")
        return

    cfg = biz_cfg()
    if not BIZ_SUPPORTED:
        bot.send_message(message.chat.id,
            "⚠️ Serverdagi telebot kutubxonasi eski — Business xabarlarini "
            "qo'llab-quvvatlamaydi.\n\nrequirements.txt faylida "
            "`pyTelegramBotAPI>=4.22` deb yozing va qayta deploy qiling.")
        return

    holat = "🟢 ulangan" if cfg["conn"] else "🔴 ulanmagan"
    javob_holati = "yoqilgan" if cfg["on"] else "o'chirilgan"
    txt = ("💼 Telegram Business — shaxsiy akkaunt\n\n"
           f"Ulanish: {holat}\n"
           f"Avtomatik javob: {javob_holati}\n"
           f"Takrorlash oralig'i: {cfg['cooldown']} soat\n\n")
    if not cfg["conn"]:
        txt += ("Ulash uchun telefoningizda:\n"
                "Sozlamalar → Telegram Business → Chatbots → "
                f"@{bot_username() or 'botingiz'} → ruxsatlarni bering.\n\n"
                "Telegram Premium kerak.\n\n")
    txt += ("Hozirgi javob matni:\n— — —\n" + biz_reply_text() +
            "\n— — —\n\n"
            "Boshqarish:\n"
            "/biznes matn <yangi matn> — javobni o'zgartirish\n"
            "/biznes soat 6 — bitta mijozga necha soatda bir marta\n"
            "/biznes off — vaqtincha o'chirish | /biznes on — yoqish")
    bot.send_message(message.chat.id, txt, reply_markup=biz_keyboard())

@bot.message_handler(commands=["havola", "link"])
def cmd_invite_link(message):
    """Shaxsiy akkauntdan mijozni botga olib o\u2018tish uchun havolalar."""
    if not is_owner(message.chat.id):
        return
    parts = (message.text or "").split()
    payload = re.sub(r"[^A-Za-z0-9_\-]", "", parts[1])[:32] if len(parts) > 1 else "dm"
    payload = payload or "dm"

    u = bot_username()
    if not u:
        bot.send_message(message.chat.id,
            "Botning @nomini aniqlay olmadim. Railway\u2019da BOT_USERNAME "
            "o\u2018zgaruvchisiga bot nomini yozing (masalan: miqotfoodbuyurtmabot).")
        return

    links = start_links(payload)
    nusxa = ("Assalomu alaykum! Buyurtmani shu yerdan berasiz \u2014 "
             "menyu, narxlar va yetkazib berish hammasi botda:\n"
             + (links.get("app") or links["start"]))

    txt = ("\U0001F517 Mijozni botga olib o\u2018tish\n\n"
           "Shaxsiy akkauntdan tugma yuborib bo\u2018lmaydi \u2014 inline tugmalarni "
           "faqat botlar yubora oladi. Uning o\u2018rniga havola yuboriladi, "
           "mijoz bossa bot ochiladi.\n\n"
           "1\ufe0f\u20e3 Oddiy havola (mijoz START bosadi):\n"
           f"`{links['start']}`\n\n")
    if links.get("app"):
        txt += ("2\ufe0f\u20e3 Mini App to\u2018g\u2018ridan-to\u2018g\u2018ri ochiladi (bitta bosish):\n"
                f"`{links['app']}`\n\n")
    else:
        txt += ("2\ufe0f\u20e3 Mini App\u2019ni bir bosishda ochadigan havola hozircha yo\u2018q.\n"
                "Buning uchun BotFather \u2192 /mybots \u2192 botingiz \u2192 Bot Settings \u2192 "
                "Configure Mini App \u2192 Enable \u2014 u yerda qisqa nom beriladi. "
                "So\u2018ng Railway\u2019da MINIAPP_NAME o\u2018zgaruvchisiga o\u2018sha nomni yozing, "
                "shunda bu yerda ikkinchi havola ham chiqadi.\n\n")

    txt += ("\u2702\ufe0f Mijozga yuborish uchun tayyor matn:\n\n"
            f"{nusxa}\n\n"
            "\U0001F4A1 Telegram\u2019da bu matnni \u00abSaqlangan xabarlar\u00bb ga qo\u2018yib "
            "qo\u2018ysangiz, har safar nusxalab yuborish oson bo\u2018ladi.\n\n"
            f"Hisobot: /havola_hisobot \u2014 shu havola orqali nechta mijoz kelgani.\n"
            f"Boshqa belgi bilan: /havola instagram")
    bot.send_message(message.chat.id, txt, parse_mode="Markdown",
                     disable_web_page_preview=True)

@bot.message_handler(commands=["havola_hisobot", "link_report"])
def cmd_invite_report(message):
    """Qaysi havola orqali nechta mijoz kelgan."""
    if not is_owner(message.chat.id):
        return
    sanoq = {}
    for rec in load_users().values():
        s = rec.get("src")
        if s:
            sanoq[s] = sanoq.get(s, 0) + 1
    if not sanoq:
        bot.send_message(message.chat.id,
            "Hozircha havola orqali kelgan mijoz yo\u2018q.\n"
            "Havolani olish: /havola")
        return
    satrlar = [f"  {k} \u2014 {v} ta" for k, v in sorted(sanoq.items(), key=lambda x: -x[1])]
    bot.send_message(message.chat.id,
        "\U0001F517 Havola orqali kelgan mijozlar\n\n" + "\n".join(satrlar) +
        f"\n\nJami: {sum(sanoq.values())} ta")

@bot.message_handler(commands=["oshxona", "kitchen"])
def cmd_kitchen_link(message):
    """Oshxona sahifasining havolasi — Chrome'da ochish uchun.

    Telegram ichidagi brauzer (ayniqsa Androidda) Bluetooth'ga ruxsat bermaydi,
    shuning uchun havolani alohida berib qo'yamiz.
    """
    if not is_owner(message.chat.id):
        return
    if not WEBAPP_URL:
        bot.send_message(message.chat.id, "WEBAPP_URL sozlanmagan.")
        return
    uid = message.chat.id
    uname = message.from_user.username if message.from_user else None
    ts, sig = sign_user_params(uid, uname)
    params = f"uid={uid}&uname={urllib.parse.quote(uname or '')}&ts={ts}&sig={sig}&v={ts}"
    link = f"{WEBAPP_URL}/kitchen?{params}"
    bot.send_message(message.chat.id,
        "\U0001F5A8 Oshxona sahifasi havolasi:\n\n"
        f"`{link}`\n\n"
        "Telefonda Bluetooth printer ishlashi uchun shuni *Chrome*da oching — "
        "Telegram ichidagi brauzerda Bluetooth yopiq.\n\n"
        "Keyin Chrome menyusidan «Asosiy ekranga qo‘shish» ni tanlang, "
        "shunda har safar shu ikonkadan ochasiz.",
        parse_mode="Markdown", disable_web_page_preview=True)

@bot.message_handler(commands=["versiya", "version"])
def cmd_version(message):
    """Serverdagi kod qachon yangilangani — deploy yetib keldimi, shundan bilinadi."""
    if not is_owner(message.chat.id):
        return
    bot.send_message(message.chat.id,
        f"\U0001F6E0 Kod versiyasi: {APP_VERSION}\n"
        f"Server vaqti: {datetime.now(TIMEZONE).strftime('%d.%m.%Y %H:%M')}\n\n"
        "Agar versiya siz yuklagan vaqtdan eski bo'lsa — Railway hali yangi kodni "
        "ishga tushirmagan. Deploy tugashini kuting yoki Railway'da xatolik bor-yo'qligini qarang.\n\n"
        "Versiya to'g'ri, lekin o'zgarish ko'rinmasa — Telegram eski sahifani ko'rsatyapti: "
        "botga /start yuboring va tugmani yangi xabardan bosing.")

@bot.message_handler(commands=["keshbek", "cashback"])
def cmd_cashback(message):
    """Mijoz uchun — o'z balansi. Admin uchun — umumiy holat."""
    cfg = get_cashback_cfg()
    lang = get_user_lang(message.from_user.id, getattr(message.from_user, "language_code", None))
    parts = (message.text or "").split()

    if is_owner(message.chat.id):
        arg = parts[1] if len(parts) > 1 else ""

        # to'liq ro'yxat — uzun bo'lsa fayl qilib yuboramiz
        if arg.lower() in ("royxat", "ro'yxat", "list", "hammasi"):
            holders = cashback_holders()
            if not holders:
                bot.send_message(message.chat.id, "Hozircha hech kimda keshbek yo'q.")
                return
            jami = money(sum(h[1] for h in holders))
            if len(holders) <= 40:
                lines = [f"\U0001F4B3 Keshbegi bor mijozlar: {len(holders)} ta",
                         f"Jami: {fmt_sum(jami)}", ""]
                lines += [cashback_holder_line(*h) for h in holders]
                bot.send_message(message.chat.id, "\n".join(lines))
            else:
                import csv, io as _io
                buf = _io.StringIO()
                w = csv.writer(buf)
                w.writerow(["user_id", "ism", "username", "balans", "jami_yozilgan",
                            "jami_ishlatilgan"])
                cb = load_cashback()
                for uid, bal, name, uname in holders:
                    rec = cb.get(str(uid)) or {}
                    w.writerow([uid, name, uname, f"{bal:.2f}",
                                f"{money(rec.get('earned', 0)):.2f}",
                                f"{money(rec.get('spent', 0)):.2f}"])
                data = buf.getvalue().encode("utf-8-sig")
                doc = _io.BytesIO(data)
                doc.name = f"keshbek-{datetime.now(TIMEZONE).strftime('%Y-%m-%d')}.csv"
                try:
                    bot.send_document(
                        message.chat.id, doc,
                        caption=(f"\U0001F4B3 Keshbegi bor mijozlar: {len(holders)} ta\n"
                                 f"Jami: {fmt_sum(jami)}\n\n"
                                 "Excel yoki Google Sheets'da ochsangiz bo'ladi."))
                except Exception as e:
                    print(f"Keshbek ro'yxatini yuborishda xato: {e}")
                    lines = [cashback_holder_line(*h) for h in holders[:40]]
                    bot.send_message(message.chat.id,
                                     "\n".join(lines) + f"\n\n… va yana {len(holders) - 40} ta")
            return

        if arg:
            try:
                target = int(arg)
            except ValueError:
                hits = cashback_find_user(arg)        # @username yoki ism bo'yicha qidiramiz
                if len(hits) == 1:
                    target = hits[0]
                elif not hits:
                    bot.send_message(message.chat.id,
                        f"\u00ab{arg}\u00bb bo'yicha mijoz topilmadi.\n\n"
                        "Foydalanish:\n/keshbek \u2014 umumiy holat\n"
                        "/keshbek royxat \u2014 kimda qancha bor\n"
                        "/keshbek <user_id yoki @username>")
                    return
                else:
                    users = load_users()
                    lines = ["Bir nechta mijoz topildi, ID sini tanlang:", ""]
                    for h in hits[:15]:
                        u = users.get(str(h)) or {}
                        kim = (u.get("name") or "Ism yo'q")
                        if u.get("username"):
                            kim += f" @{u['username']}"
                        lines.append(f"/keshbek {h} \u2014 {kim}")
                    bot.send_message(message.chat.id, "\n".join(lines))
                    return
            rec = load_cashback().get(str(target)) or {}
            u = load_users().get(str(target)) or {}
            kim = (u.get("name") or "").strip() or "Ism yo'q"
            if u.get("username"):
                kim += f" @{u['username']}"
            hist = (rec.get("history") or [])[-8:]
            lines = [f"\U0001F4B3 {kim}",
                     f"ID: {target}",
                     f"Balans: {fmt_sum(rec.get('balance', 0))}",
                     f"Jami yozilgan: {fmt_sum(rec.get('earned', 0))}",
                     f"Jami ishlatilgan: {fmt_sum(rec.get('spent', 0))}"]
            if hist:
                lines.append("")
                lines.append("Oxirgi harakatlar:")
                for h in reversed(hist):
                    when = datetime.fromtimestamp(h.get("ts", 0), TIMEZONE).strftime("%d.%m %H:%M")
                    sign = "+" if h.get("delta", 0) > 0 else "\u2212"
                    lines.append(f"  {when}  {sign}{fmt_sum(abs(h.get('delta', 0)))}  {h.get('note', '')}")
            bot.send_message(message.chat.id, "\n".join(lines))
            return
        tot = cashback_totals()
        state = f"\U0001F7E2 yoqilgan — {cfg['percent']:g}%" if cfg["active"] else "\u23F9 o'chirilgan"
        holders = cashback_holders()
        top_text = ""
        if holders:
            top_text = "Eng ko'p yig'ilganlar:\n"
            top_text += "\n".join("  " + cashback_holder_line(*h) for h in holders[:10])
            if len(holders) > 10:
                top_text += f"\n  \u2026 va yana {len(holders) - 10} ta"
            top_text += "\n\n"
        bot.send_message(message.chat.id,
            "\U0001F4B3 Keshbek holati\n\n"
            f"Sozlama: {state}\n"
            f"Mijozlarda yig'ilgan: {fmt_sum(tot['balance'])}\n"
            f"Keshbegi bor mijozlar: {tot['people']} ta\n\n"
            + top_text +
            "Boshqarish:\n"
            "/keshbek royxat \u2014 to'liq ro'yxat\n"
            "/keshbek <user_id yoki @username> \u2014 bitta mijoz\n"
            "/keshbek_foiz 5 \u2014 foizni o'zgartirish\n"
            "/keshbek_foiz 0 \u2014 keshbekni butunlay o'chirish")
        return

    if not cfg["active"]:
        bot.send_message(message.chat.id, t("cb_off", lang))
        return
    bal = cashback_balance(message.from_user.id)
    key = "cb_balance" if bal > 0 else "cb_zero"
    bot.send_message(message.chat.id, t(key, lang, bal=fmt_sum(bal), pct=f"{cfg['percent']:g}"),
                     reply_markup=main_keyboard(message.from_user.id, message.from_user.username))

@bot.message_handler(commands=["hisob", "nasiya", "account"])
def cmd_account(message):
    """Mijoz hisobi: nasiya (minus) va avans (plyus).

    Mijoz uchun \u2014 o\'z balansi.
    Admin uchun \u2014 ro\'yxat, bitta mijoz, pul qo\'shish va yechish.
    """
    parts = (message.text or "").split()
    owner = is_owner(message.chat.id)

    # ----- mijoz o\'z hisobini ko\'radi -----
    if not owner:
        lang = get_user_lang(message.from_user.id)
        bal = account_balance(message.from_user.id)
        if bal < 0:
            txt = t("acct_my_debt", lang, bal=fmt_signed(bal), amt=fmt_sum(-bal))
        elif bal > 0:
            txt = t("acct_my_adv", lang, bal=fmt_signed(bal), amt=fmt_sum(bal))
        else:
            txt = t("acct_my_zero", lang)
        # oxirgi harakatlar — raqamning orqasi ko'rinib tursin, bahs bo'lmasin
        hist = account_history(message.from_user.id, 8)
        if hist:
            satrlar = []
            for h in hist:
                vaqt = datetime.fromtimestamp(h.get("ts", 0), TIMEZONE).strftime("%d.%m")
                izoh = h.get("note") or ""
                satrlar.append(f"  {vaqt}  {fmt_signed(h.get('delta', 0))}"
                               + (f"  — {izoh}" if izoh else ""))
            txt += "\n\n" + t("acct_my_hist", lang) + "\n" + "\n".join(satrlar)
        bot.send_message(message.chat.id, txt,
                         reply_markup=main_keyboard(message.from_user.id,
                                                    message.from_user.username, lang))
        return

    # ----- admin: pul qo\'shish / yechish -----
    if len(parts) >= 4 and parts[1] in ("+", "-", "\u2212"):
        kim = parts[2]
        try:
            amount = money(float(parts[3].replace(",", ".")))
        except Exception:
            bot.send_message(message.chat.id, "Summani to\u2018g\u2018ri yozing: /hisob + @ali 100")
            return
        if amount <= 0:
            bot.send_message(message.chat.id, "Summa noldan katta bo\u2018lsin.")
            return
        izoh = " ".join(parts[4:]).strip()

        if kim.lstrip("-").isdigit():
            hits = [int(kim)]
        else:
            hits = cashback_find_user(kim)
        if not hits:
            bot.send_message(message.chat.id, f"\u00ab{kim}\u00bb bo\u2018yicha mijoz topilmadi.")
            return
        if len(hits) > 1:
            users = load_users()
            ro = "\n".join(f"  {(users.get(str(h)) or {}).get('name') or 'Ism yo\u2018q'} \u2014 {h}"
                            for h in hits[:10])
            bot.send_message(message.chat.id,
                             f"Bir nechta mijoz topildi, ID bilan yozing:\n{ro}")
            return

        uid = hits[0]
        delta = amount if parts[1] == "+" else -amount
        bal = account_move(uid, delta, None, izoh or ("to\u2018lov" if delta > 0 else "qo\u2018lda yechildi"))
        users = load_users()
        u = users.get(str(uid)) or {}
        nom = (u.get("name") or "").strip() or str(uid)
        bot.send_message(message.chat.id,
            f"\u2705 {nom}: {fmt_signed(delta)}\nYangi balans: {fmt_signed(bal)}")
        if delta > 0:
            try:
                lang = get_user_lang(uid)
                bot.send_message(uid, t("acct_paid", lang,
                                        amt=fmt_sum(delta), bal=fmt_signed(bal)))
            except Exception:
                pass
        return

    # ----- admin: bitta mijoz -----
    if len(parts) >= 2 and parts[1] not in ("royxat", "ro\u2018yxat", "list"):
        kim = parts[1]
        hits = [int(kim)] if kim.lstrip("-").isdigit() else cashback_find_user(kim)
        if not hits:
            bot.send_message(message.chat.id, f"\u00ab{kim}\u00bb bo\u2018yicha mijoz topilmadi.")
            return
        users = load_users()
        bloklar = []
        for uid in hits[:5]:
            u = users.get(str(uid)) or {}
            bal = account_balance(uid)
            rec = (load_account().get(str(uid)) or {})
            hist = (rec.get("history") or [])[-8:]
            satrlar = []
            for h in reversed(hist):
                vaqt = datetime.fromtimestamp(h.get("ts", 0), TIMEZONE).strftime("%d.%m %H:%M")
                nomer = f" #{h['order_id']}" if h.get("order_id") else ""
                satrlar.append(f"  {vaqt}{nomer}  {fmt_signed(h.get('delta', 0))}"
                               f"  \u2192 {fmt_signed(h.get('bal', 0))}"
                               + (f"  ({h['note']})" if h.get("note") else ""))
            bloklar.append(
                account_line(uid, bal, (u.get("name") or "").strip(), u.get("username") or "")
                + ("\n" + "\n".join(satrlar) if satrlar else "\n  (harakat yo\u2018q)"))
        bot.send_message(message.chat.id, "\n\n".join(bloklar))
        return

    # ----- admin: umumiy ro\'yxat -----
    tot = account_totals()
    holders = account_holders()
    qarzdorlar = [h for h in holders if h[1] < 0]
    avanslilar = [h for h in holders if h[1] > 0]

    txt = ("\U0001F4D2 Mijozlar hisobi\n\n"
           f"\U0001F534 Nasiya: {fmt_sum(tot['debt'])} \u2014 {tot['debtors']} ta mijoz\n"
           f"\U0001F7E2 Avans: {fmt_sum(tot['advance'])} \u2014 {tot['advanced']} ta mijoz\n")
    if qarzdorlar:
        txt += "\nQarzdorlar:\n" + "\n".join(account_line(*h) for h in qarzdorlar[:20])
        if len(qarzdorlar) > 20:
            txt += f"\n  ...va yana {len(qarzdorlar) - 20} ta"
    if avanslilar:
        txt += "\n\nAvansi borlar:\n" + "\n".join(account_line(*h) for h in avanslilar[:20])
        if len(avanslilar) > 20:
            txt += f"\n  ...va yana {len(avanslilar) - 20} ta"
    if not holders:
        txt += "\nHozircha nol bo\u2018lmagan hisob yo\u2018q."
    txt += ("\n\nBoshqarish:\n"
            "/hisob + @ali 100 \u2014 to\u2018lov yoki avans qo\u2018shish\n"
            "/hisob - @ali 50 \u2014 qo\u2018lda yechish\n"
            "/hisob @ali \u2014 bitta mijoz va tarixi\n\n"
            "Buyurtmani nasiyaga yozish: buyurtma xabaridagi "
            "\u00abHisobga yozish\u00bb tugmasi.")
    uname = message.from_user.username if message.from_user else None
    bot.send_message(message.chat.id, txt,
                     reply_markup=hisob_webapp_kb(message.chat.id, uname))

@bot.message_handler(commands=["keshbek_foiz"])
def cmd_cashback_percent(message):
    if not is_owner(message.chat.id):
        return
    parts = (message.text or "").split()
    if len(parts) < 2:
        cfg = get_cashback_cfg()
        bot.send_message(message.chat.id,
                         f"Hozirgi keshbek: {cfg['percent']:g}%\n"
                         "O'zgartirish: /keshbek_foiz 5\nO'chirish: /keshbek_foiz 0")
        return
    try:
        pct = float(parts[1].replace(",", "."))
    except ValueError:
        bot.send_message(message.chat.id, "Raqam kiriting. Masalan: /keshbek_foiz 5")
        return
    if pct < 0 or pct > 100:
        bot.send_message(message.chat.id, "Foiz 0 dan 100 gacha bo'lishi kerak.")
        return
    cfg = set_cashback_cfg(active=pct > 0, percent=pct)
    if cfg["active"]:
        bot.send_message(message.chat.id,
            f"\u2705 Keshbek {cfg['percent']:g}% qilib qo'yildi.\n\n"
            "Bu faqat bundan keyingi yetkazilgan buyurtmalarga ta'sir qiladi — "
            "mijozlarda yig'ilib turgan keshbek joyida qoladi.")
    else:
        bot.send_message(message.chat.id,
            "\u23F9 Keshbek o'chirildi. Yangi buyurtmalardan keshbek yozilmaydi.\n\n"
            "Mijozlardagi eski keshbek saqlanib qoladi, lekin ular uni ishlata olmaydi. "
            "Qayta yoqish: /keshbek_foiz 5")

@bot.message_handler(commands=["yesterday_report"])
def cmd_yesterday_report(message):
    if not is_owner(message.chat.id):
        return
    yday = datetime.now(TIMEZONE).date() - timedelta(days=1)
    bot.send_message(message.chat.id, build_daily_report_text(yday))

def daily_report_scheduler():
    """Har kuni 00:00 da (TIMEZONE bo'yicha) o'tgan kunning hisobotini yuboradi."""
    last_sent_date = None
    while True:
        try:
            now = datetime.now(TIMEZONE)
            if now.hour == 0 and now.minute == 0 and last_sent_date != now.date():
                yesterday = now.date() - timedelta(days=1)
                send_daily_report(yesterday)
                last_sent_date = now.date()
        except Exception as e:
            print(f"Kunlik hisobot xatosi: {e}")
        time.sleep(30)

# ---------- viktorina: mijoz tomoni ----------

QUIZ_BTN = "🎁 Viktorina"
BOARD_BTN = "🏆 Natijalar"

def quiz_question_keyboard(qi, options):
    kb = types.InlineKeyboardMarkup(row_width=1)
    for i, o in enumerate(options):
        label = o if len(o) <= 60 else o[:59] + "…"
        kb.add(types.InlineKeyboardButton(label, callback_data=f"qz:{qi}:{i}"))
    return kb

def send_quiz_question(chat_id, user_id, quiz):
    """Savolni yuboradi va yuborilgan vaqtni qulf ostida yozib qo'yadi."""
    with DATA_LOCK:
        results = load_quiz_results()
        res = results.get(str(user_id))
        if not res or res.get("done"):
            return
        qi = res["idx"]
    if qi >= len(quiz["questions"]):
        return
    item = quiz["questions"][qi]
    total = len(quiz["questions"])
    text = (f"❓ {qi + 1}/{total}\n\n{item['q']}\n\n"
            "⏱ Tezlik ham hisobga olinadi — o'ylab, lekin shoshilib javob bering.")
    bot.send_message(chat_id, text, reply_markup=quiz_question_keyboard(qi, item["options"]))
    with DATA_LOCK:
        results = load_quiz_results()
        r = results.get(str(user_id))
        if r and not r.get("done") and r.get("idx") == qi:
            r["sent_at"] = int(time.time() * 1000)
            results[str(user_id)] = r
            save_quiz_results(results)

def quiz_result_text(user_id, res, quiz):
    board = quiz_leaderboard()
    place = next((i + 1 for i, r in enumerate(board) if r["uid"] == int(user_id)), None)
    total = len(quiz["questions"])
    lines = [
        "🏁 Viktorina tugadi!",
        "",
        f"✅ To'g'ri javoblar: {res['correct']} / {total}",
        f"⏱ Sarflangan vaqt: {fmt_secs(res['elapsed_ms'])}",
    ]
    if place:
        lines.append(f"📊 Hozirgi o'rningiz: {place}-o'rin ({len(board)} ta qatnashchi orasida)")
    if quiz.get("prize"):
        lines += ["", f"🎁 Sovg'a: {quiz['prize']}"]
    lines += ["", f"Umumiy jadvalni ko'rish uchun \"{BOARD_BTN}\" tugmasini bosing."]
    return "\n".join(lines)

def start_quiz(message):
    quiz = load_quiz()
    user = message.from_user
    add_known_user(user)
    uid = str(user.id)
    lang = get_user_lang(user.id, getattr(user, "language_code", None))

    if not quiz_visible_to(user.id):
        bot.send_message(message.chat.id, "Hozircha faol viktorina yo'q. Kanalimizni kuzatib turing 😊")
        return
    if quiz["test"]:
        bot.send_message(message.chat.id, "🧪 SINOV REJIMI — bu faqat sizga ko'rinyapti, mijozlar ko'rmayapti.")

    with DATA_LOCK:
        results = load_quiz_results()
        res = results.get(uid)
        yangi = False
        if not res:
            yangi = True
            res = {
                "name": (user.first_name or "Mijoz") + ((" " + user.last_name) if getattr(user, "last_name", None) else ""),
                "username": user.username,
                "idx": 0, "correct": 0, "elapsed_ms": 0,
                "started_at": int(time.time()), "sent_at": None,
                "done": False, "finished_at": None,
            }
            results[uid] = res
            save_quiz_results(results)
        tugagan = bool(res.get("done"))

    if tugagan:
        bot.send_message(
            message.chat.id,
            "Siz bu viktorinada allaqachon qatnashgansiz — har kim bir marta yechadi.\n\n"
            + quiz_result_text(uid, res, quiz)
        )
        return

    if yangi:
        intro = [f"🎁 {quiz['title']}", ""]
        intro.append(f"Savollar soni: {len(quiz['questions'])} ta")
        intro.append("Har kim faqat bir marta yechadi.")
        intro.append("G'olib eng ko'p to'g'ri javob bergan, teng bo'lsa — eng tez javob bergan bo'ladi.")
        if quiz.get("prize"):
            intro += ["", f"🏆 Sovg'a: {quiz['prize']}"]
        intro += ["", "Boshladik! 👇"]
        bot.send_message(message.chat.id, "\n".join(intro))
    else:
        bot.send_message(message.chat.id, "Viktorinani davom ettiramiz 👇")

    send_quiz_question(message.chat.id, user.id, quiz)

@bot.message_handler(func=lambda m: m.text == QUIZ_BTN)
def handle_quiz_button(message):
    start_quiz(message)

@bot.message_handler(commands=["viktorina_boshlash"])
def cmd_quiz_start(message):
    start_quiz(message)

@bot.callback_query_handler(func=lambda c: c.data.startswith("qz:"))
def cb_quiz_answer(call):
    quiz = load_quiz()
    uid = str(call.from_user.id)

    try:
        _, qi_str, choice_str = call.data.split(":")
        qi, choice = int(qi_str), int(choice_str)
    except Exception:
        bot.answer_callback_query(call.id)
        return
    if qi >= len(quiz["questions"]):
        bot.answer_callback_query(call.id, "Savol topilmadi.")
        return
    item = quiz["questions"][qi]
    ok = (choice == item["correct"])

    # --- holatni o'zgartirish: qulf ostida, bitta-bittadan ---
    with DATA_LOCK:
        results = load_quiz_results()
        res = results.get(uid)
        if not res or res.get("done"):
            bot.answer_callback_query(call.id, "Bu viktorina siz uchun tugagan.")
            return
        if qi != res["idx"]:
            bot.answer_callback_query(call.id, "Bu savol o'tib ketgan.")
            return

        now = int(time.time() * 1000)
        sent = res.get("sent_at") or now
        res["elapsed_ms"] = res.get("elapsed_ms", 0) + max(0, now - sent)
        if ok:
            res["correct"] = res.get("correct", 0) + 1
        res["idx"] = qi + 1
        tugadi = res["idx"] >= len(quiz["questions"])
        if tugadi:
            res["done"] = True
            res["finished_at"] = int(time.time())
            res["sent_at"] = None
        results[uid] = res
        save_quiz_results(results)
        res = dict(res)      # qulfdan tashqarida ishlatish uchun nusxa

    # javob berilgan savolni belgilab qo'yamiz — qayta bosib bo'lmaydi
    try:
        chosen = item["options"][choice]
        right = item["options"][item["correct"]]
        mark = (f"❓ {qi + 1}/{len(quiz['questions'])}\n\n{item['q']}\n\n"
                + (f"✅ To'g'ri: {chosen}" if ok else f"❌ Siz: {chosen}\n✅ To'g'risi: {right}"))
        bot.edit_message_text(mark, call.message.chat.id, call.message.message_id)
    except Exception:
        pass

    bot.answer_callback_query(call.id, "✅ To'g'ri!" if ok else "❌ Noto'g'ri")

    if tugadi:
        bot.send_message(call.message.chat.id, quiz_result_text(uid, res, quiz),
                         reply_markup=main_keyboard(call.from_user.id, call.from_user.username))
        for admin_id in load_admin_ids():
            try:
                who = f"@{res['username']}" if res.get("username") else res.get("name")
                bot.send_message(admin_id,
                    f"🎁 Viktorina: {res.get('name')} ({who}) tugatdi — "
                    f"{res['correct']}/{len(quiz['questions'])}, {fmt_secs(res['elapsed_ms'])}")
            except Exception:
                pass
        return

    send_quiz_question(call.message.chat.id, call.from_user.id, quiz)

def board_text(viewer_id=None):
    quiz = load_quiz()
    board = quiz_leaderboard()
    if not board:
        return "Hozircha hech kim viktorinani tugatmagan. Birinchi bo'ling! 🎯"
    total = len(quiz["questions"]) or 0
    medals = ["🥇", "🥈", "🥉"]
    lines = [f"🏆 {quiz['title']} — natijalar", ""]
    for i, r in enumerate(board[:10]):
        tag = medals[i] if i < 3 else f"{i+1}."
        lines.append(f"{tag} {r['name']} — {r['correct']}/{total} · {fmt_secs(r['ms'])}")
    lines.append("")
    lines.append(f"Jami qatnashchilar: {len(board)} ta")
    if viewer_id is not None:
        place = next((i + 1 for i, r in enumerate(board) if r["uid"] == int(viewer_id)), None)
        if place:
            me = board[place - 1]
            lines += ["", f"📊 Siz: {place}-o'rin — {me['correct']}/{total} · {fmt_secs(me['ms'])}"]
        else:
            lines += ["", f"Siz hali qatnashmagansiz — \"{QUIZ_BTN}\" tugmasini bosing."]
    if quiz.get("prize"):
        lines += ["", f"🎁 Sovg'a: {quiz['prize']}"]
    return "\n".join(lines)

@bot.message_handler(func=lambda m: m.text == BOARD_BTN)
def handle_board_button(message):
    bot.send_message(message.chat.id, board_text(message.from_user.id))

@bot.message_handler(commands=["natijalar"])
def cmd_board(message):
    bot.send_message(message.chat.id, board_text(message.from_user.id))

# ---------- mijoz bilan yozishish (support chat) ----------

support_message_map = {}  # (admin_chat_id, message_id) -> mijoz_user_id

@bot.message_handler(func=lambda m: m.text and is_contact_button(m.text))
def handle_contact_button(message):
    add_known_user(message.from_user)
    lang = get_user_lang(message.from_user.id, getattr(message.from_user, "language_code", None))
    bot.send_message(message.chat.id, t("contact_prompt", lang))

@bot.message_handler(commands=["til", "lang", "language"])
def cmd_lang(message):
    lang = get_user_lang(message.from_user.id, getattr(message.from_user, "language_code", None))
    bot.send_message(message.chat.id, t("lang_choose", lang), reply_markup=lang_keyboard())

@bot.message_handler(func=lambda m: m.text and is_my_account_button(m.text))
def btn_my_account(message):
    cmd_account(message)

@bot.message_handler(func=lambda m: m.text and is_lang_button(m.text))
def handle_lang_button(message):
    cmd_lang(message)

@bot.callback_query_handler(func=lambda c: c.data.startswith("setlang:"))
def cb_set_lang(call):
    code = call.data.split(":", 1)[1]
    if code not in SUPPORTED_LANGS:
        bot.answer_callback_query(call.id)
        return
    set_user_lang(call.from_user.id, code)
    bot.answer_callback_query(call.id, t("lang_saved", code))
    try:
        bot.edit_message_text(t("lang_saved", code) + " " + LANG_NAMES[code],
                              call.message.chat.id, call.message.message_id)
    except Exception:
        pass
    bot.send_message(call.message.chat.id, t("welcome", code, biz=BUSINESS_NAME),
                     reply_markup=main_keyboard(call.from_user.id, call.from_user.username, code))

@bot.message_handler(
    func=lambda m: (
        m.reply_to_message is not None
        and is_staff_or_admin(m.from_user.id)
        and (m.chat.id, m.reply_to_message.message_id) in support_message_map
    )
)
def handle_admin_reply(message):
    customer_id = support_message_map.get((message.chat.id, message.reply_to_message.message_id))
    if not customer_id:
        return
    if isinstance(customer_id, str) and customer_id.startswith("ig:"):
        res = ig_send_text(customer_id[3:], f"{BUSINESS_NAME}: {message.text}")
        bot.send_message(message.chat.id, "✅ Javob Instagram'ga yuborildi." if res
                         else "❌ Yuborilmadi (Instagram 24 soatlik oyna yopilgan bo'lishi mumkin).")
        return
    try:
        clang = get_user_lang(customer_id)
        bot.send_message(customer_id, t("reply_from", clang, biz=BUSINESS_NAME) + f"\n{message.text}")
        bot.send_message(message.chat.id, "✅ Javobingiz mijozga yuborildi.")
    except Exception:
        bot.send_message(message.chat.id, "❌ Yuborib bo'lmadi — mijoz botni bloklagan bo'lishi mumkin.")

# "menyu?" degan so'rovni tanish uchun so'zlar.
# KUCHLI — bu so'z bo'lsa aniq menyu so'ralgan.
MENU_WORDS_STRONG = [
    "menyu", "menu", "menyusi", "menyuni", "menyular",
    "меню", "менью", "миню",
    "narx", "narxi", "narxlar", "narxlari", "necha pul", "qancha turadi",
    "цена", "цены", "почем", "почём", "price", "prices", "how much",
    "منيو", "المنيو", "قائمة", "القائمة", "الاسعار", "الأسعار", "اسعار",
    "مینو", "قیمت", "قیمتیں", "ریٹ",
    "fiyat", "fiyatlar", "harga", "daftar menu",
]
# KUCHSIZ — faqat juda qisqa xabarda hisobga olinadi.
# ("buyurtma" so'zi shikoyatda ham uchraydi: "buyurtmam qayerda qoldi?")
MENU_WORDS_WEAK = [
    "zakaz", "zakas", "buyurtma", "заказ", "order", "sipariş", "siparis", "pesan",
    "qancha", "nechchi", "nechi", "сколько", "كم السعر",
]

def looks_like_menu_request(text):
    """Mijoz menyu yoki narx so'rayaptimi. Shikoyat va savollarni tegmay qoldiradi."""
    low = (text or "").strip().lower()
    if not low or len(low) > 60:
        return False
    if any(w in low for w in MENU_WORDS_STRONG):
        return True
    # kuchsiz so'zlar: faqat 1-2 so'zlik juda qisqa xabarda
    # ("buyurtmam qayerda qoldi?" kabi savol adminga borishi kerak)
    if len(low.split()) <= 2 and any(w in low for w in MENU_WORDS_WEAK):
        return True
    return False

@bot.message_handler(
    func=lambda m: (
        m.content_type == "text"
        and not m.text.startswith("/")
        and m.from_user.id not in checkout_state
        and m.from_user.id not in repeat_state
        and not is_staff_or_admin(m.from_user.id)
        and not is_any_bot_button(m.text)
    )
)
def handle_customer_free_text(message):
    sender = message.from_user
    add_known_user(sender)
    lang = get_user_lang(sender.id, getattr(sender, "language_code", None))

    # "menyu?" degan xabarga bot o'zi javob beradi — adminni bezovta qilmaymiz
    if looks_like_menu_request(message.text):
        bot.send_message(message.chat.id, t("menu_hint", lang),
                         reply_markup=main_keyboard(sender.id, sender.username, lang))
        return

    label = f"{sender.first_name or ''} (@{sender.username})" if sender.username else (sender.first_name or "Mijoz")
    forward_text = (
        f"📩 Mijozdan xabar\n👤 {label} (ID: {sender.id})\n\n{message.text}\n\n"
        "↩️ Javob berish uchun shu xabarga \"Reply\" qiling."
    )
    for recipient_id in notify_recipients():
        try:
            sent = bot.send_message(recipient_id, forward_text)
            support_message_map[(recipient_id, sent.message_id)] = sender.id
        except Exception:
            pass
    bot.send_message(message.chat.id, t("msg_received", get_user_lang(sender.id, getattr(sender, "language_code", None))))


# ======================================================================
#  INSTAGRAM BOT — Direct'dagi buyurtmalar ham shu Telegram tizimga tushadi
# ======================================================================
#  Railway Variables (sozlamalar):
#    IG_ACCESS_TOKEN  — Meta Developers'da yaratilgan Instagram tokeni
#    IG_APP_SECRET    — Meta ilovaning Instagram App Secret'i (imzo tekshiruvi)
#    IG_VERIFY_TOKEN  — webhook tasdiqlash uchun o'zingiz o'ylab topgan so'z
#    IG_USER_ID       — @miqotfood'ning Instagram ID'si (o'z izohlariga javob bermaslik uchun)
#    IG_MIN_ORDER     — eng kam buyurtma summasi (standart 30)
#    IG_COMMENT_ALL   — "1" bo'lsa har qanday izohga Direct yuboradi, aks holda faqat "menyu" kabi so'zlarga
#  Webhook manzili:  {WEBAPP_URL}/ig/webhook
# ----------------------------------------------------------------------

IG_ACCESS_TOKEN = os.environ.get("IG_ACCESS_TOKEN", "")
IG_APP_SECRET = os.environ.get("IG_APP_SECRET", "")
IG_VERIFY_TOKEN = os.environ.get("IG_VERIFY_TOKEN", "")
IG_USER_ID = os.environ.get("IG_USER_ID", "")
# Yangi Meta ilovalari "Unified login" ishlatadi -> graph.facebook.com (token muddatsiz).
# Eski "Instagram login" tokeni bo'lsa IG_API_HOST=graph.instagram.com qo'ying.
IG_API_HOST = os.environ.get("IG_API_HOST", "")
IG_API_VERSION = os.environ.get("IG_API_VERSION", "v21.0")
IG_API = ""

def ig_detect_host():
    """Token qaysi Meta serveriga tegishli ekanini o'zi aniqlaydi (instagram yoki facebook)."""
    global IG_API_HOST, IG_API
    if not IG_API_HOST and IG_ACCESS_TOKEN:
        for host in ("graph.instagram.com", "graph.facebook.com"):
            try:
                r = httpreq.get(f"https://{host}/{IG_API_VERSION}/me",
                                params={"fields": "id", "access_token": IG_ACCESS_TOKEN}, timeout=10)
                if r.ok:
                    IG_API_HOST = host
                    break
            except Exception:
                pass
    IG_API_HOST = IG_API_HOST or "graph.facebook.com"
    IG_API = f"https://{IG_API_HOST}/{IG_API_VERSION}"
    print(f"[IG] API: {IG_API}")
IG_MIN_ORDER = float(os.environ.get("IG_MIN_ORDER", "30"))
IG_COMMENT_ALL = os.environ.get("IG_COMMENT_ALL", "0") == "1"
IG_TG_BOT_URL = os.environ.get("IG_TG_BOT_URL", "https://t.me/miqotfoodbuyurtmabot")
# Mini App'ning to'g'ridan-to'g'ri havolasi — bosilsa darrov menyu ochiladi
IG_TG_MENU_URL = os.environ.get(
    "IG_TG_MENU_URL", IG_TG_BOT_URL.rstrip("/") + "/menyu")

IG_SESSIONS_FILE = os.path.join(DATA_DIR, "ig_sessions.json")
IG_LOCK = threading.RLock()
_ig_profile_cache = {}

# quick-reply tugmalari
IGQ_MENU = ("🍽 Menyu", "MENU")
IGQ_CART = ("🛒 Savat", "CART")
IGQ_CHECKOUT = ("✅ Buyurtma berish", "CHECKOUT")
IGQ_CLEAR = ("🗑 Tozalash", "CLEAR")
IGQ_CONFIRM = ("✅ Tasdiqlash", "CONFIRM")
IGQ_CANCEL = ("❌ Bekor qilish", "CANCEL")
IGQ_MORE = ("➡️ Yana taomlar", "MORE")


IG_TOKEN_FILE = os.path.join(DATA_DIR, "ig_token.json")
# avval yangilangan token faylda bo'lsa, o'shani olamiz (Railway'dagi eski token 60 kunda eskiradi)
_saved_tok = load_json(IG_TOKEN_FILE, {}).get("token")
if _saved_tok:
    IG_ACCESS_TOKEN = _saved_tok


def ig_enabled():
    return bool(IG_ACCESS_TOKEN)


def ig_token_refresher():
    """Har 20 kunda tokenni yangilaydi — 60 kunlik muddat hech qachon tugamaydi."""
    global IG_ACCESS_TOKEN
    ig_detect_host()
    if IG_API_HOST != "graph.instagram.com":
        return  # Unified login tokeni muddatsiz — yangilash shart emas
    while True:
        try:
            if IG_ACCESS_TOKEN:
                r = httpreq.get("https://graph.instagram.com/refresh_access_token",
                                params={"grant_type": "ig_refresh_token",
                                        "access_token": IG_ACCESS_TOKEN}, timeout=15)
                if r.ok and r.json().get("access_token"):
                    IG_ACCESS_TOKEN = r.json()["access_token"]
                    save_json(IG_TOKEN_FILE, {"token": IG_ACCESS_TOKEN, "at": int(time.time())})
                    print("[IG] token yangilandi")
                else:
                    print(f"[IG] tokenni yangilab bo'lmadi: {r.status_code} {r.text[:200]}")
        except Exception as e:
            print(f"[IG] token yangilash xatosi: {e}")
        time.sleep(20 * 86400)


# ---------- sessiya (savat, qadam) ----------

def ig_sessions():
    return load_json(IG_SESSIONS_FILE, {})

def ig_get(uid):
    with IG_LOCK:
        return ig_sessions().get(str(uid)) or {"cart": {}, "step": None}

def ig_put(uid, st):
    with IG_LOCK:
        data = ig_sessions()
        st["updated"] = int(time.time())
        data[str(uid)] = st
        # 7 kundan eski sessiyalarni tozalaymiz
        cutoff = time.time() - 7 * 86400
        data = {k: v for k, v in data.items() if v.get("updated", 0) > cutoff}
        save_json(IG_SESSIONS_FILE, data)


# ---------- Instagram API ----------

_ig_msg_route = None  # ishlagan (host, yo'l) juftligi eslab qolinadi

def ig_send_message(payload):
    """Xabar yuborish: Meta tokeni turiga qarab to'g'ri manzilni o'zi topadi."""
    global _ig_msg_route
    routes = [_ig_msg_route] if _ig_msg_route else []
    for host in ("graph.facebook.com", "graph.instagram.com"):
        if IG_USER_ID:
            routes.append((host, f"{IG_USER_ID}/messages"))
        routes.append((host, "me/messages"))
    last_err = None
    for host, path in routes:
        try:
            r = httpreq.post(f"https://{host}/{IG_API_VERSION}/{path}", json=payload,
                             params={"access_token": IG_ACCESS_TOKEN}, timeout=15)
            if r.ok:
                if _ig_msg_route != (host, path):
                    _ig_msg_route = (host, path)
                    print(f"[IG] xabar yuborish manzili: {host}/{path}")
                return r.json()
            last_err = f"{host}/{path} {r.status_code}: {r.text[:300]}"
            # mijozga tegishli xato (masalan 24 soat o'tgan) bo'lsa boshqa manzilni sinamaymiz
            if _ig_msg_route == (host, path):
                break
        except Exception as e:
            last_err = f"{host}/{path} ulanish xatosi: {e}"
    print(f"[IG] xabar yuborilmadi: {last_err}")
    return None

def ig_api_post(path, payload):
    if path == "me/messages":
        return ig_send_message(payload)
    try:
        r = httpreq.post(f"{IG_API}/{path}", json=payload,
                         params={"access_token": IG_ACCESS_TOKEN}, timeout=15)
        if r.status_code >= 400:
            print(f"[IG] {path} xato {r.status_code}: {r.text[:300]}")
            return None
        return r.json()
    except Exception as e:
        print(f"[IG] {path} ulanish xatosi: {e}")
        return None

def ig_quick(buttons):
    return [{"content_type": "text", "title": title[:20], "payload": payload}
            for title, payload in buttons][:13]

def ig_send_text(igsid, text, quick=None):
    msg = {"text": (text or "")[:1000]}
    if quick:
        msg["quick_replies"] = ig_quick(quick)
    return ig_api_post("me/messages", {"recipient": {"id": str(igsid)}, "message": msg})

def ig_send_carousel(igsid, elements):
    return ig_api_post("me/messages", {
        "recipient": {"id": str(igsid)},
        "message": {"attachment": {"type": "template", "payload": {
            "template_type": "generic", "elements": elements[:10]}}},
    })

def ig_username(igsid):
    if igsid in _ig_profile_cache:
        return _ig_profile_cache[igsid]
    name = None
    try:
        r = httpreq.get(f"{IG_API}/{igsid}", params={"fields": "username,name",
                                                      "access_token": IG_ACCESS_TOKEN}, timeout=10)
        if r.ok:
            j = r.json()
            name = j.get("username") or j.get("name")
    except Exception:
        pass
    _ig_profile_cache[igsid] = name
    return name


# ---------- menyu va savat ----------

def ig_available_menu():
    menu = load_menu()
    out = []
    for _, dishes in group_menu_by_category(menu):
        for d in dishes:
            stock = d.get("stock")
            if stock is not None and stock <= 0:
                continue
            out.append(d)
    return out

def ig_cart_lines(cart):
    menu = {d["id"]: d for d in load_menu()}
    disc = get_discount()
    lines, total = [], 0.0
    for did, qty in cart.items():
        d = menu.get(int(did))
        if not d or qty <= 0:
            continue
        unit = discounted_price(d["price"], disc)
        total += unit * qty
        lines.append(f"• {d['name']} × {qty} = {fmt_sum(unit * qty)}")
    return lines, money(total)

# ---------- Mini App (Telegram'dagi sahifaning o'zi, Instagram brauzerida) ----------

def ig_sign(igsid, ts):
    return hmac.new(BOT_TOKEN.encode(), f"ig:{igsid}:{ts}".encode(), hashlib.sha256).hexdigest()

def ig_verify(igsid, ts, sig):
    if not (igsid and ts and sig):
        return False
    return hmac.compare_digest(ig_sign(igsid, ts), str(sig))

def ig_menu_url(igsid):
    ts = int(time.time())
    return f"{WEBAPP_URL}/?ig={igsid}&its={ts}&isig={ig_sign(igsid, ts)}&v={ts}"

def ig_send_app_card(igsid):
    """Bitta karta: Mini App'ni ochish tugmasi + chatda tanlash varianti."""
    st = shop_status()
    if not st["open"]:
        ig_send_text(igsid, closed_message("uz", st))
        return
    if not WEBAPP_URL:
        ig_send_menu(igsid)
        return
    el = {
        "title": f"{BUSINESS_NAME} — bugungi menyu 🍽",
        "subtitle": "Yetkazib berish BEPUL 🚚 · Taomni tanlab, shu yerda buyurtma bering",
        "buttons": [
            {"type": "web_url", "url": ig_menu_url(igsid), "title": "🛍 Menyuni ochish"},
            {"type": "postback", "title": "💬 Chatda tanlash", "payload": "CHATMENU"},
        ],
    }
    if os.path.exists(LOGO_PATH):
        el["image_url"] = f"{WEBAPP_URL}/static/logo.jpg"
    if ig_send_carousel(igsid, [el]) is None:
        ig_send_menu(igsid)   # karta ketmasa — oddiy menyu

def ig_send_menu(igsid, page=0):
    st = shop_status()
    if not st["open"]:
        ig_send_text(igsid, closed_message("uz", st))
        return
    dishes = ig_available_menu()
    if not dishes:
        ig_send_text(igsid, "Bugungi menyu hali tayyor emas. Birozdan keyin qayta yozing 🙏")
        return
    disc = get_discount()
    chunk = dishes[page * 10:(page + 1) * 10]
    elements = []
    for d in chunk:
        unit = discounted_price(d["price"], disc)
        price = fmt_sum(unit)
        if unit != d["price"]:
            price = f"{fmt_sum(unit)} (avval {fmt_sum(d['price'])})"
        sub = price + ((" · " + d["desc"]) if d.get("desc") else "")
        el = {"title": d["name"][:80], "subtitle": sub[:80],
              "buttons": [{"type": "postback", "title": "➕ Savatga", "payload": f"ADD:{d['id']}"}]}
        if d.get("local_photo") and WEBAPP_URL:
            el["image_url"] = f"{WEBAPP_URL}/static/dishes/{d['local_photo']}"
        elements.append(el)
    if page == 0:
        head = "🍽 Bugungi menyu"
        if disc.get("active"):
            head += f" — 🔥 {disc.get('percent')}% chegirma!"
        ig_send_text(igsid, head + "\nTaomni tanlab «➕ Savatga» ni bosing 👇")
    ig_send_carousel(igsid, elements)
    quick = [IGQ_CART]
    if len(dishes) > (page + 1) * 10:
        quick.insert(0, IGQ_MORE)
        s = ig_get(igsid); s["menu_page"] = page + 1; ig_put(igsid, s)
    ig_send_text(igsid, "Tanlab bo'lgach «🛒 Savat» ni bosing.", quick)

def ig_send_cart(igsid):
    s = ig_get(igsid)
    lines, total = ig_cart_lines(s.get("cart", {}))
    if not lines:
        ig_send_text(igsid, "🛒 Savatingiz bo'sh.", [IGQ_MENU])
        return
    text = "🛒 Savatingiz:\n" + "\n".join(lines) + f"\n\nJami: {fmt_sum(total)}\n🚚 Yetkazib berish BEPUL"
    if total < IG_MIN_ORDER:
        text += f"\n\n⚠️ Eng kam buyurtma {fmt_sum(IG_MIN_ORDER)}. Yana {fmt_sum(IG_MIN_ORDER - total)} qo'shing."
        ig_send_text(igsid, text, [IGQ_MENU, IGQ_CLEAR])
    else:
        ig_send_text(igsid, text, [IGQ_CHECKOUT, IGQ_MENU, IGQ_CLEAR])

def ig_add(igsid, dish_id):
    dish = next((d for d in load_menu() if d["id"] == int(dish_id)), None)
    if not dish:
        ig_send_text(igsid, "Bu taom menyuda qolmadi.", [IGQ_MENU])
        return
    s = ig_get(igsid)
    cart = s.setdefault("cart", {})
    key = str(dish["id"])
    new_qty = cart.get(key, 0) + 1
    stock = dish.get("stock")
    if stock is not None and new_qty > stock:
        ig_send_text(igsid, f"«{dish['name']}» dan faqat {stock} dona qoldi.", [IGQ_CART, IGQ_MENU])
        return
    cart[key] = new_qty
    ig_put(igsid, s)
    _, total = ig_cart_lines(cart)
    ig_send_text(igsid, f"✅ {dish['name']} qo'shildi (×{new_qty}).\nSavat: {fmt_sum(total)}",
                 [IGQ_CART, IGQ_MENU, IGQ_CHECKOUT])


# ---------- rasmiylashtirish ----------

def ig_start_checkout(igsid):
    st = shop_status()
    if not st["open"]:
        ig_send_text(igsid, closed_message("uz", st))
        return
    s = ig_get(igsid)
    _, total = ig_cart_lines(s.get("cart", {}))
    if total <= 0:
        ig_send_text(igsid, "🛒 Savatingiz bo'sh.", [IGQ_MENU])
        return
    if total < IG_MIN_ORDER:
        ig_send_cart(igsid)
        return
    s["step"] = "name"
    ig_put(igsid, s)
    ig_send_text(igsid, "👤 Ismingizni yozing:")

def ig_handle_step(igsid, text):
    s = ig_get(igsid)
    step = s.get("step")
    text = (text or "").strip()
    if step == "name":
        if len(text) < 2:
            ig_send_text(igsid, "Ismingizni yozing, iltimos:")
            return
        s["name"] = text[:60]
        s["step"] = "phone"
        ig_put(igsid, s)
        ig_send_text(igsid, "📞 Telefon raqamingizni yozing (masalan 05XXXXXXXX):")
    elif step == "phone":
        digits = re.sub(r"\D", "", text)
        if len(digits) < 9:
            ig_send_text(igsid, "Raqam noto'g'ri ko'rinadi. Qaytadan yozing (masalan 05XXXXXXXX):")
            return
        s["phone"] = text[:25]
        s["step"] = "address"
        ig_put(igsid, s)
        ig_send_text(igsid, "📍 Manzilingizni yozing (mahalla, mehmonxona/bino, xona raqami) "
                            "yoki Google Maps havolasini yuboring:")
    elif step == "address":
        if len(text) < 4:
            ig_send_text(igsid, "Manzilni batafsilroq yozing, iltimos:")
            return
        s["address"] = text[:300]
        s["step"] = "confirm"
        ig_put(igsid, s)
        lines, total = ig_cart_lines(s.get("cart", {}))
        ig_send_text(igsid,
                     "Buyurtmangizni tekshiring:\n\n" + "\n".join(lines)
                     + f"\n\nJami: {fmt_sum(total)} (naqd, yetkazib berish BEPUL)"
                     + f"\n👤 {s['name']}\n📞 {s['phone']}\n📍 {s['address']}",
                     [IGQ_CONFIRM, IGQ_CANCEL])
    elif step == "confirm":
        ig_send_text(igsid, "Tasdiqlaysizmi?", [IGQ_CONFIRM, IGQ_CANCEL])

def ig_confirm(igsid):
    s = ig_get(igsid)
    if s.get("step") != "confirm" or not s.get("cart"):
        ig_send_cart(igsid)
        return
    st = shop_status()
    if not st["open"]:
        ig_send_text(igsid, closed_message("uz", st))
        return
    uname = ig_username(igsid)
    order, error = create_order(
        items_cart=s["cart"], customer_name=s.get("name") or "Mijoz", phone=s.get("phone") or "",
        latitude=None, longitude=None, address_text=s.get("address"), note="",
        tg_user_id=None, username=None,
        extra={"source": "instagram", "ig_user_id": str(igsid), "ig_username": uname},
    )
    if error:
        ig_send_text(igsid, "❗ " + error, [IGQ_CART, IGQ_MENU])
        return
    ig_put(igsid, {"cart": {}, "step": None, "greeted": True,
                   "name": s.get("name"), "phone": s.get("phone"), "address": s.get("address")})
    ig_send_text(igsid, build_customer_receipt_text(order, "uz")
                 + f"\n\n🎁 Telegram botimizdan buyurtma bersangiz har safar 5% keshbek olasiz: {IG_TG_BOT_URL}")

def ig_welcome(igsid):
    ig_send_text(igsid,
                 f"Assalomu alaykum! {BUSINESS_NAME}'ga xush kelibsiz 🍽\n"
                 "Makkada uy ovqatini BEPUL yetkazib beramiz 🚚\n\n"
                 "Shu yerning o'zida buyurtma berishingiz mumkin 👇",
                 [IGQ_MENU, IGQ_CART])


# ---------- adminga oddiy xabarni yuborish ----------

def ig_forward_to_admins(igsid, text):
    uname = ig_username(igsid)
    who = f"@{uname}" if uname else f"ID {igsid}"
    body = f"📷 Instagram xabar — {who}:\n\n{text}\n\n↩️ Shu xabarga \"Reply\" qilsangiz, javob Instagram'ga boradi."
    for rid in notify_recipients():
        try:
            sent = bot.send_message(rid, body)
            support_message_map[(rid, sent.message_id)] = f"ig:{igsid}"
        except Exception as e:
            print(f"[IG] adminga yuborishda xato: {e}")


# ---------- kelgan hodisalarni ishlash ----------

def ig_handle_payload(igsid, payload):
    if payload == "MENU":
        ig_send_app_card(igsid)
    elif payload == "CHATMENU":
        ig_send_menu(igsid)
    elif payload == "MORE":
        ig_send_menu(igsid, ig_get(igsid).get("menu_page", 1))
    elif payload == "CART":
        ig_send_cart(igsid)
    elif payload == "CHECKOUT":
        ig_start_checkout(igsid)
    elif payload == "CLEAR":
        s = ig_get(igsid); s["cart"] = {}; s["step"] = None; ig_put(igsid, s)
        ig_send_text(igsid, "🗑 Savat tozalandi.", [IGQ_MENU])
    elif payload == "CONFIRM":
        ig_confirm(igsid)
    elif payload == "CANCEL":
        s = ig_get(igsid); s["step"] = None; ig_put(igsid, s)
        ig_send_text(igsid, "Bekor qilindi. Savatingiz saqlanib qoldi.", [IGQ_CART, IGQ_MENU])
    elif payload.startswith("ADD:"):
        ig_add(igsid, payload.split(":", 1)[1])

def ig_handle_messaging(ev):
    sender = str((ev.get("sender") or {}).get("id") or "")
    if not sender or sender == IG_USER_ID:
        return
    msg = ev.get("message") or {}
    if msg.get("is_echo") or msg.get("is_deleted"):
        return
    if ev.get("postback"):
        ig_handle_payload(sender, ev["postback"].get("payload") or "")
        return
    qr = (msg.get("quick_reply") or {}).get("payload")
    if qr:
        ig_handle_payload(sender, qr)
        return
    text = (msg.get("text") or "").strip()
    if not text:
        if msg.get("attachments"):
            ig_forward_to_admins(sender, "[rasm/ovozli xabar/fayl — Instagram'da ko'ring]")
        return
    s = ig_get(sender)
    low = text.lower()
    if s.get("step") and low in ("bekor", "cancel", "отмена", "stop"):
        ig_handle_payload(sender, "CANCEL")
        return
    if s.get("step"):
        ig_handle_step(sender, text)
        return
    if looks_like_menu_request(text):
        ig_send_app_card(sender)
        return
    if not s.get("greeted"):
        s["greeted"] = True
        ig_put(sender, s)
        ig_welcome(sender)
        return
    # oddiy savol/shikoyat — adminga
    ig_forward_to_admins(sender, text)

def ig_comment_buttons(igsid):
    """Izohga javoban ketadigan tugmalar. Birinchisi — bir bosishda menyu."""
    tugma = []
    if WEBAPP_URL and igsid:
        tugma.append({"type": "web_url", "url": ig_menu_url(igsid),
                      "title": "\U0001F6CD Menyuni ochish"})
    if IG_TG_MENU_URL:
        tugma.append({"type": "web_url", "url": IG_TG_MENU_URL,
                      "title": "\u2708\uFE0F Telegramda ochish"})
    if not tugma and WEBAPP_URL:
        tugma.append({"type": "web_url", "url": WEBAPP_URL,
                      "title": "\U0001F6CD Menyuni ochish"})
    return tugma[:3]

def ig_comment_private_reply(cid, igsid):
    """Izoh qoldirgan odamga Direct'ga tugmali menyu yuboradi.
    Karta ketmasa — havolali oddiy matn bilan urinadi (baribir bitta xabar)."""
    tugma = ig_comment_buttons(igsid)
    if tugma:
        el = {
            "title": f"{BUSINESS_NAME} — menyu \U0001F37D",
            "subtitle": "Yetkazib berish BEPUL \U0001F69A",
            "buttons": tugma,
        }
        if WEBAPP_URL and os.path.exists(LOGO_PATH):
            el["image_url"] = f"{WEBAPP_URL}/static/logo.jpg"
        res = ig_api_post("me/messages", {
            "recipient": {"comment_id": cid},
            "message": {"attachment": {"type": "template", "payload": {
                "template_type": "generic", "elements": [el]}}},
        })
        if res is not None:
            return res
        print("[IG] izohga tugmali karta ketmadi — matn bilan urinamiz")

    havola = (ig_menu_url(igsid) if (WEBAPP_URL and igsid)
              else (IG_TG_MENU_URL or WEBAPP_URL or ""))
    matn = f"Assalomu alaykum! {BUSINESS_NAME} menyusi \U0001F37D"
    if havola:
        matn += f"\n{havola}"
    matn += "\nYetkazib berish BEPUL \U0001F69A"
    return ig_api_post("me/messages", {
        "recipient": {"comment_id": cid},
        "message": {"text": matn},
    })

def ig_handle_comment(val):
    frm = val.get("from") or {}
    if not frm.get("id") or str(frm.get("id")) == IG_USER_ID:
        return
    text = val.get("text") or ""
    if not (IG_COMMENT_ALL or looks_like_menu_request(text)):
        return
    cid = val.get("id")
    if not cid:
        return
    igsid = str(frm.get("id") or "")

    #  Direct'ga shaxsiy javob — har izohga faqat BIR marta ruxsat beriladi,
    #  shuning uchun o'sha bitta xabarning o'zida menyu tugmasi ketadi.
    #  Mijozga "yana menyu deb yozing" demaymiz: bosdi — menyu ochildi.
    res = ig_comment_private_reply(cid, igsid)

    #  izohning o'ziga ochiq javob
    if res is not None:
        ig_api_post(f"{cid}/replies", {"message": "Menyuni Direct'ga yubordik \U0001F4E9"})

def ig_process(body):
    try:
        for entry in body.get("entry", []):
            for ev in entry.get("messaging", []) or []:
                ig_handle_messaging(ev)
            for ch in entry.get("changes", []) or []:
                if ch.get("field") == "comments":
                    ig_handle_comment(ch.get("value") or {})
    except Exception as e:
        print(f"[IG] hodisani ishlashda xato: {e}")


@app.route("/ig/webhook", methods=["GET"])
def ig_webhook_verify():
    if (request.args.get("hub.mode") == "subscribe" and IG_VERIFY_TOKEN
            and request.args.get("hub.verify_token") == IG_VERIFY_TOKEN):
        return request.args.get("hub.challenge", ""), 200
    return "forbidden", 403

@app.route("/ig/webhook", methods=["POST"])
def ig_webhook_receive():
    raw = request.get_data()
    if IG_APP_SECRET:
        sig = request.headers.get("X-Hub-Signature-256", "")
        expected = "sha256=" + hmac.new(IG_APP_SECRET.encode(), raw, hashlib.sha256).hexdigest()
        if not hmac.compare_digest(sig, expected):
            return "bad signature", 403
    if not ig_enabled():
        return "ok", 200
    body = json.loads(raw or b"{}")
    # Meta tez javob kutadi — ishni fonda bajaramiz
    threading.Thread(target=ig_process, args=(body,), daemon=True).start()
    return "ok", 200


def ig_notify_customer(order, text):
    """Buyurtma Instagram'dan bo'lsa, mijozga Instagram orqali xabar."""
    igsid = order.get("ig_user_id")
    if igsid and ig_enabled():
        ig_send_text(igsid, text)



def ig_identity_from_request(body):
    """Mini App Instagram'dan ochilgan bo'lsa — mijozning Instagram ID'si (imzo tekshiriladi)."""
    igsid, ts, sig = body.get("ig"), body.get("its"), body.get("isig")
    if not igsid:
        # index.html bu maydonlarni yubormaydi — sahifa manzilidan (Referer) olamiz
        try:
            ref = request.headers.get("Referer", "")
            q = urllib.parse.parse_qs(urllib.parse.urlparse(ref).query)
            igsid, ts, sig = (q.get("ig") or [None])[0], (q.get("its") or [None])[0], (q.get("isig") or [None])[0]
        except Exception:
            return None
    return str(igsid) if ig_verify(igsid, ts, sig) else None


# ---------- Maxfiylik siyosati va ma'lumotlarni o'chirish (Meta App Review uchun) ----------
PRIVACY_CONTACT_EMAIL = os.environ.get("PRIVACY_CONTACT_EMAIL", "abi_93-07@mail.ru")
PRIVACY_UPDATED = "2026-11-01"

_LEGAL_CSS = """
:root{--bg:#f7f5f0;--card:#fff;--ink:#1d2433;--muted:#5b6475;--acc:#0b1f4b;--gold:#c99a2e;--line:#e6e1d6}
@media (prefers-color-scheme:dark){:root{--bg:#0e1320;--card:#161d2e;--ink:#e8ebf2;--muted:#a3abbd;--acc:#f0c869;--gold:#f0c869;--line:#26304a}}
*{box-sizing:border-box}body{margin:0;background:var(--bg);color:var(--ink);font:16px/1.6 -apple-system,Segoe UI,Roboto,Arial,sans-serif}
main{max-width:760px;margin:0 auto;padding:32px 16px 64px}
header{border-bottom:3px solid var(--gold);padding-bottom:16px;margin-bottom:24px}
h1{font-size:26px;margin:0 0 4px;color:var(--acc)}h2{font-size:19px;margin:28px 0 8px;color:var(--acc)}
.muted{color:var(--muted);font-size:14px}.card{background:var(--card);border:1px solid var(--line);border-radius:14px;padding:20px;margin:16px 0}
ul{padding-left:20px}a{color:var(--acc)}.lang{display:flex;gap:8px;margin-top:10px}
.lang a{font-size:14px;text-decoration:none;border:1px solid var(--line);border-radius:999px;padding:4px 12px}
"""

def _legal_page(title, body_html):
    return (f"<!doctype html><html lang='en'><head><meta charset='utf-8'>"
            f"<meta name='viewport' content='width=device-width,initial-scale=1'>"
            f"<meta name='facebook-domain-verification' content='{FB_DOMAIN_VERIFICATION}'>"
            f"<title>{title} — {BUSINESS_NAME}</title><style>{_LEGAL_CSS}</style></head>"
            f"<body><main>{body_html}</main></body></html>")

@app.route("/privacy")
def privacy_page():
    e = PRIVACY_CONTACT_EMAIL
    html = f"""
<header><h1>Privacy Policy</h1>
<div class="muted">{BUSINESS_NAME} · Makkah, Saudi Arabia · Last updated {PRIVACY_UPDATED}</div>
<div class="lang"><a href="#en">English</a><a href="#uz">O'zbekcha</a></div></header>

<section id="en">
<p>{BUSINESS_NAME} is a home-cooked food delivery service in Makkah. Customers order through our Telegram bot,
our web menu, and our Instagram account (@miqotfood). This policy explains what information we collect and how we use it.</p>

<h2>Information we collect</h2>
<ul>
<li><b>Order details:</b> the dishes you choose, quantities, order total and order history.</li>
<li><b>Contact and delivery details you give us:</b> your name, phone number, delivery address and, if you share it, your location.</li>
<li><b>Messaging identifiers:</b> your Telegram user ID and username, or your Instagram-scoped user ID and username, and the messages you send to our account.</li>
<li><b>Cashback balance</b> (Telegram customers only).</li>
</ul>

<h2>How we use it</h2>
<ul>
<li>To receive, prepare and deliver your order and to contact you about it.</li>
<li>To send you order confirmations and status updates in the same app you ordered from.</li>
<li>To answer your questions and comments.</li>
<li>To calculate cashback and keep basic sales records.</li>
</ul>
<p>We do <b>not</b> sell your information, use it for advertising profiles, or share it with anyone except as needed to deliver your order.</p>

<h2>Instagram data</h2>
<p>When you message @miqotfood or comment asking for the menu, our app receives your message, your Instagram-scoped ID and username
through Meta's Instagram API. We use this only to reply to you, show you the menu, and take your order. Comments are used only to send
you a single private reply with the menu.</p>

<h2>Service providers</h2>
<p>Our system runs on Railway (cloud hosting). Messages are delivered through Meta (Instagram) and Telegram, under their own privacy policies.</p>

<h2>How long we keep it</h2>
<p>Order records are kept for up to 24 months for accounting and service quality, then deleted. Unfinished Instagram chat sessions are removed after 7 days.</p>

<h2>Deleting your data</h2>
<p>You can ask us to delete your data at any time — see <a href="/data-deletion">Data deletion instructions</a>. We complete requests within 30 days.</p>

<h2>Contact</h2>
<p>Email: <a href="mailto:{e}">{e}</a> · Instagram: @miqotfood · Telegram: @miqotfoodbuyurtmabot</p>
</section>

<section id="uz" class="card">
<h2>Maxfiylik siyosati (qisqacha)</h2>
<p>{BUSINESS_NAME} Makkada uy ovqatini yetkazib beradi. Buyurtmani bajarish uchun quyidagilarni saqlaymiz: tanlagan taomlaringiz,
ismingiz, telefon raqamingiz, manzilingiz (yoki joylashuvingiz), Telegram yoki Instagram foydalanuvchi ID va nomingiz, keshbek balansingiz.</p>
<p>Bu ma'lumotlar faqat buyurtmani yetkazish, siz bilan bog'lanish va buyurtma holatini xabar qilish uchun ishlatiladi.
Hech kimga sotilmaydi va reklama uchun ishlatilmaydi.</p>
<p>Ma'lumotlaringizni o'chirishni xohlasangiz, Direct yoki Telegram'da «ma'lumotlarimni o'chiring» deb yozing yoki
<a href="mailto:{e}">{e}</a> manziliga xat yuboring — 30 kun ichida o'chiramiz.</p>
</section>
"""
    return _legal_page("Privacy Policy", html)

@app.route("/data-deletion")
def data_deletion_page():
    e = PRIVACY_CONTACT_EMAIL
    html = f"""
<header><h1>Data Deletion Instructions</h1>
<div class="muted">{BUSINESS_NAME} · Last updated {PRIVACY_UPDATED}</div></header>
<p>You can ask {BUSINESS_NAME} to delete all personal data we hold about you (name, phone number, address, order history,
messaging IDs and cashback balance).</p>
<div class="card"><b>How to request deletion — any one of these:</b>
<ul>
<li>Send a Direct message to <b>@miqotfood</b> on Instagram: <i>"Delete my data"</i>.</li>
<li>Send the same message to our Telegram bot <b>@miqotfoodbuyurtmabot</b>.</li>
<li>Email <a href="mailto:{e}">{e}</a> with your Instagram username or phone number.</li>
</ul></div>
<p>We confirm your request and delete your data within <b>30 days</b>. Records we are legally required to keep for accounting
are anonymised (your name, phone and address are removed).</p>
<p>You can also remove our app's access at any time in Instagram: <i>Settings → Website permissions → Apps and websites</i>.</p>
<div class="card"><b>O'zbekcha:</b> ma'lumotlaringizni o'chirish uchun Instagram'da @miqotfood'ga yoki Telegram'da
@miqotfoodbuyurtmabot'ga «ma'lumotlarimni o'chiring» deb yozing yoki <a href="mailto:{e}">{e}</a> ga xat yuboring.
30 kun ichida o'chiramiz.</div>
<p><a href="/privacy">Privacy Policy</a></p>
"""
    return _legal_page("Data Deletion", html)

@app.route("/terms")
def terms_page():
    html = f"""
<header><h1>Terms of Service</h1><div class="muted">{BUSINESS_NAME} · Last updated {PRIVACY_UPDATED}</div></header>
<p>By ordering from {BUSINESS_NAME} through Telegram, our web menu or Instagram you agree that: prices and menu items are shown at the
time of ordering; payment is made in cash on delivery unless agreed otherwise; we deliver within our service area in Makkah;
we may contact you by phone or message about your order; and you may cancel by contacting us before the order is prepared.</p>
<p>See our <a href="/privacy">Privacy Policy</a> for how we handle your data.</p>
"""
    return _legal_page("Terms of Service", html)

# ---------- ishga tushirish ----------

def run_bot_polling():
    bot.infinity_polling()

if __name__ == "__main__":
    migrate_builder_category()
    qoshildi = backfill_users_from_history()
    if qoshildi:
        print(f"Eski buyurtmalardan {qoshildi} ta mijoz ro'yxatga qo'shildi.")
    threading.Thread(target=run_bot_polling, daemon=True).start()
    threading.Thread(target=daily_report_scheduler, daemon=True).start()
    threading.Thread(target=winback_scheduler, daemon=True).start()
    if ig_enabled():
        threading.Thread(target=ig_token_refresher, daemon=True).start()
    port = int(os.environ.get("PORT", 8080))
    print(f"Mini App server {port}-portda ishga tushdi, bot polling fonda ishlayapti...")
    app.run(host="0.0.0.0", port=port)
