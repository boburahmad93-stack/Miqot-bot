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
DISH_PHOTOS_DIR = os.path.join(DATA_DIR, "static", "dishes")
LOGO_PATH = os.path.join(DATA_DIR, "static", "logo.jpg")

os.makedirs(DISH_PHOTOS_DIR, exist_ok=True)

bot = telebot.TeleBot(BOT_TOKEN)
app = Flask(__name__)
app.config["MAX_CONTENT_LENGTH"] = 12 * 1024 * 1024  # rasm uchun eng katta hajm: 12 MB

# ---------- fayl bilan ishlash ----------

def load_json(path, default):
    if not os.path.exists(path):
        return default
    with open(path, "r", encoding="utf-8") as f:
        return json.load(f)

def save_json(path, data):
    with open(path, "w", encoding="utf-8") as f:
        json.dump(data, f, ensure_ascii=False, indent=2)

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

CATEGORIES = ["Nonushta", "Ovqatlar", "Fast Food", "Salatlar", "Salqin ichimliklar", "Boshqa mahsulotlar"]
DEFAULT_CATEGORY = "Boshqa mahsulotlar"
CATEGORY_EMOJI = {
    "Nonushta": "🍳",
    "Ovqatlar": "🍲",
    "Fast Food": "🍔",
    "Salatlar": "🥗",
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

def get_user_lang(user_id, tg_code=None):
    """Avval mijoz tanlagan til, bo'lmasa Telegram tilidan taxmin, bo'lmasa inglizcha."""
    if user_id:
        saved = load_user_langs().get(str(user_id))
        if saved in SUPPORTED_LANGS:
            return saved
    code = (tg_code or "").lower().split("-")[0]
    if code in SUPPORTED_LANGS:
        return code
    if code in LANG_ALIASES:
        return LANG_ALIASES[code]
    return "uz"

TEXTS = {
    "welcome": {
        "uz": "Assalomu alaykum! 👋\n{biz}ga xush kelibsiz.\nPastdagi tugma orqali buyurtma bera boshlang:",
        "ar": "السلام عليكم! 👋\nمرحبًا بك في {biz}.\nابدأ طلبك من الزر بالأسفل:",
        "en": "Hello! 👋\nWelcome to {biz}.\nStart your order with the button below:",
        "ru": "Здравствуйте! 👋\nДобро пожаловать в {biz}.\nНачните заказ кнопкой ниже:",
        "tr": "Merhaba! 👋\n{biz}'a hoş geldiniz.\nAşağıdaki butondan siparişe başlayın:",
        "ur": "السلام علیکم! 👋\n{biz} میں خوش آمدید۔\nنیچے والے بٹن سے آرڈر شروع کریں:",
        "id": "Halo! 👋\nSelamat datang di {biz}.\nMulai pesanan lewat tombol di bawah:",
    },
    "btn_order": {
        "uz": "🛍 Buyurtma berish", "ar": "🛍 اطلب الآن", "en": "🛍 Place an order",
        "ru": "🛍 Сделать заказ", "tr": "🛍 Sipariş ver", "ur": "🛍 آرڈر دیں", "id": "🛍 Pesan sekarang",
    },
    "btn_contact": {
        "uz": "💬 Biz bilan bog'lanish", "ar": "💬 تواصل معنا", "en": "💬 Contact us",
        "ru": "💬 Связаться с нами", "tr": "💬 Bize ulaşın", "ur": "💬 ہم سے رابطہ", "id": "💬 Hubungi kami",
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
    "status_update": {
        "uz": "Buyurtmangiz #{no} holati: {st}", "ar": "حالة طلبك #{no}: {st}",
        "en": "Your order #{no} status: {st}", "ru": "Статус заказа №{no}: {st}",
        "tr": "Sipariş #{no} durumu: {st}", "ur": "آپ کے آرڈر #{no} کی حالت: {st}",
        "id": "Status pesanan #{no}: {st}",
    },
    "lang_choose": {
        "uz": "Tilni tanlang:", "ar": "اختر اللغة:", "en": "Choose your language:",
        "ru": "Выберите язык:", "tr": "Dil seçin:", "ur": "زبان منتخب کریں:", "id": "Pilih bahasa:",
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

def is_owner(chat_id):
    """To'liq admin — menyu, zaxira, adminlarni boshqara oladi."""
    return chat_id in load_admin_ids()

def is_staff_or_admin(chat_id):
    """Xodim yoki admin — buyurtma xabarini oladi, holatini o'zgartira oladi."""
    return chat_id in load_admin_ids() or chat_id in load_staff_ids()

def notify_recipients():
    return load_admin_ids() | load_staff_ids()

def fmt_sum(n):
    return f"{n:,.0f} SAR".replace(",", " ")

def parse_dish_caption(text):
    """'Nomi;Narxi;Tavsif;Kategoriya' formatini o'qiydi. Kategoriya ixtiyoriy."""
    parts = text.split(";")
    name = parts[0].strip()
    price = float(parts[1].strip())
    desc = parts[2].strip() if len(parts) > 2 else ""
    category_raw = parts[3].strip() if len(parts) > 3 else ""
    category = match_category(category_raw)
    category_warning = category is None
    if category is None:
        category = DEFAULT_CATEGORY
    return name, price, desc, category, category_warning

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
            kb.row(types.KeyboardButton("🧑‍🍳 Menyuni boshqarish", web_app=types.WebAppInfo(url=admin_url)))
    kb.row(types.KeyboardButton(t("btn_contact", lang)), types.KeyboardButton(t("btn_lang", lang)))
    return kb

def is_contact_button(text):
    return any(text == TEXTS["btn_contact"][l] for l in SUPPORTED_LANGS)

def is_lang_button(text):
    return any(text == TEXTS["btn_lang"][l] for l in SUPPORTED_LANGS)

def is_no_phone_button(text):
    return any(text == TEXTS["btn_no_phone"][l] for l in SUPPORTED_LANGS)

def is_any_bot_button(text):
    return is_contact_button(text) or is_lang_button(text) or is_no_phone_button(text)

def lang_keyboard():
    kb = types.InlineKeyboardMarkup(row_width=2)
    buttons = [types.InlineKeyboardButton(LANG_NAMES[c], callback_data=f"setlang:{c}") for c in SUPPORTED_LANGS]
    for i in range(0, len(buttons), 2):
        kb.row(*buttons[i:i+2])
    return kb

# ---------- /start ----------

@bot.message_handler(commands=["start"])
def cmd_start(message):
    carts.pop(message.from_user.id, None)
    checkout_state.pop(message.from_user.id, None)
    lang = get_user_lang(message.from_user.id, getattr(message.from_user, "language_code", None))
    st = shop_status()
    if st["open"] or is_owner(message.chat.id):
        welcome = t("welcome", lang, biz=BUSINESS_NAME)
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

def create_order(items_cart, customer_name, phone, latitude, longitude, address_text, note, tg_user_id, username):
    """Muvaffaqiyatli bo'lsa (order, None), zaxira yetmasa (None, xato_matni) qaytaradi."""
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
        items.append(item)
        total += unit * qty
        original_total += dish["price"] * qty

    if not items:
        return None, "Savat bo'sh."

    # zaxirani kamaytiramiz
    for dish, qty in parsed_cart:
        if dish.get("stock") is not None:
            dish["stock"] = max(0, dish["stock"] - qty)
    save_menu(full_menu)

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
        "payment": "naqd",
        "created_at": created_at,
        "user_id": tg_user_id,
        "username": username,
    }
    orders.append(order)
    save_orders(orders)
    if OWNER_CHAT_ID:
        notify_owner_new_order(order)
    if tg_user_id:
        try:
            bot.send_message(
                tg_user_id,
                build_customer_receipt_text(order),
                reply_markup=main_keyboard(tg_user_id, username)
            )
        except Exception:
            pass
    return order, None

def build_customer_receipt_text(order, lang=None):
    lang = lang or get_user_lang(order.get("user_id"))
    text = (
        t("receipt_title", lang, no=order["daily_number"]) + "\n\n"
        f"{order_items_text(order)}\n\n"
        + discount_line_for_customer(order, lang)
        + t("receipt_total", lang, sum=fmt_sum(order["total"])) + "\n"
        f"{order_address_line(order)}\n"
    )
    if order.get("note"):
        text += f"📝 {order['note']}\n"
    if not (order.get("phone") or "").strip():
        text += t("receipt_nophone", lang)
    text += t("receipt_tail", lang)
    return text

def discount_line_for_customer(order, lang):
    pct = order.get("discount_percent") or 0
    old = order.get("original_total")
    if not pct or not old or old <= order.get("total", 0):
        return ""
    return t("discount_line", lang, pct=pct,
             old=fmt_sum(old), new=fmt_sum(order["total"]))

def order_items_text(order):
    return "\n".join([f"{it['name']} × {it['qty']} = {fmt_sum(it['price']*it['qty'])}" for it in order["items"]])

def order_discount_line(order):
    """Aksiya bo'lgan buyurtmada eski summa va chegirma qatorini qaytaradi."""
    pct = order.get("discount_percent") or 0
    old = order.get("original_total")
    if not pct or not old or old <= order.get("total", 0):
        return ""
    saved = old - order["total"]
    return f"🏷 Aksiya −{pct}%: {fmt_sum(old)} → {fmt_sum(order['total'])} (−{fmt_sum(saved)})\n"

def order_address_line(order):
    if order.get("latitude") is not None:
        return "📍 Joylashuv quyida xarita orqali yuborildi"
    return f"📍 {order.get('address_text') or '—'}"

def order_contact_line(order):
    if order.get("username"):
        return f"@{order['username']}"
    return "username yo'q"

def status_keyboard(order, include_contact=True):
    kb = types.InlineKeyboardMarkup(row_width=2)
    kb.add(
        types.InlineKeyboardButton("👨‍🍳 Tayyorlanmoqda", callback_data=f"status:{order['id']}:Tayyorlanmoqda"),
        types.InlineKeyboardButton("🚴 Yo'lda", callback_data=f"status:{order['id']}:Yo'lda"),
    )
    kb.add(types.InlineKeyboardButton("✅ Yetkazildi", callback_data=f"status:{order['id']}:Yetkazildi"))
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
            + f"💰 Jami: {fmt_sum(order['total'])} (naqd)\n"
            f"Holat: {order['status']}"
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
    except Exception as e:
        print(f"Reply manzilini eslab qolishda xato: {e}")

@bot.callback_query_handler(func=lambda c: c.data.startswith("status:"))
def cb_update_status(call):
    if not is_staff_or_admin(call.message.chat.id):
        bot.answer_callback_query(call.id, "Ruxsat yo'q.")
        return
    _, order_id_str, new_status = call.data.split(":", 2)
    order_id = int(order_id_str)
    orders = load_orders()
    order = next((o for o in orders if o["id"] == order_id), None)
    if not order:
        bot.answer_callback_query(call.id, "Buyurtma topilmadi.")
        return
    order["status"] = new_status
    save_orders(orders)

    text = (
        f"📦 Buyurtma #{order['daily_number']}\n\n"
        f"👤 {order['customer_name']} ({order_contact_line(order)})\n"
        f"{order_phone_line(order)}\n"
        f"{order_address_line(order)}\n"
        + (f"📝 {order['note']}\n" if order.get('note') else "")
        + f"\n{order_items_text(order)}\n\n"
        + order_discount_line(order)
        + f"💰 Jami: {fmt_sum(order['total'])} (naqd)\n"
        f"Holat: {new_status}"
    )
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
        # boshqa xatolar (masalan matn o'zgarmagan) e'tiborsiz qoldiriladi
    bot.answer_callback_query(call.id, f"Holat yangilandi: {new_status}")

    try:
        clang = get_user_lang(order["user_id"])
        bot.send_message(order["user_id"], t("status_update", clang,
                                             no=order["daily_number"], st=status_name(new_status, clang)))
    except Exception:
        pass

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
            "Taom rasmini caption bilan yuboring: Nomi;Narxi;Tavsif;Kategoriya\n"
            f"Kategoriyalar: {', '.join(CATEGORIES)}\n"
            "Kategoriyani yozmasangiz \"Boshqa mahsulotlar\"ga tushadi.\n"
            "Yoki logotip sifatida saqlash uchun caption'ga \"logo\" deb yozing."
        )
        return

    try:
        name, price, desc, category, cat_warning = parse_dish_caption(caption)
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
        "photo_id": photo_id, "local_photo": local_filename, "stock": 0, "category": category
    })
    save_menu(menu)
    warn = f"\n⚠️ Kategoriya tanilmadi, \"{DEFAULT_CATEGORY}\"ga qo'yildi." if cat_warning else ""
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

@app.route("/")
def miniapp_index():
    return send_from_directory(".", "index.html")

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

    if not user:
        # 1) avval botning o'zi imzolagan uid/uname/ts/sig orqali tekshiramiz (eng ishonchli)
        signed_user = verify_signed_user(
            body.get("uid"), body.get("uname"), body.get("ts"), body.get("sig")
        )
        if signed_user:
            user = signed_user
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
    # Raqam majburiy emas: raqami bo'lmagan mijoz bilan bot orqali bog'lanamiz.
    # Lekin raqam ham, Telegram hisobi ham bo'lmasa — bog'lanishning iloji yo'q.
    if not phone and not user.get("id"):
        return jsonify({"error": "Telefon raqamingizni kiriting — aks holda siz bilan bog'lana olmaymiz."}), 400

    order, error = create_order(
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
    return jsonify({"ok": True, "order_id": order["daily_number"], "total": order["total"]})

# ---------- admin paneli (Mini App orqali taom qo'shish) ----------

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
  .card.hours.shut { border-color:var(--danger); background:linear-gradient(135deg, rgba(220,38,38,0.1), transparent); }
  .timeRow { display:flex; gap:12px; margin:4px 0 16px; }
  .timeRow label { flex:1; margin:0; }
  .timeRow.off { opacity:0.42; pointer-events:none; }
  .card.hours .saleBtn { width:100%; }
</style>
</head>
<body>
<h1>🧑‍🍳 Menyuni boshqarish</h1>
<p class="sub">Taomni rasmi bilan shu yerdan qo'shing — Telegram'ga qaytish shart emas.</p>

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

function resetForm() {
  editingId = null;
  $('formTitle').textContent = '➕ Yangi taom';
  $('f_name').value = ''; $('f_price').value = ''; $('f_desc').value = '';
  $('f_stock').value = '0'; $('f_photo').value = ''; $('f_cat').selectedIndex = 0;
  $('f_unlimited').checked = false; $('f_stock').disabled = false;
  $('preview').hidden = true; $('cancelBtn').hidden = true; say('');
}
$('cancelBtn').addEventListener('click', resetForm);

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
    render((await r.json()).dishes || []);
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
            .replace("__EMOJI__", json.dumps(CATEGORY_EMOJI, ensure_ascii=False)))
    return html, 200, {"Content-Type": "text/html; charset=utf-8"}

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
        }
        if d.get("local_photo"):
            item["photo_url"] = f"/static/dishes/{d['local_photo']}"
        out.append(item)
    return jsonify({"dishes": out})

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
    return {"name": name, "price": price, "desc": desc, "category": category, "stock": stock}, None

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

    total_revenue = sum(o["total"] for o in day_orders)
    dish_counts = {}
    for o in day_orders:
        for it in o["items"]:
            dish_counts[it["name"]] = dish_counts.get(it["name"], 0) + it["qty"]

    sorted_dishes = sorted(dish_counts.items(), key=lambda x: -x[1])
    dish_lines = "\n".join(f"  • {name} — {qty} dona" for name, qty in sorted_dishes)

    status_counts = {}
    for o in day_orders:
        status_counts[o["status"]] = status_counts.get(o["status"], 0) + 1
    status_lines = "\n".join(f"  • {s}: {c}" for s, c in status_counts.items())

    return (
        f"📊 Kunlik hisobot — {target_date.strftime('%d.%m.%Y')}\n\n"
        f"🧾 Buyurtmalar soni: {len(day_orders)}\n"
        f"💰 Jami savdo: {fmt_sum(total_revenue)}\n\n"
        f"🍽 Sotilgan taomlar:\n{dish_lines}\n\n"
        f"📦 Holatlar bo'yicha:\n{status_lines}"
    )

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

# ---------- mijoz bilan yozishish (support chat) ----------

support_message_map = {}  # (admin_chat_id, message_id) -> mijoz_user_id

@bot.message_handler(func=lambda m: m.text and is_contact_button(m.text))
def handle_contact_button(message):
    lang = get_user_lang(message.from_user.id, getattr(message.from_user, "language_code", None))
    bot.send_message(message.chat.id, t("contact_prompt", lang))

@bot.message_handler(commands=["til", "lang", "language"])
def cmd_lang(message):
    lang = get_user_lang(message.from_user.id, getattr(message.from_user, "language_code", None))
    bot.send_message(message.chat.id, t("lang_choose", lang), reply_markup=lang_keyboard())

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
    try:
        clang = get_user_lang(customer_id)
        bot.send_message(customer_id, t("reply_from", clang, biz=BUSINESS_NAME) + f"\n{message.text}")
        bot.send_message(message.chat.id, "✅ Javobingiz mijozga yuborildi.")
    except Exception:
        bot.send_message(message.chat.id, "❌ Yuborib bo'lmadi — mijoz botni bloklagan bo'lishi mumkin.")

@bot.message_handler(
    func=lambda m: (
        m.content_type == "text"
        and not m.text.startswith("/")
        and m.from_user.id not in checkout_state
        and not is_staff_or_admin(m.from_user.id)
        and not is_any_bot_button(m.text)
    )
)
def handle_customer_free_text(message):
    sender = message.from_user
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

# ---------- ishga tushirish ----------

def run_bot_polling():
    bot.infinity_polling()

if __name__ == "__main__":
    threading.Thread(target=run_bot_polling, daemon=True).start()
    threading.Thread(target=daily_report_scheduler, daemon=True).start()
    port = int(os.environ.get("PORT", 8080))
    print(f"Mini App server {port}-portda ishga tushdi, bot polling fonda ishlayapti...")
    app.run(host="0.0.0.0", port=port)
