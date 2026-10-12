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
    "lang_choose": {
        "uz": "Tilni tanlang:", "ar": "اختر اللغة:", "en": "Choose your language:",
        "ru": "Выберите язык:", "tr": "Dil seçin:", "ur": "زبان منتخب کریں:", "id": "Pilih bahasa:",
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
    if not uid or order.get("cashback_credited") or is_cancelled(order):
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

def cashback_totals():
    """Barcha mijozlardagi yig'ilib turgan keshbek — bu bizning qarzimiz."""
    data = load_cashback()
    bal = money(sum(money(r.get("balance", 0)) for r in data.values()))
    people = sum(1 for r in data.values() if money(r.get("balance", 0)) > 0)
    return {"balance": bal, "people": people, "all": len(data)}

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
            kitchen_url = f"{WEBAPP_URL}/kitchen?{params}"
            kb.row(types.KeyboardButton("🧑‍🍳 Menyuni boshqarish", web_app=types.WebAppInfo(url=admin_url)))
            kb.row(types.KeyboardButton("🖨 Oshxona", web_app=types.WebAppInfo(url=kitchen_url)))
    try:
        if user_id and quiz_visible_to(user_id):
            kb.row(types.KeyboardButton(QUIZ_BTN), types.KeyboardButton(BOARD_BTN))
    except Exception:
        pass
    kb.row(types.KeyboardButton(t("btn_contact", lang)), types.KeyboardButton(t("btn_lang", lang)))
    return kb

def is_contact_button(text):
    return any(text == TEXTS["btn_contact"][l] for l in SUPPORTED_LANGS)

def is_lang_button(text):
    return any(text == TEXTS["btn_lang"][l] for l in SUPPORTED_LANGS)

def is_no_phone_button(text):
    return any(text == TEXTS["btn_no_phone"][l] for l in SUPPORTED_LANGS)

def is_any_bot_button(text):
    return (is_contact_button(text) or is_lang_button(text) or is_no_phone_button(text)
            or text in (QUIZ_BTN, BOARD_BTN))

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

def create_order(items_cart, customer_name, phone, latitude, longitude, address_text, note, tg_user_id, username, use_cashback=False):
    """Muvaffaqiyatli bo'lsa (order, None), zaxira yetmasa (None, xato_matni) qaytaradi."""
    with DATA_LOCK:
        order, error = _create_order_locked(items_cart, customer_name, phone, latitude, longitude,
                                            address_text, note, tg_user_id, username, use_cashback)
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

def _create_order_locked(items_cart, customer_name, phone, latitude, longitude, address_text, note, tg_user_id, username, use_cashback=False):
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

    # keshbek: balansdan buyurtma summasidan oshmaydigan qismi ishlatiladi
    cb_used = 0.0
    if use_cashback and tg_user_id and get_cashback_cfg()["active"]:
        cb_used = money(min(cashback_balance(tg_user_id), money(total)))
        if cb_used < 0.01:
            cb_used = 0.0

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
        "printed": False,
        "payment": "naqd",
        "created_at": created_at,
        "user_id": tg_user_id,
        "username": username,
    }
    orders.append(order)
    save_orders(orders)
    if cb_used > 0:
        cashback_move(tg_user_id, -cb_used, order["id"], "buyurtmada ishlatildi")
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
        f"{order_items_text(order)}\n\n"
        + discount_line_for_customer(order, lang)
        + t("receipt_total", lang, sum=fmt_sum(order["total"])) + "\n"
        + cashback_line_for_customer(order, lang)
        + f"{order_address_line(order)}\n"
    )
    if order.get("note"):
        text += f"📝 {order['note']}\n"
    if not (order.get("phone") or "").strip():
        text += t("receipt_nophone", lang)
    text += t("receipt_tail", lang)
    return text

def cashback_line_for_customer(order, lang):
    used = order_cashback_used(order)
    if used <= 0:
        return ""
    return t("cb_receipt_line", lang, amt=fmt_sum(used), pay=fmt_sum(order_payable(order)))

def discount_line_for_customer(order, lang):
    pct = order.get("discount_percent") or 0
    old = order.get("original_total")
    if not pct or not old or old <= order.get("total", 0):
        return ""
    return t("discount_line", lang, pct=pct,
             old=fmt_sum(old), new=fmt_sum(order["total"]))

def order_items_text(order):
    lines = []
    for it in order["items"]:
        line = f"{it['name']} × {it['qty']} = {fmt_sum(it['price']*it['qty'])}"
        if it.get("cancelled"):
            line = f"❌ {line}  (bekor qilindi)"
        lines.append(line)
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
    out, line = [], ""
    for word in str(text).split():
        if not line:
            line = word
        elif len(line) + 1 + len(word) <= width:
            line += " " + word
        else:
            out.append(line); line = word
    if line:
        out.append(line)
    return out or [""]

def build_receipt_lines(order, width=None, safe=True, header=True):
    """Termoprinter uchun chek matni — oddiy qatorlar ro'yxati.
    header=False — tepaga logo rasmi chiqadi, nom yozuvi kerak emas."""
    w = width or RECEIPT_WIDTH
    L = []
    if header:
        L.append(BUSINESS_NAME.upper().center(w).rstrip())
    L.append("-" * w)
    created = datetime.fromtimestamp(order.get("created_at", int(time.time())), TIMEZONE)
    L.append(_rline(f"Buyurtma #{order.get('daily_number', '?')}", created.strftime("%d.%m %H:%M"), w))
    L.append("")
    L.append(f"Mijoz: {order.get('customer_name') or '-'}")
    tel = (order.get("phone") or "").strip()
    L.append(f"Tel: {tel}" if tel else "Tel: yo'q (Telegram orqali)")
    if order.get("username"):
        L.append(f"TG: @{order['username']}")
    if order.get("latitude") is not None:
        L.append("Manzil: xaritada yuborilgan")
        L.append(f"  {order['latitude']:.5f}, {order['longitude']:.5f}")
    else:
        for i, ln in enumerate(_wrap(order.get("address_text") or "-", w - 8)):
            L.append(("Manzil: " if i == 0 else "        ") + ln)
    L.append("-" * w)

    for it in order.get("items", []):
        if it.get("cancelled"):
            continue
        L.append(it["name"][:w])
        L.append(_rline(f"  {it['qty']} x {it['price']:.0f}", f"{it['price'] * it['qty']:.0f}", w))

    L.append("-" * w)
    pct = order.get("discount_percent") or 0
    old = order.get("original_total")
    if pct and old and old > order.get("total", 0):
        L.append(_rline("Oldingi summa", f"{old:.0f}", w))
        L.append(_rline(f"Aksiya -{pct}%", f"-{old - order['total']:.0f}", w))
    L.append(_rline("JAMI", fmt_sum(order.get("total", 0)), w))
    used_cb = order_cashback_used(order)
    if used_cb > 0:
        L.append(_rline("Keshbek", "-" + fmt_sum(used_cb), w))
        L.append(_rline("TO'LOVGA", fmt_sum(order_payable(order)), w))
    L.append("")
    if used_cb > 0:
        L.append("To'lov: NAQD + KESHBEK".center(w).rstrip())
    else:
        L.append("To'lov: NAQD (yetkazishda)".center(w).rstrip())

    if order.get("note"):
        L.append("-" * w)
        L.append("IZOH:")
        for ln in _wrap(order["note"], w):
            L.append("  " + ln)

    L.append("-" * w)
    L.append("Rahmat! Yana kutamiz".center(w).rstrip())
    return [ascii_safe(x) for x in L] if safe else L

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
    """Admin ko'radigan pul qatorlari — keshbek ishlatilgan bo'lsa ajratib ko'rsatamiz."""
    used = order_cashback_used(order)
    if used <= 0:
        return f"\U0001F4B0 Jami: {fmt_sum(order.get('total', 0))} (naqd)\n"
    return (f"\U0001F4B0 Jami: {fmt_sum(order.get('total', 0))}\n"
            f"\U0001F4B3 Keshbek bilan: \u2212{fmt_sum(used)}\n"
            f"\U0001F4B5 Naqd olinadi: {fmt_sum(order_payable(order))}\n")

def order_address_line(order):
    if order.get("latitude") is not None:
        return "📍 Joylashuv quyida xarita orqali yuborildi"
    return f"📍 {order.get('address_text') or '—'}"

def order_contact_line(order):
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
            kb.add(types.InlineKeyboardButton(f"➖ {nom} ({it['qty']}) olib tashlash",
                                              callback_data=f"rmitem:{order['id']}:{idx}"))
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
        save_orders(orders)

    msg = "❌ Buyurtma bekor qilindi."
    if taken_back > 0:
        msg += f" Keshbek −{fmt_sum(taken_back)}."
    if refunded > 0:
        msg += f" Mijozga {fmt_sum(refunded)} keshbek qaytarildi."
    bot.answer_callback_query(call.id, msg)
    refresh_order_card(call, order)
    tell_customer(order, "order_cancelled", no=order["daily_number"])
    if refunded > 0:
        tell_customer(order, "cb_refunded", amt=fmt_sum(refunded), bal=fmt_sum(new_balance))

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
        save_orders(orders)
    msg = "♻️ Buyurtma qaytarildi."
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
        save_orders(orders)

    msg = f"➖ {it['name']} olib tashlandi."
    if given_back > 0:
        msg += f" {fmt_sum(given_back)} keshbek mijozga qaytarildi."
    bot.answer_callback_query(call.id, msg)
    refresh_order_card(call, order)
    tell_customer(order, "item_cancelled", no=order["daily_number"],
                  dish=it["name"], sum=fmt_sum(order["total"]))

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
    # Raqam majburiy emas: raqami bo'lmagan mijoz bilan bot orqali bog'lanamiz.
    # Lekin raqam ham, Telegram hisobi ham bo'lmasa — bog'lanishning iloji yo'q.
    if not phone and not user.get("id"):
        return jsonify({"error": "Telefon raqamingizni kiriting — aks holda siz bilan bog'lana olmaymiz."}), 400

    # keshbekni faqat shaxsi tasdiqlangan foydalanuvchi ishlata oladi —
    # imzosiz so'rov bilan birovning hisobidan yechib bo'lmaydi
    order, error = create_order(
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
    return jsonify({
        "ok": True,
        "order_id": order["daily_number"],
        "total": order["total"],
        "cashback_used": order_cashback_used(order),
        "payable": order_payable(order),
        "cashback_balance": cashback_balance(user.get("id")) if user.get("id") else 0,
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
    return jsonify({
        "active": cfg["active"],
        "percent": cfg["percent"],
        "balance": cashback_balance(uid) if uid else 0,
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
      display:block; margin:0 auto 2mm; max-width:100%;
      image-rendering:pixelated;
    }
    #printArea pre{ margin:0; font:inherit; white-space:pre; }
    @page{ margin:2mm; }
  }
</style>
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
    <button class="ghost" id="btAgain">Qayta chiqarish</button>
  </div>
  <div class="opts">
    <label><input type="checkbox" id="auto" checked> Avtomatik chiqarsin</label>
    <label><input type="checkbox" id="snd" checked> Ovoz</label>
    <label title="Chek tepasida nom yozuvi o'rniga logo rasmi chiqadi">
      <input type="checkbox" id="logo" checked> Logo bilan
      <img id="logoPrev" class="logoprev" alt="" hidden>
    </label>
    <label>Kengligi
      <select id="w">
        <option value="32">58 mm</option>
        <option value="48" selected>80 mm</option>
      </select>
    </label>
    <label>Usul
      <select id="mode">
        <option value="bt" selected>Bevosita Bluetooth</option>
        <option value="sys">Tizim orqali (RawBT)</option>
      </select>
    </label>
  </div>
</header>

<div id="printArea" aria-hidden="true"></div>

<main>
  <div class="msg info" id="hint">
    Printerni yoqing, telefon Bluetooth'ini yoqing, so'ng <b>“Printerni ulash”</b>ni bosing.
  </div>
  <div id="list"></div>

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

  async function connect(){
    if (!btSupported()){
      say("Bu brauzer Bluetooth printerni qo'llab-quvvatlamaydi. Android'da <b>Chrome</b> bilan oching, " +
          "yoki pastdagi “boshqa yo'l”dan foydalaning.", 'err');
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
      var svcs = await server.getPrimaryServices();
      for (var i=0; i<svcs.length && !chr; i++){
        var cs = await svcs[i].getCharacteristics();
        for (var j=0; j<cs.length; j++){
          if (cs[j].properties.write || cs[j].properties.writeWithoutResponse){ chr = cs[j]; break; }
        }
      }
      if (!chr) throw new Error('yozish kanali topilmadi');
      setState('Printer ulandi: ' + (dev.name || 'nomsiz'), true);
      say('✅ Printer ulandi. Yangi buyurtmalar o‘zi chiqadi.', 'ok');
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

  function dots(){ return $('w').value === '32' ? 384 : 576; }
  function logoOn(){ var c = $('logo'); return !!(c && c.checked && hasLogo); }

  function loadImage(src){
    return new Promise(function(res, rej){
      var im = new Image();
      im.onload = function(){ res(im); };
      im.onerror = function(){ rej(new Error('logo yuklanmadi')); };
      im.src = src;
    });
  }

  async function buildLogo(width){
    if (logoCache[width]) return logoCache[width];
    var im = await loadImage(url('/static/logo.jpg'));
    var maxH = 220;                                  // qog'oz behuda ketmasin
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

    // Floyd-Steinberg: kulrangni nuqtalarga taqsimlaymiz
    var bpr = w / 8;
    var bits = new Uint8Array(bpr * h);
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

    // GS v 0 — ESC/POS rastr buyrug'i
    var head = new Uint8Array([0x1d, 0x76, 0x30, 0x00,
                               bpr & 0xff, (bpr >> 8) & 0xff,
                               h & 0xff, (h >> 8) & 0xff]);
    var raster = new Uint8Array(head.length + bits.length);
    raster.set(head, 0); raster.set(bits, head.length);

    logoCache[width] = { bytes: raster, url: cv.toDataURL('image/png') };
    var pv = $('logoPrev');
    if (pv){ pv.src = logoCache[width].url; pv.hidden = false; }
    return logoCache[width];
  }

  function joinBytes(parts){
    var n = 0, i;
    for (i = 0; i < parts.length; i++) n += parts[i].length;
    var out = new Uint8Array(n), at = 0;
    for (i = 0; i < parts.length; i++){ out.set(parts[i], at); at += parts[i].length; }
    return out;
  }

  function escpos(text, logo){
    var enc = new TextEncoder();
    var parts = [new Uint8Array([0x1b,0x40, 0x1b,0x74,0x00])];   // reset + kodlash jadvali
    if (logo){
      parts.push(new Uint8Array([0x1b,0x61,0x01]));              // o'rtaga
      parts.push(logo.bytes);
      parts.push(new Uint8Array([0x0a, 0x1b,0x61,0x00]));        // chapga qaytaramiz
    }
    parts.push(enc.encode(text + "\\n"));
    parts.push(new Uint8Array([0x0a,0x0a,0x0a,0x0a, 0x1d,0x56,0x42,0x00])); // bo'sh joy + kesish
    return joinBytes(parts);
  }

  async function sendBytes(bytes){
    var CH = 180;                       // katta paketlarni bo'lib yuboramiz
    for (var i=0; i<bytes.length; i+=CH){
      var part = bytes.slice(i, i+CH);
      if (chr.writeValueWithoutResponse) await chr.writeValueWithoutResponse(part);
      else await chr.writeValue(part);
      await new Promise(function(r){ setTimeout(r, 22); });
    }
  }

  function systemPrint(text, logo){
    // Android chop etish oynasi ochiladi — u yerdan RawBT yoki printer xizmati tanlanadi
    var area = document.getElementById('printArea');
    area.innerHTML = '';
    if (logo){
      var im = document.createElement('img');
      im.className = 'plogo';
      im.src = logo.url;
      area.appendChild(im);
    }
    var pre = document.createElement('pre');
    pre.textContent = text;
    area.appendChild(pre);
    window.print();
  }

  function mode(){ return $('mode').value; }

  ['w','logo'].forEach(function(id){
    var el = document.getElementById(id);
    if (!el) return;
    el.addEventListener('change', function(){
      logoCache = {};                       // yangi kenglikka qayta tayyorlanadi
      seen = {};                            // cheklar yangi matn bilan qayta kelsin
      var list = document.getElementById('list');
      if (list) list.innerHTML = '';
      try{ localStorage.setItem('miqot_logo', $('logo').checked ? '1' : '0'); }catch(e){}
      if (logoOn()) buildLogo(dots()).catch(function(){});
      poll();
    });
  });
  try{
    var savedLogo = localStorage.getItem('miqot_logo');
    if (savedLogo === '0') $('logo').checked = false;
  }catch(e){}

  async function printText(text){
    var logo = null;
    if (logoOn()){
      try{
        logo = await buildLogo(dots());
      }catch(e){
        logo = null;
        say("Logo yuklanmadi — chek nom yozuvi bilan chiqadi.", 'info');
      }
    }
    if (mode() === 'sys'){ systemPrint(text, logo); return; }
    if (!chr) throw new Error('printer ulanmagan');
    await sendBytes(escpos(text, logo));
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
      await printText(o.receipt);
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
      var r = await fetch(url('/api/print/pending?w=' + $('w').value +
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

  $('btTest').addEventListener('click', async function(){
    var w = parseInt($('w').value, 10);
    var line = '-'.repeat(w);
    var t = [
      'MIQOT FOOD'.padStart(Math.floor((w + 10)/2)),
      line, 'SINOV CHEKI', line,
      'Agar bu matn to‘g‘ri chiqsa,'.slice(0,w),
      'printer tayyor.',
      line, ''
    ].join('\\n');
    if (mode() === 'bt' && !chr){ say('Avval printerni ulang.', 'err'); return; }
    try{ await printText(t); say('✅ Sinov cheki yuborildi.', 'ok'); }
    catch(e){ say('❌ Chiqmadi: ' + e.message, 'err'); }
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
      say("Tizim rejimi: har bir chek uchun Android chop etish oynasi ochiladi, " +
          "u yerdan <b>RawBT</b>ni tanlaysiz. Bu Bluetooth Classic printerlar uchun.", 'info');
    } else {
      $('auto').checked = true;
      say("Bevosita rejim: printerni ulasangiz cheklar o‘zi chiqadi.", 'info');
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

  if (!btSupported()){
    say("Bu brauzerda printerga bevosita ulab bo‘lmaydi (Android Chrome kerak). " +
        "Buyurtmalar baribir ko‘rinadi — “Matnni nusxalash” orqali chiqarasiz.", 'err');
  }

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

# ---------- oshxona printeri uchun API ----------

@app.route("/kitchen")
def kitchen_page():
    if not admin_from_request():
        return ("<h3 style='font-family:sans-serif;padding:24px;line-height:1.6'>Ruxsat yo'q.<br><br>"
                "Telegramda botga <b>/start</b> yuboring va \"🖨 Oshxona\" tugmasini bosing.</h3>"), 403
    return KITCHEN_PAGE_HTML, 200, {"Content-Type": "text/html; charset=utf-8"}

@app.route("/api/print/pending")
def api_print_pending():
    """Hali chop etilmagan buyurtmalar. Oshxona sahifasi shuni so'rab turadi."""
    if not admin_from_request():
        return jsonify({"error": "Ruxsat yo'q"}), 403
    try:
        width = int(request.args.get("w") or RECEIPT_WIDTH)
    except Exception:
        width = RECEIPT_WIDTH
    width = max(24, min(64, width))
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
            "items": [f"{it['name']} x{it['qty']}" for it in o.get("items", []) if not it.get("cancelled")],
            "receipt": build_receipt_text(o, width, header=not with_logo),
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

@bot.message_handler(commands=["keshbek", "cashback"])
def cmd_cashback(message):
    """Mijoz uchun — o'z balansi. Admin uchun — umumiy holat."""
    cfg = get_cashback_cfg()
    lang = get_user_lang(message.from_user.id, getattr(message.from_user, "language_code", None))
    parts = (message.text or "").split()

    if is_owner(message.chat.id):
        if len(parts) > 1:
            try:
                target = int(parts[1])
            except ValueError:
                bot.send_message(message.chat.id, "Foydalanish: /keshbek yoki /keshbek <user_id>")
                return
            rec = load_cashback().get(str(target)) or {}
            hist = (rec.get("history") or [])[-8:]
            lines = [f"\U0001F4B3 Mijoz {target}",
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
        bot.send_message(message.chat.id,
            "\U0001F4B3 Keshbek holati\n\n"
            f"Sozlama: {state}\n"
            f"Mijozlarda yig'ilgan: {fmt_sum(tot['balance'])}\n"
            f"Keshbegi bor mijozlar: {tot['people']} ta\n\n"
            "Boshqarish:\n"
            "/keshbek_foiz 5 — foizni o'zgartirish\n"
            "/keshbek_foiz 0 — keshbekni butunlay o'chirish\n"
            "/keshbek <user_id> — bitta mijozni ko'rish")
        return

    if not cfg["active"]:
        bot.send_message(message.chat.id, t("cb_off", lang))
        return
    bal = cashback_balance(message.from_user.id)
    key = "cb_balance" if bal > 0 else "cb_zero"
    bot.send_message(message.chat.id, t(key, lang, bal=fmt_sum(bal), pct=f"{cfg['percent']:g}"),
                     reply_markup=main_keyboard(message.from_user.id, message.from_user.username))

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

# ---------- ishga tushirish ----------

def run_bot_polling():
    bot.infinity_polling()

if __name__ == "__main__":
    qoshildi = backfill_users_from_history()
    if qoshildi:
        print(f"Eski buyurtmalardan {qoshildi} ta mijoz ro'yxatga qo'shildi.")
    threading.Thread(target=run_bot_polling, daemon=True).start()
    threading.Thread(target=daily_report_scheduler, daemon=True).start()
    port = int(os.environ.get("PORT", 8080))
    print(f"Mini App server {port}-portda ishga tushdi, bot polling fonda ishlayapti...")
    app.run(host="0.0.0.0", port=port)
