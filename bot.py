# -*- coding: utf-8 -*-
"""
Oshxona uchun Telegram bot + Mini App (professional buyurtma ilovasi).

- Mijoz: /start -> "🛍 Buyurtma berish" (Mini App) yoki oddiy chat orqali menyu/savat
- Har bir buyurtmada mijozning Telegram username va doimiy ID'si avtomatik yoziladi
- Egasi (OWNER_CHAT_ID): yangi buyurtma haqida xabar oladi, mijozga to'g'ridan-to'g'ri
  yozish tugmasi bilan, va holatni o'zgartiradi.
- Mijoz "✉️ Savol / Murojaat" tugmasi orqali botga yozadi -> xabar OWNER_CHAT_ID'ga
  keladi (mijozning shaxsiy akkaunti egaga ochilmaydi). Ega o'sha xabarga *reply*
  qilsa, javob avtomatik mijozga bot orqali yetadi (ega ham shaxsini ochmaydi).

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
from datetime import datetime, timedelta, timezone

import requests as httpreq
import telebot
from telebot import types
from flask import Flask, request, jsonify, send_from_directory

BOT_TOKEN = os.environ.get("BOT_TOKEN", "TOKEN_BU_YERGA")
OWNER_CHAT_ID = int(os.environ.get("OWNER_CHAT_ID", "0"))
WEBAPP_URL = os.environ.get("WEBAPP_URL", "").rstrip("/")
BUSINESS_NAME = os.environ.get("BUSINESS_NAME", "Miqot Food")

DATA_DIR = os.environ.get("DATA_DIR", ".")
os.makedirs(DATA_DIR, exist_ok=True)

# Mahalliy vaqt zonasi - Saudiya Arabistoni doim UTC+3, yoz vaqtiga o'tish yo'q.
TZ = timezone(timedelta(hours=3))

def local_now():
    return datetime.now(TZ)

def local_date_str(ts):
    """Unix timestamp'ni mahalliy sana satriga o'giradi (masalan '2026-09-17')."""
    return datetime.fromtimestamp(ts, TZ).strftime("%Y-%m-%d")

MENU_FILE = os.path.join(DATA_DIR, "menu.json")
ORDERS_FILE = os.path.join(DATA_DIR, "orders.json")
SETTINGS_FILE = os.path.join(DATA_DIR, "settings.json")
DISH_PHOTOS_DIR = os.path.join(DATA_DIR, "static", "dishes")
LOGO_PATH = os.path.join(DATA_DIR, "static", "logo.jpg")

os.makedirs(DISH_PHOTOS_DIR, exist_ok=True)

bot = telebot.TeleBot(BOT_TOKEN)
app = Flask(__name__)

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

def next_daily_no(orders):
    """Bugun (mahalliy vaqt bo'yicha) uchun keyingi tartib raqamini beradi - har kuni 1'dan boshlanadi."""
    today = local_date_str(time.time())
    todays_orders = [o for o in orders if o.get("date") == today]
    return (max([o.get("daily_no", 0) for o in todays_orders], default=0)) + 1

carts = {}
checkout_state = {}

# --- "Adminga yozish" uchun holat ---
waiting_for_admin_message = set()   # xabar yozmoqchi bo'lgan mijozlar (user_id)
contact_map = {}                    # {ownerga_yuborilgan_xabar_id: mijoz_user_id}

def is_owner(chat_id):
    return chat_id == OWNER_CHAT_ID

def fmt_sum(n):
    return f"{n:,.0f} SAR".replace(",", " ")

def parse_dish_caption(text):
    parts = text.split(";")
    name = parts[0].strip()
    price = float(parts[1].strip())
    desc = parts[2].strip() if len(parts) > 2 else ""
    return name, price, desc

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

def main_keyboard(user_id=None, username=None):
    kb = types.ReplyKeyboardMarkup(resize_keyboard=True)
    if WEBAPP_URL and user_id:
        ts, sig = sign_user_params(user_id, username)
        params = f"uid={user_id}&uname={urllib.parse.quote(username or '')}&ts={ts}&sig={sig}&v={ts}"
        fresh_url = f"{WEBAPP_URL}?{params}"
        kb.row(types.KeyboardButton("🛍 Buyurtma berish", web_app=types.WebAppInfo(url=fresh_url)))
    kb.row(types.KeyboardButton("🍽 Menyu"), types.KeyboardButton("🛒 Savat"))
    kb.row(types.KeyboardButton("✉️ Savol / Murojaat"))
    return kb

# ---------- /start ----------

@bot.message_handler(commands=["start"])
def cmd_start(message):
    carts.pop(message.from_user.id, None)
    checkout_state.pop(message.from_user.id, None)
    waiting_for_admin_message.discard(message.from_user.id)
    welcome = (
        f"Assalomu alaykum! 👋\n{BUSINESS_NAME}ga xush kelibsiz.\n"
        "Pastdagi tugma orqali buyurtma bera boshlang:"
    )
    settings = load_settings()
    kb = main_keyboard(message.from_user.id, message.from_user.username)
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

def send_menu(chat_id):
    menu = sort_menu_by_availability(load_menu())
    if not menu:
        bot.send_message(chat_id, "Menyu hozircha bo'sh.")
        return
    for dish in menu:
        stock = dish.get("stock")
        sold_out = stock is not None and stock <= 0
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
        if dish.get("photo_id"):
            bot.send_photo(chat_id, dish["photo_id"], caption=caption, reply_markup=kb)
        else:
            bot.send_message(chat_id, caption, reply_markup=kb)
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
    for dish_id, qty in cart.items():
        dish = menu.get(dish_id)
        if not dish:
            continue
        line_total = dish["price"] * qty
        total += line_total
        lines.append(f"{dish['name']} × {qty} = {fmt_sum(line_total)}")
    text = "🛒 Savatingiz:\n" + "\n".join(lines) + f"\n\nJami: {fmt_sum(total)}"
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
    checkout_state[user_id] = {"step": "name"}
    bot.send_message(call.message.chat.id, "Ismingizni kiriting:", reply_markup=types.ReplyKeyboardRemove())
    bot.answer_callback_query(call.id)

def location_keyboard():
    kb = types.ReplyKeyboardMarkup(resize_keyboard=True, one_time_keyboard=True)
    kb.add(types.KeyboardButton("📍 Joylashuvimni yuborish", request_location=True))
    return kb

@bot.message_handler(func=lambda m: m.from_user.id in checkout_state, content_types=["text", "location"])
def handle_checkout_steps(message):
    user_id = message.from_user.id
    state = checkout_state[user_id]
    step = state["step"]

    if step == "name":
        if message.content_type != "text":
            return
        state["name"] = message.text.strip()
        state["step"] = "phone"
        bot.send_message(message.chat.id, "Telefon raqamingiz:")
        return

    if step == "phone":
        if message.content_type != "text":
            return
        state["phone"] = message.text.strip()
        state["step"] = "address"
        bot.send_message(
            message.chat.id,
            "Endi joylashuvingizni yuboring 📍\n"
            "Pastdagi tugmani bosing (eng aniq usul) — yoki manzilni yozib yuborishingiz ham mumkin.",
            reply_markup=location_keyboard()
        )
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
        bot.send_message(
            message.chat.id,
            "🙏 Rahmat! Buyurtmangiz qabul qilindi, tafsilotlar yuqorida.",
            reply_markup=main_keyboard(message.from_user.id, message.from_user.username)
        )
        return

# ---------- buyurtma yaratish (chat va Mini App uchun umumiy) ----------

def create_order(items_cart, customer_name, phone, latitude, longitude, address_text, note, tg_user_id, username):
    """Muvaffaqiyatli bo'lsa (order, None), zaxira yetmasa (None, xato_matni) qaytaradi."""
    full_menu = load_menu()
    menu = {d["id"]: d for d in full_menu}
    items = []
    total = 0
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
        items.append({"name": dish["name"], "price": dish["price"], "qty": qty})
        total += dish["price"] * qty

    if not items:
        return None, "Savat bo'sh."

    # zaxirani kamaytiramiz
    for dish, qty in parsed_cart:
        if dish.get("stock") is not None:
            dish["stock"] = max(0, dish["stock"] - qty)
    save_menu(full_menu)

    orders = load_orders()
    order = {
        "id": next_order_id(orders),
        "daily_no": next_daily_no(orders),
        "date": local_date_str(time.time()),
        "customer_name": customer_name,
        "phone": phone,
        "latitude": latitude,
        "longitude": longitude,
        "address_text": address_text,
        "note": note,
        "items": items,
        "total": total,
        "status": "Yangi",
        "payment": "naqd",
        "created_at": int(time.time()),
        "user_id": tg_user_id,
        "username": username,
    }
    orders.append(order)
    save_orders(orders)
    if OWNER_CHAT_ID:
        notify_owner_new_order(order)
    notify_customer_order(order)
    return order, None

def order_items_text(order):
    return "\n".join([f"{it['name']} × {it['qty']} = {fmt_sum(it['price']*it['qty'])}" for it in order["items"]])

def order_address_line(order):
    if order.get("latitude") is not None:
        return "📍 Joylashuv quyida xarita orqali yuborildi"
    return f"📍 {order.get('address_text') or '—'}"

def order_contact_line(order):
    if order.get("username"):
        return f"@{order['username']}"
    return "username yo'q"

def status_keyboard(order):
    kb = types.InlineKeyboardMarkup(row_width=2)
    kb.add(
        types.InlineKeyboardButton("👨‍🍳 Tayyorlanmoqda", callback_data=f"status:{order['id']}:Tayyorlanmoqda"),
        types.InlineKeyboardButton("🚴 Yo'lda", callback_data=f"status:{order['id']}:Yo'lda"),
    )
    kb.add(types.InlineKeyboardButton("✅ Yetkazildi", callback_data=f"status:{order['id']}:Yetkazildi"))
    # DIQQAT: bu yerda avval "tg://user?id=..." havolali tugma bor edi. Ba'zi
    # mijozlarning maxfiylik sozlamalari bunday havolani taqiqlaydi va Telegram
    # BUTTON_USER_PRIVACY_RESTRICTED xatosi bilan BUTUN xabarni rad etadi (shu
    # tugmalar ham, taom tafsilotlari ham yuborilmay qoladi). Shu sabab olib
    # tashlandi. Endi buyurtma xabariga oddiy REPLY qilib yozsangiz, javobingiz
    # mijozga bot orqali (shaxsiy havolasiz) yetadi - handle_owner_reply_to_customer
    # funksiyasiga qarang.
    return kb

def notify_owner_new_order(order):
    text = (
        f"🆕 Yangi buyurtma #{order['daily_no']} ({order['date']})\n\n"
        f"👤 {order['customer_name']} ({order_contact_line(order)})\n"
        f"📞 {order['phone']}\n"
        f"{order_address_line(order)}\n"
        + (f"📝 {order['note']}\n" if order.get('note') else "")
        + f"\n{order_items_text(order)}\n\n"
        f"💰 Jami: {fmt_sum(order['total'])} (naqd)\n"
        f"Holat: {order['status']}"
    )
    # MUHIM: bu funksiya hech qachon xato chiqarmasligi kerak. Buyurtma orders.json'ga
    # allaqachon saqlangan bo'ladi (shu funksiya chaqirilishidan oldin) - shuning uchun
    # bu yerdagi Telegram xatosi (flood limit, tarmoq va h.k.) mijozning "buyurtma
    # qabul qilindi" javobini buzmasligi kerak.
    try:
        if order.get("latitude") is not None:
            bot.send_location(OWNER_CHAT_ID, order["latitude"], order["longitude"])
        sent = bot.send_message(OWNER_CHAT_ID, text, reply_markup=status_keyboard(order))
        # Shu xabarga reply qilib yozsangiz ham, javobingiz mijozga bot orqali yetadi
        # (tg://user havolasiz, shaxsiy ma'lumot ochilmaydi).
        if order.get("user_id"):
            contact_map[sent.message_id] = order["user_id"]
    except Exception as e:
        print(f"[OGOHLANTIRISH] Buyurtma #{order['daily_no']} haqida to'liq xabar yuborilmadi: {e}")
        # Zaxira: hech bo'lmasa qisqa ogohlantiruvchi xabar yuborishga urinamiz,
        # shunda buyurtma diqqatingizdan chetda qolmaydi.
        try:
            bot.send_message(
                OWNER_CHAT_ID,
                f"🆕 Yangi buyurtma #{order['daily_no']} (to'liq xabar yuborishda xato chiqdi - "
                f"orders.json faylidan yoki /menu orqali tekshiring)"
            )
        except Exception:
            pass

def notify_customer_order(order):
    """Mijozga buyurtmasi haqida to'liq chek yuboradi - bot chatida saqlanib qoladi."""
    if not order.get("user_id"):
        return
    text = (
        f"✅ Buyurtmangiz qabul qilindi!\n\n"
        f"🧾 Buyurtma #{order['daily_no']} ({order['date']})\n\n"
        f"{order_items_text(order)}\n\n"
        f"💰 Jami: {fmt_sum(order['total'])}\n"
        f"💳 To'lov: naqd (yetkazib berilganda)\n"
        f"{order_address_line(order)}\n"
        f"📞 {order['phone']}\n\n"
        f"Holat: {order['status']}\n"
        f"Tez orada siz bilan bog'lanamiz."
    )
    try:
        bot.send_message(order["user_id"], text)
    except Exception as e:
        print(f"[OGOHLANTIRISH] Buyurtma #{order['daily_no']} - mijozga chek yuborilmadi: {e}")

@bot.callback_query_handler(func=lambda c: c.data.startswith("status:"))
def cb_update_status(call):
    if not is_owner(call.message.chat.id):
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
        f"📦 Buyurtma #{order['daily_no']} ({order['date']})\n\n"
        f"👤 {order['customer_name']} ({order_contact_line(order)})\n"
        f"📞 {order['phone']}\n"
        f"{order_address_line(order)}\n"
        + (f"📝 {order['note']}\n" if order.get('note') else "")
        + f"\n{order_items_text(order)}\n\n"
        f"💰 Jami: {fmt_sum(order['total'])} (naqd)\n"
        f"Holat: {new_status}"
    )
    try:
        bot.edit_message_text(text, call.message.chat.id, call.message.message_id,
                               reply_markup=status_keyboard(order))
    except Exception:
        pass
    bot.answer_callback_query(call.id, f"Holat yangilandi: {new_status}")

    try:
        bot.send_message(order["user_id"], f"Buyurtmangiz #{order['daily_no']} holati: {new_status}")
    except Exception:
        pass

# ---------- Mijoz -> Admin: "Savol / Murojaat" ----------

@bot.message_handler(func=lambda m: (
    m.text == "✉️ Savol / Murojaat"
    and not is_owner(m.chat.id)
    and m.from_user.id not in checkout_state
))
def handle_contact_button(message):
    waiting_for_admin_message.add(message.from_user.id)
    bot.send_message(
        message.chat.id,
        "Xabaringizni yozing, men uni administratorga yetkazaman:",
        reply_markup=types.ReplyKeyboardRemove()
    )

@bot.message_handler(func=lambda m: (
    m.from_user.id in waiting_for_admin_message
    and m.from_user.id not in checkout_state
), content_types=["text"])
def handle_customer_message_to_admin(message):
    waiting_for_admin_message.discard(message.from_user.id)
    user = message.from_user

    # mijozning oxirgi buyurtmasini topamiz (bo'lsa) - kontekst uchun
    orders = load_orders()
    last_order = None
    for o in reversed(orders):
        if o.get("user_id") == user.id:
            last_order = o
            break

    contact_info = f"@{user.username}" if user.username else "username yo'q"
    header = f"📩 Yangi murojaat\n👤 {user.first_name or ''} ({contact_info}, ID: {user.id})\n"
    if last_order:
        header += f"🧾 Oxirgi buyurtma: #{last_order.get('daily_no', last_order['id'])} ({last_order.get('date', '')}) — {last_order['status']}\n"
    header += f"\n\"{message.text}\"\n\n(Javob berish uchun shu xabarga reply qiling)"

    sent = bot.send_message(OWNER_CHAT_ID, header)
    contact_map[sent.message_id] = user.id

    bot.send_message(
        message.chat.id,
        "✅ Xabaringiz yuborildi. Tez orada javob beramiz.",
        reply_markup=main_keyboard(user.id, user.username)
    )

@bot.message_handler(func=lambda m: (
    is_owner(m.chat.id)
    and m.reply_to_message is not None
    and m.reply_to_message.message_id in contact_map
), content_types=["text"])
def handle_owner_reply_to_customer(message):
    customer_id = contact_map[message.reply_to_message.message_id]
    try:
        bot.send_message(customer_id, f"✉️ Administrator javobi:\n{message.text}")
        bot.send_message(message.chat.id, "✅ Javob mijozga yuborildi.")
    except Exception as e:
        bot.send_message(message.chat.id, f"❌ Yuborilmadi (mijoz botni bloklagan bo'lishi mumkin): {e}")

# ---------- admin: menyuni boshqarish ----------

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
        line = f"#{d['id']} — {d['name']} — {fmt_sum(d['price'])}"
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
        "\n\nZaxira belgilash: /set_stock id soni (masalan: /set_stock 1 10)\n"
        "Barchasini \"Tugadi\" qilish (ishlamagan kun): /reset_stock\n"
        "Cheklovni olib tashlash: /set_stock id -1"
    )

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
        name, price, desc = parse_dish_caption(payload)
    except Exception:
        bot.send_message(message.chat.id, "Format: /add_dish Nomi;Narxi;Tavsif")
        return
    menu = load_menu()
    new_id = (max([d["id"] for d in menu], default=0)) + 1
    menu.append({"id": new_id, "name": name, "price": price, "desc": desc, "photo_id": None, "local_photo": None, "stock": 0})
    save_menu(menu)
    bot.send_message(message.chat.id, f"Qo'shildi (rasmsiz): #{new_id} {name} — {fmt_sum(price)}\n"
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
            "Taom rasmini caption bilan yuboring: Nomi;Narxi;Tavsif\n"
            "Yoki logotip sifatida saqlash uchun caption'ga \"logo\" deb yozing."
        )
        return

    try:
        name, price, desc = parse_dish_caption(caption)
    except Exception:
        bot.send_message(message.chat.id, "Caption formati noto'g'ri. Namuna: Osh;35;Palov go'shtli")
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
        "photo_id": photo_id, "local_photo": local_filename, "stock": 0
    })
    save_menu(menu)
    bot.send_message(message.chat.id, f"Qo'shildi (rasm bilan): #{new_id} {name} — {fmt_sum(price)}\n"
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

# ---------- kunlik hisobot ----------

def build_daily_report(date_str):
    orders = load_orders()
    days_orders = [o for o in orders if o.get("date") == date_str]
    if not days_orders:
        return f"📊 {date_str} kuni uchun buyurtmalar bo'lmadi."

    total_revenue = sum(o["total"] for o in days_orders)
    count = len(days_orders)

    dish_counts = {}
    for o in days_orders:
        for it in o["items"]:
            dish_counts[it["name"]] = dish_counts.get(it["name"], 0) + it["qty"]
    top_dishes = sorted(dish_counts.items(), key=lambda x: -x[1])[:5]

    lines = [
        f"📊 {date_str} kunlik hisobot",
        "",
        f"🧾 Buyurtmalar soni: {count}",
        f"💰 Jami savdo: {fmt_sum(total_revenue)}",
    ]
    if top_dishes:
        lines.append("")
        lines.append("🍽 Eng ko'p buyurtma qilingan taomlar:")
        for name, qty in top_dishes:
            lines.append(f"  • {name} — {qty} dona")
    return "\n".join(lines)

@bot.message_handler(commands=["hisobot"])
def cmd_report(message):
    if not is_owner(message.chat.id):
        return
    today_str = local_date_str(time.time())
    bot.send_message(message.chat.id, build_daily_report(today_str))

def daily_report_scheduler():
    """Har kuni mahalliy 00:01'da o'tgan kunning savdo hisobotini avtomatik yuboradi."""
    while True:
        now = local_now()
        next_run = (now + timedelta(days=1)).replace(hour=0, minute=1, second=0, microsecond=0)
        sleep_seconds = (next_run - now).total_seconds()
        time.sleep(max(sleep_seconds, 1))
        yesterday_str = (local_now() - timedelta(days=1)).strftime("%Y-%m-%d")
        if OWNER_CHAT_ID:
            try:
                bot.send_message(OWNER_CHAT_ID, build_daily_report(yesterday_str))
            except Exception as e:
                print(f"[OGOHLANTIRISH] Kunlik hisobotni yuborishda xato: {e}")

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
    menu = sort_menu_by_availability(load_menu())
    out = []
    for d in menu:
        item = {"id": d["id"], "name": d["name"], "price": d["price"], "desc": d.get("desc", ""), "stock": d.get("stock")}
        if d.get("local_photo"):
            item["photo_url"] = f"/static/dishes/{d['local_photo']}"
        out.append(item)
    return jsonify({
        "menu": out,
        "business_name": BUSINESS_NAME,
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

@app.route("/api/order", methods=["POST"])
def api_order():
    try:
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

        if not phone or not items_cart:
            return jsonify({"error": "Ma'lumotlar to'liq emas"}), 400

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
        return jsonify({"ok": True, "order_id": order["id"], "daily_order_no": order["daily_no"], "total": order["total"]})
    except Exception as e:
        # Kutilmagan xato bo'lsa ham, mijozga tushunarli javob va serverga
        # tekshirish uchun log qoldiramiz (Railway loglarida ko'rinadi).
        print(f"[XATO] /api/order da kutilmagan muammo: {e}")
        return jsonify({"error": "Server xatoligi. Iltimos, qayta urinib ko'ring."}), 500

# ---------- ishga tushirish ----------

def run_bot_polling():
    bot.infinity_polling()

if __name__ == "__main__":
    threading.Thread(target=run_bot_polling, daemon=True).start()
    threading.Thread(target=daily_report_scheduler, daemon=True).start()
    port = int(os.environ.get("PORT", 8080))
    print(f"Mini App server {port}-portda ishga tushdi, bot polling fonda ishlayapti...")
    app.run(host="0.0.0.0", port=port)
