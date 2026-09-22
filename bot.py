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

CATEGORIES = ["Nonushta", "Ovqatlar", "Salatlar", "Salqin ichimliklar", "Boshqa mahsulotlar"]
DEFAULT_CATEGORY = "Boshqa mahsulotlar"
CATEGORY_EMOJI = {
    "Nonushta": "🍳",
    "Ovqatlar": "🍲",
    "Salatlar": "🥗",
    "Salqin ichimliklar": "🥤",
    "Boshqa mahsulotlar": "🍽",
}

def match_category(raw):
    if not raw:
        return DEFAULT_CATEGORY
    raw = raw.strip().lower()
    for c in CATEGORIES:
        if c.lower() == raw:
            return c
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

def main_keyboard(user_id=None, username=None):
    kb = types.ReplyKeyboardMarkup(resize_keyboard=True)
    if WEBAPP_URL and user_id:
        ts, sig = sign_user_params(user_id, username)
        params = f"uid={user_id}&uname={urllib.parse.quote(username or '')}&ts={ts}&sig={sig}&v={ts}"
        fresh_url = f"{WEBAPP_URL}?{params}"
        kb.row(types.KeyboardButton("🛍 Buyurtma berish", web_app=types.WebAppInfo(url=fresh_url)))
    kb.row(types.KeyboardButton("💬 Biz bilan bog'lanish"))
    return kb

# ---------- /start ----------

@bot.message_handler(commands=["start"])
def cmd_start(message):
    carts.pop(message.from_user.id, None)
    checkout_state.pop(message.from_user.id, None)
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

def group_menu_by_category(menu):
    """Kategoriya bo'yicha guruhlaydi (CATEGORIES tartibida), har bir guruh ichida
    mavjud taomlar avval, tugaganlari oxirida keladi. Bo'sh kategoriyalar tashlab ketiladi."""
    groups = []
    for cat in CATEGORIES:
        items = [d for d in menu if d.get("category", DEFAULT_CATEGORY) == cat]
        if items:
            groups.append((cat, sort_menu_by_availability(items)))
    return groups

def send_menu(chat_id):
    menu = load_menu()
    if not menu:
        bot.send_message(chat_id, "Menyu hozircha bo'sh.")
        return
    for category, dishes in group_menu_by_category(menu):
        emoji = CATEGORY_EMOJI.get(category, "🍽")
        bot.send_message(chat_id, f"{emoji} {category.upper()}")
        for dish in dishes:
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
        # Chek create_order ichida avtomatik mijozga yuboriladi — bu yerda qayta yuborish shart emas.
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

def build_customer_receipt_text(order):
    text = (
        f"✅ Buyurtmangiz qabul qilindi! (#{order['daily_number']})\n\n"
        f"{order_items_text(order)}\n\n"
        f"💰 Jami: {fmt_sum(order['total'])} (naqd — yetkazib berilganda)\n"
        f"{order_address_line(order)}\n"
    )
    if order.get("note"):
        text += f"📝 {order['note']}\n"
    text += "\nTez orada siz bilan bog'lanamiz. Holat o'zgarganda sizga xabar boradi."
    return text

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
            f"📞 {order['phone']}\n"
            f"{order_address_line(order)}\n"
            + (f"📝 {order['note']}\n" if order.get('note') else "")
            + f"\n{order_items_text(order)}\n\n"
            f"💰 Jami: {fmt_sum(order['total'])} (naqd)\n"
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
            bot.send_message(recipient_id, text, reply_markup=kb)
        except Exception as e:
            print(f"Buyurtma matnini yuborishda xato ({recipient_id}): {e}")
            if "BUTTON_USER_PRIVACY_RESTRICTED" in str(e):
                try:
                    fallback_kb = status_keyboard(order, include_contact=False) if kb is not None else None
                    bot.send_message(recipient_id, text, reply_markup=fallback_kb)
                except Exception as e2:
                    print(f"Qayta urinishda ham xato ({recipient_id}): {e2}")

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
        bot.send_message(order["user_id"], f"Buyurtmangiz #{order['daily_number']} holati: {new_status}")
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
        "\n\nZaxira belgilash: /set_stock id soni (masalan: /set_stock 1 10)\n"
        "Barchasini \"Tugadi\" qilish (ishlamagan kun): /reset_stock\n"
        "Cheklovni olib tashlash: /set_stock id -1\n"
        f"Kategoriya o'zgartirish: /set_category id Kategoriya (masalan: /set_category 1 Ovqatlar)\n"
        f"Kategoriyalar: {', '.join(CATEGORIES)}\n\n"
        "Hisobot: /report (bugungi), /yesterday_report (kechagi)\n"
        "Admin qo'shish: /add_admin id | /remove_admin id | /admins\n"
        "Xodim qo'shish (faqat holat o'zgartira oladi): /add_staff id | /remove_staff id\n"
        "Buyurtmani o'chirish (faqat bugungi): /delete_order kunlik_raqami"
    )

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
    grouped = group_menu_by_category(menu)
    out = []
    for d in menu:
        item = {
            "id": d["id"], "name": d["name"], "price": d["price"],
            "desc": d.get("desc", ""), "stock": d.get("stock"),
            "category": d.get("category", DEFAULT_CATEGORY)
        }
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
    return jsonify({"ok": True, "order_id": order["daily_number"], "total": order["total"]})

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

@bot.message_handler(func=lambda m: m.text == "💬 Biz bilan bog'lanish")
def handle_contact_button(message):
    bot.send_message(
        message.chat.id,
        "✍️ Savolingiz yoki fikringizni shu yerga yozing — tez orada javob beramiz."
    )

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
        bot.send_message(customer_id, f"💬 Miqot Food'dan javob:\n{message.text}")
        bot.send_message(message.chat.id, "✅ Javobingiz mijozga yuborildi.")
    except Exception:
        bot.send_message(message.chat.id, "❌ Yuborib bo'lmadi — mijoz botni bloklagan bo'lishi mumkin.")

@bot.message_handler(
    func=lambda m: (
        m.content_type == "text"
        and not m.text.startswith("/")
        and m.from_user.id not in checkout_state
        and not is_staff_or_admin(m.from_user.id)
        and m.text != "💬 Biz bilan bog'lanish"
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
    bot.send_message(message.chat.id, "✅ Xabaringiz qabul qilindi, tez orada javob beramiz.")

# ---------- ishga tushirish ----------

def run_bot_polling():
    bot.infinity_polling()

if __name__ == "__main__":
    threading.Thread(target=run_bot_polling, daemon=True).start()
    threading.Thread(target=daily_report_scheduler, daemon=True).start()
    port = int(os.environ.get("PORT", 8080))
    print(f"Mini App server {port}-portda ishga tushdi, bot polling fonda ishlayapti...")
    app.run(host="0.0.0.0", port=port)
