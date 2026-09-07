# -*- coding: utf-8 -*-
"""
Oshxona uchun Telegram bot.
- Mijoz: /start -> menyu (rasmlar bilan) -> savat -> buyurtma (ism, telefon, lokatsiya)
- Egasi (OWNER_CHAT_ID): har bir yangi buyurtma haqida xabar oladi (mijozning joylashuvi xarita
  ko'rinishida ham keladi) va tugmalar orqali holatini o'zgartiradi.
- Admin buyruqlari (faqat OWNER_CHAT_ID uchun):
    /menu                 - menyudagi taomlar ro'yxati (id bilan)
    /add_dish             - Nomi;Narxi;Tavsif  (rasmsiz qo'shish uchun)
    /remove_dish id       - taomni o'chirish
    RASM + caption        - rasmga "Nomi;Narxi;Tavsif" deb yozib yuborsangiz, taom rasm bilan qo'shiladi
"""

import json
import os
import time
import telebot
from telebot import types

BOT_TOKEN = os.environ.get("BOT_TOKEN", "TOKEN_BU_YERGA")
OWNER_CHAT_ID = int(os.environ.get("OWNER_CHAT_ID", "0"))

MENU_FILE = "menu.json"
ORDERS_FILE = "orders.json"

bot = telebot.TeleBot(BOT_TOKEN)

# ---------- yordamchi funksiyalar: fayl bilan ishlash ----------

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

def next_order_id(orders):
    return (max([o["id"] for o in orders], default=0)) + 1

# xotiradagi holat: har bir mijozning savati va checkout bosqichi
carts = {}            # user_id -> {dish_id: qty}
checkout_state = {}   # user_id -> {"step": "name"/"phone"/"address", "name":..., "phone":...}

def is_owner(chat_id):
    return chat_id == OWNER_CHAT_ID

def fmt_sum(n):
    return f"{n:,.0f} SAR".replace(",", " ")

def parse_dish_caption(text):
    """'Nomi;Narxi;Tavsif' formatini o'qiydi."""
    parts = text.split(";")
    name = parts[0].strip()
    price = float(parts[1].strip())
    desc = parts[2].strip() if len(parts) > 2 else ""
    return name, price, desc

# ---------- /start ----------

@bot.message_handler(commands=["start"])
def cmd_start(message):
    carts.pop(message.from_user.id, None)
    checkout_state.pop(message.from_user.id, None)
    kb = types.InlineKeyboardMarkup()
    kb.add(types.InlineKeyboardButton("🍽 Menyuni ko'rish", callback_data="show_menu"))
    bot.send_message(
        message.chat.id,
        "Assalomu alaykum! 👋\nUy oshxonamizga xush kelibsiz.\nBuyurtma berish uchun menyuni ko'ring:",
        reply_markup=kb
    )

# ---------- menyuni ko'rsatish (har bir taom alohida xabar, rasm bilan) ----------

@bot.callback_query_handler(func=lambda c: c.data == "show_menu")
def cb_show_menu(call):
    menu = load_menu()
    if not menu:
        bot.answer_callback_query(call.id, "Menyu hozircha bo'sh.")
        return
    for dish in menu:
        caption = f"{dish['name']} — {fmt_sum(dish['price'])}"
        if dish.get("desc"):
            caption += f"\n{dish['desc']}"
        kb = types.InlineKeyboardMarkup()
        kb.add(types.InlineKeyboardButton("➕ Savatga qo'shish", callback_data=f"add:{dish['id']}"))
        if dish.get("photo_id"):
            bot.send_photo(call.message.chat.id, dish["photo_id"], caption=caption, reply_markup=kb)
        else:
            bot.send_message(call.message.chat.id, caption, reply_markup=kb)
    kb_cart = types.InlineKeyboardMarkup()
    kb_cart.add(types.InlineKeyboardButton("🛒 Savatni ko'rish", callback_data="show_cart"))
    bot.send_message(call.message.chat.id, "Tanlab bo'lgach, savatni ko'ring:", reply_markup=kb_cart)
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
    cart[dish_id] = cart.get(dish_id, 0) + 1
    bot.answer_callback_query(call.id, f"{dish['name']} savatga qo'shildi ✅")

# ---------- savat ----------

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

@bot.callback_query_handler(func=lambda c: c.data == "show_cart")
def cb_show_cart(call):
    text, _ = cart_summary_text(call.from_user.id)
    bot.send_message(call.message.chat.id, text, reply_markup=build_cart_keyboard(call.from_user.id))
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

# ---------- checkout (ism -> telefon -> lokatsiya) ----------

@bot.callback_query_handler(func=lambda c: c.data == "checkout")
def cb_checkout(call):
    user_id = call.from_user.id
    if not carts.get(user_id):
        bot.answer_callback_query(call.id, "Savatingiz bo'sh.")
        return
    checkout_state[user_id] = {"step": "name"}
    bot.send_message(call.message.chat.id, "Ismingizni kiriting:")
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
            "Pastdagi tugmani bosing (eng aniq usul) — yoki xohlasangiz manzilni yozib yuborishingiz ham mumkin.",
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
        finalize_order(message, user_id, state)
        checkout_state.pop(user_id, None)
        return

def finalize_order(message, user_id, state):
    menu = {d["id"]: d for d in load_menu()}
    cart = carts.get(user_id, {})
    items = []
    total = 0
    for dish_id, qty in cart.items():
        dish = menu.get(dish_id)
        if not dish:
            continue
        items.append({"name": dish["name"], "price": dish["price"], "qty": qty})
        total += dish["price"] * qty

    orders = load_orders()
    order = {
        "id": next_order_id(orders),
        "customer_name": state["name"],
        "phone": state["phone"],
        "latitude": state.get("latitude"),
        "longitude": state.get("longitude"),
        "address_text": state.get("address_text"),
        "items": items,
        "total": total,
        "status": "Yangi",
        "payment": "naqd",
        "created_at": int(time.time()),
        "user_id": user_id,
    }
    orders.append(order)
    save_orders(orders)
    carts[user_id] = {}

    bot.send_message(
        message.chat.id,
        f"✅ Buyurtmangiz qabul qilindi!\nJami: {fmt_sum(total)}\n"
        f"To'lov: yetkazib berilganda naqd.\nTez orada siz bilan bog'lanamiz.",
        reply_markup=types.ReplyKeyboardRemove()
    )

    if OWNER_CHAT_ID:
        notify_owner_new_order(order)

def order_items_text(order):
    return "\n".join([f"{it['name']} × {it['qty']} = {fmt_sum(it['price']*it['qty'])}" for it in order["items"]])

def order_address_line(order):
    if order.get("latitude") is not None:
        return "📍 Joylashuv quyida xarita orqali yuborildi"
    return f"📍 {order.get('address_text') or '—'}"

def status_keyboard(order_id):
    kb = types.InlineKeyboardMarkup(row_width=2)
    kb.add(
        types.InlineKeyboardButton("👨‍🍳 Tayyorlanmoqda", callback_data=f"status:{order_id}:Tayyorlanmoqda"),
        types.InlineKeyboardButton("🚴 Yo'lda", callback_data=f"status:{order_id}:Yo'lda"),
    )
    kb.add(types.InlineKeyboardButton("✅ Yetkazildi", callback_data=f"status:{order_id}:Yetkazildi"))
    return kb

def notify_owner_new_order(order):
    text = (
        f"🆕 Yangi buyurtma #{order['id']}\n\n"
        f"👤 {order['customer_name']}\n"
        f"📞 {order['phone']}\n"
        f"{order_address_line(order)}\n\n"
        f"{order_items_text(order)}\n\n"
        f"💰 Jami: {fmt_sum(order['total'])} (naqd)\n"
        f"Holat: {order['status']}"
    )
    if order.get("latitude") is not None:
        bot.send_location(OWNER_CHAT_ID, order["latitude"], order["longitude"])
    bot.send_message(OWNER_CHAT_ID, text, reply_markup=status_keyboard(order["id"]))

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
        f"📦 Buyurtma #{order['id']}\n\n"
        f"👤 {order['customer_name']}\n"
        f"📞 {order['phone']}\n"
        f"{order_address_line(order)}\n\n"
        f"{order_items_text(order)}\n\n"
        f"💰 Jami: {fmt_sum(order['total'])} (naqd)\n"
        f"Holat: {new_status}"
    )
    try:
        bot.edit_message_text(text, call.message.chat.id, call.message.message_id,
                               reply_markup=status_keyboard(order_id))
    except Exception:
        pass
    bot.answer_callback_query(call.id, f"Holat yangilandi: {new_status}")

    try:
        bot.send_message(order["user_id"], f"Buyurtmangiz #{order['id']} holati: {new_status}")
    except Exception:
        pass

# ---------- admin: menyuni boshqarish ----------

@bot.message_handler(commands=["menu"])
def cmd_menu_admin(message):
    if not is_owner(message.chat.id):
        return
    menu = load_menu()
    if not menu:
        bot.send_message(message.chat.id, "Menyu bo'sh. Rasm + tavsif yuborib yoki /add_dish bilan qo'shing.")
        return
    lines = [f"#{d['id']} — {d['name']} — {fmt_sum(d['price'])}" + (f" ({d['desc']})" if d.get("desc") else "")
             + (" 🖼" if d.get("photo_id") else "")
             for d in menu]
    bot.send_message(message.chat.id, "Menyu:\n" + "\n".join(lines))

@bot.message_handler(commands=["add_dish"])
def cmd_add_dish(message):
    if not is_owner(message.chat.id):
        return
    try:
        payload = message.text.split(" ", 1)[1]
        name, price, desc = parse_dish_caption(payload)
    except Exception:
        bot.send_message(message.chat.id, "Format: /add_dish Nomi;Narxi;Tavsif\nMasalan: /add_dish Osh;35;Palov go'shtli")
        return
    menu = load_menu()
    new_id = (max([d["id"] for d in menu], default=0)) + 1
    menu.append({"id": new_id, "name": name, "price": price, "desc": desc, "photo_id": None})
    save_menu(menu)
    bot.send_message(message.chat.id, f"Qo'shildi (rasmsiz): #{new_id} {name} — {fmt_sum(price)}\n"
                                       f"Rasm qo'shish uchun rasmni caption bilan yuboring.")

@bot.message_handler(content_types=["photo"])
def handle_dish_photo(message):
    if not is_owner(message.chat.id):
        return
    if not message.caption:
        bot.send_message(
            message.chat.id,
            "Taom rasmini caption bilan yuboring.\nFormat: Nomi;Narxi;Tavsif\n"
            "Masalan: Osh;35;Palov go'shtli"
        )
        return
    try:
        name, price, desc = parse_dish_caption(message.caption)
    except Exception:
        bot.send_message(message.chat.id, "Caption formati noto'g'ri. Namuna: Osh;35;Palov go'shtli")
        return
    photo_id = message.photo[-1].file_id  # eng katta o'lchamdagi rasm
    menu = load_menu()
    new_id = (max([d["id"] for d in menu], default=0)) + 1
    menu.append({"id": new_id, "name": name, "price": price, "desc": desc, "photo_id": photo_id})
    save_menu(menu)
    bot.send_message(message.chat.id, f"Qo'shildi (rasm bilan): #{new_id} {name} — {fmt_sum(price)}")

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

# ---------- ishga tushirish ----------

if __name__ == "__main__":
    print("Bot ishga tushdi...")
    bot.infinity_polling()
