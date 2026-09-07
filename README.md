# Oshxona Telegram boti — o'rnatish yo'riqnomasi

## 1. Bot yaratish (BotFather orqali)
1. Telegram'da **@BotFather** ni oching.
2. `/newbot` buyrug'ini yuboring, botga nom va username bering.
3. Sizga bir qatorli **TOKEN** beriladi — uni saqlab qo'ying (masalan: `123456:ABC-DEF...`).

## 2. O'zingizning Telegram chat ID'ingizni bilib oling
1. Telegram'da **@userinfobot** ni oching va `/start` bosing.
2. U sizga raqamli **ID** ni yuboradi (masalan: `987654321`). Shu — sizning `OWNER_CHAT_ID`.

## 3. Kodni ishga tushirish (Railway.app orqali, bepul)
1. https://railway.app saytida ro'yxatdan o'ting (GitHub akkaunt bilan kirsa bo'ladi).
2. "New Project" → "Deploy from GitHub repo" — shu papkadagi fayllarni GitHub'ga yuklab, ulang.
   (Agar GitHub bilan ishlamasangiz, menga ayting — boshqa usulini ham aytib beraman.)
3. Railway loyihasining **Variables** bo'limiga kiring va quyidagilarni qo'shing:
   - `BOT_TOKEN` = 1-qadamda olingan token
   - `OWNER_CHAT_ID` = 2-qadamda olingan ID
4. Railway avtomatik `requirements.txt` va `Procfile`ni o'qib, botni ishga tushiradi.

## 4. Botni sinab ko'rish
1. Telegram'da o'z botingizni toping va `/start` bosing.
2. "Menyuni ko'rish" tugmasini bosib, taom tanlang.
3. Savatga qo'shib, "Buyurtma berish" tugmasini bosing, ism/telefon/manzil kiriting.
4. Buyurtma yuborilgach, **sizga (OWNER_CHAT_ID)** darhol xabar keladi — tugmalar orqali holatini
   ("Tayyorlanmoqda", "Yo'lda", "Yetkazildi") o'zgartira olasiz.

## 5. Menyuni boshqarish (siz — bot egasi sifatida)
Botga shu buyruqlarni yuboring:
- `/menu` — hozirgi menyuni ko'rish (id raqamlari bilan)
- `/add_dish Nomi;Narxi;Tavsif` — masalan: `/add_dish Lag'mon;30;Qo'lda tayyorlangan`
- `/remove_dish id` — masalan: `/remove_dish 2`

## Eslatma
- Hozircha to'lov faqat **naqd (yetkazib berishda)**. Karta orqali onlayn to'lovni keyin
  HyperPay/PayTabs/Tap Payments kabi tizim orqali ulash mumkin.
- Ma'lumotlar oddiy `menu.json` va `orders.json` fayllarida saqlanadi — kichik biznes uchun yetarli.
