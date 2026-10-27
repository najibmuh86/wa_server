# WhatsApp Server (WhatsApp Web, tanpa API resmi)

Server web untuk membaca dan membalas WhatsApp dari beberapa user lewat browser. Login user memakai
Google Apps Script (tab `USER_CLIENT`), pesan dicatat ke Google Sheet.

## Persiapan
1. Pasang Python 3.10+ dan Google Chrome.
2. `pip install -r requirements.txt`
3. Salin `config.example.json` menjadi `config.json` lalu isi `WEB_APP_URL` dengan URL deployment Apps Script Anda
   (atau biarkan kosong, program akan menanyakannya saat pertama dijalankan).

## Menjalankan
- Mode jendela: klik dua kali `wa_server.pyw`
- Mode cmd: `jalankan_cmd.bat` (tambahkan `--tampil` untuk menampilkan Chrome saat scan QR pertama kali)
- Membuat exe: `buat_exe.bat` -> `wa_server_cmd.exe`

Client lain membuka `http://IP-SERVER:5000` di browser.

## Keamanan
File berikut dibuat otomatis saat program berjalan dan **tidak boleh diunggah** (sudah ada di `.gitignore`):
`wa_profile/` (sesi WhatsApp), `messages.jsonl` & `wa_images/` (isi chat), `secret.key`, `config.json`, `roles.json`, dll.
<img width="1677" height="586" alt="image" src="https://github.com/user-attachments/assets/2815810e-7cf3-4e80-a750-2d6c35b22557" />
<img width="1912" height="344" alt="image" src="https://github.com/user-attachments/assets/c2e20953-49bf-4d97-abaa-2c188f9475f0" />
<img width="1908" height="771" alt="image" src="https://github.com/user-attachments/assets/32ecbb92-f048-4ce6-96f8-05527c15f569" />
