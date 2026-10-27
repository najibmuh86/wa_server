@echo off
cd /d "%~dp0"
rem Jalankan WhatsApp Server di cmd (butuh Python). Contoh: jalankan_cmd.bat --tampil
python wa_server.pyw --cmd %*
pause
