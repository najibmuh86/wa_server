@echo off
cd /d "%~dp0"
echo ============================================
echo  Membuat wa_server_cmd.exe  (jalan di cmd)
echo ============================================
echo.
python --version >nul 2>&1
if errorlevel 1 (
  echo Python belum terpasang / belum masuk PATH. Pasang dari python.org lalu ulangi.
  pause
  exit /b 1
)
python -m pip install --upgrade pyinstaller flask requests playwright
if errorlevel 1 goto gagal
python -m PyInstaller --noconfirm --clean --onefile --console --name wa_server_cmd --collect-all playwright wa_server.pyw
if errorlevel 1 goto gagal
copy /y "dist\wa_server_cmd.exe" "%~dp0wa_server_cmd.exe" >nul
echo.
echo SELESAI. Jalankan: wa_server_cmd.exe  (klik dua kali, atau lewat cmd)
echo Opsi:  wa_server_cmd.exe --tampil   (tampilkan Chrome)
pause
exit /b 0
:gagal
echo.
echo GAGAL membuat exe. Lihat pesan error di atas.
pause
exit /b 1
