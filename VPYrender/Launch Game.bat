@echo off
setlocal
cd /d "%~dp0"

set "PYTHON_CMD="
py -3 --version >nul 2>&1
if not errorlevel 1 set "PYTHON_CMD=py -3"
if defined PYTHON_CMD goto :install_packages

python --version >nul 2>&1
if not errorlevel 1 set "PYTHON_CMD=python"
if defined PYTHON_CMD goto :install_packages

echo Python was not found. Opening the Microsoft Store...
start "" "ms-windows-store://search/?query=Python%203.13"
echo Install Python 3.13 from the Store, then return here and press a key.
pause >nul

py -3 --version >nul 2>&1
if not errorlevel 1 set "PYTHON_CMD=py -3"
if not defined PYTHON_CMD (
    python --version >nul 2>&1
    if not errorlevel 1 set "PYTHON_CMD=python"
)
if not defined PYTHON_CMD goto :python_missing

:install_packages
call %PYTHON_CMD% -c "import pygame, VPYrender" >nul 2>&1
if errorlevel 1 (
    echo Installing the game's Python packages...
    call %PYTHON_CMD% -m ensurepip --upgrade
    if errorlevel 1 goto :package_install_failed
    call %PYTHON_CMD% -m pip install --user pygame VPYrender
    if errorlevel 1 goto :package_install_failed
)

call %PYTHON_CMD% main.py
if errorlevel 1 goto :game_failed
exit /b 0

:python_missing
echo Python is still unavailable. Install Python 3.13 from the Microsoft Store and run this launcher again.
goto :failed

:package_install_failed
echo The required Python packages could not be installed.
goto :failed

:game_failed
echo The game exited with an error.

:failed
echo.
pause
exit /b 1
