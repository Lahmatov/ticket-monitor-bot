#!/bin/bash
# Install the ticket bot on this Mac as a background service (launchd).
# Usage, from the repo folder:  bash tools/macos/install.sh
set -euo pipefail
cd "$(dirname "$0")/../.."
REPO="$PWD"
LABEL="com.ticket-monitor.bot"
PLIST="$HOME/Library/LaunchAgents/$LABEL.plist"
LOG="$HOME/Library/Logs/ticket-monitor.log"

case "$REPO" in
  "$HOME/Documents"*|"$HOME/Desktop"*|"$HOME/Downloads"*)
    echo "❌ Move the folder out of Documents/Desktop/Downloads (macOS blocks"
    echo "   background services there), e.g.:  mv \"$REPO\" ~/ticket-monitor-bot"
    exit 1;;
esac

echo "1/5 Python..."
PY=""
for c in python3.13 python3.12 python3.11 python3.10 /opt/homebrew/bin/python3 /usr/local/bin/python3 python3; do
  if command -v "$c" >/dev/null 2>&1 &&
     "$c" -c 'import sys; sys.exit(0 if sys.version_info >= (3, 10) else 1)' 2>/dev/null; then
    PY="$(command -v "$c")"; break
  fi
done
if [ -z "$PY" ]; then
  echo "❌ Python 3.10+ is needed. Install it from https://www.python.org/downloads/macos/"
  echo "   (the macOS 64-bit universal2 installer), then run this script again."
  exit 1
fi
echo "    $("$PY" --version) at $PY"

echo "2/5 Libraries..."
"$PY" -m venv .venv
.venv/bin/pip install -q --upgrade pip
.venv/bin/pip install -q -r requirements.txt

echo "3/5 Settings and state..."
find_file() {  # $1 = name; Telegram saves to Downloads or Downloads/Telegram Desktop
  for d in "$HOME/Downloads" "$HOME/Downloads/Telegram Desktop"; do
    [ -f "$d/$1" ] && { echo "$d/$1"; return; }
  done
}
if [ ! -f .env ]; then
  src="$(find_file bot.env || true)"
  if [ -n "$src" ]; then
    cp "$src" .env && echo "    settings taken from $src"
  else
    read -r -s -p "    Telegram bot token: " TOKEN; echo
    read -r -p "    Your Telegram chat id: " CHAT
    printf 'TELEGRAM_BOT_TOKEN=%s\nTELEGRAM_CHAT_ID=%s\n' "$TOKEN" "$CHAT" > .env
  fi
fi
chmod 600 .env
if [ ! -f state.json ]; then
  src="$(find_file state.json || true)"
  if [ -n "$src" ]; then
    cp "$src" state.json && echo "    state taken from $src (subscribers, settings...)"
  else
    echo "    no state.json found - starting fresh"
  fi
fi

echo "4/5 Telegram test message..."
if ! ( set -a; . ./.env; set +a; .venv/bin/python monitor.py --mode test ); then
  echo "❌ Telegram did not accept the settings: check the token and chat id in"
  echo "   $REPO/.env (open it with: open -e .env), then run this script again."
  exit 1
fi

echo "5/5 Background service..."
mkdir -p "$HOME/Library/LaunchAgents" "$HOME/Library/Logs"
cat > "$PLIST" <<PLIST
<?xml version="1.0" encoding="UTF-8"?>
<!DOCTYPE plist PUBLIC "-//Apple//DTD PLIST 1.0//EN" "http://www.apple.com/DTDs/PropertyList-1.0.dtd">
<plist version="1.0">
<dict>
  <key>Label</key><string>$LABEL</string>
  <key>ProgramArguments</key>
  <array><string>/bin/bash</string><string>$REPO/tools/macos/run.sh</string></array>
  <key>RunAtLoad</key><true/>
  <key>KeepAlive</key><true/>
  <key>ThrottleInterval</key><integer>30</integer>
  <key>StandardOutPath</key><string>$LOG</string>
  <key>StandardErrorPath</key><string>$LOG</string>
</dict>
</plist>
PLIST
launchctl bootout "gui/$(id -u)/$LABEL" 2>/dev/null || true
launchctl bootstrap "gui/$(id -u)" "$PLIST"
sleep 3
if launchctl print "gui/$(id -u)/$LABEL" >/dev/null 2>&1; then
  echo "✅ The bot is running on this Mac and starts again after a restart."
  echo "   Log:    tail -f \"$LOG\""
  echo "   Update: bash tools/macos/update.sh     Remove: bash tools/macos/uninstall.sh"
else
  echo "❌ The service did not start - see $LOG"; exit 1
fi
