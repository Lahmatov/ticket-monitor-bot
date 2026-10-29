#!/bin/bash
# Get the latest bot code and restart the service.
set -euo pipefail
cd "$(dirname "$0")/../.."
git pull --ff-only
.venv/bin/pip install -q -r requirements.txt
launchctl kickstart -k "gui/$(id -u)/com.ticket-monitor.bot"
echo "✅ Updated and restarted."
