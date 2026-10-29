#!/bin/bash
# Started by launchd (see install.sh): runs the bot on this Mac.
cd "$(dirname "$0")/../.." || exit 1
set -a; . ./.env; set +a
export LOCAL_RUN=1 REPORT_MODE=changes ACCESS_MODE=open STATE_FILE="$PWD/state.json"
# caffeinate -i: keep the Mac from idle-sleeping while the bot runs.
exec /usr/bin/caffeinate -i .venv/bin/python monitor.py --mode normal --loop-minutes 1440
