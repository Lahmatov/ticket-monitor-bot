#!/bin/bash
# Stop the bot on this Mac and remove the background service.
LABEL="com.ticket-monitor.bot"
launchctl bootout "gui/$(id -u)/$LABEL" 2>/dev/null || true
rm -f "$HOME/Library/LaunchAgents/$LABEL.plist"
echo "Stopped. (The folder, .env and state.json are kept.)"
