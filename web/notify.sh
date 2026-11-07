#!/usr/bin/env bash
# Report a dig.roars.dev problem to GitHub so it emails the maintainer.
#   ./web/notify.sh "<title>" "<one-line reason>"
#
# Sends a repository_dispatch event (type prime-alert) using the gh CLI login of
# the current user. .github/workflows/prime-alert.yml then fails on purpose, and
# GitHub notifies the user who triggered the run ("Run failed" email).
# The repository is public: keep the reason short and free of secrets/logs.

set -uo pipefail

REPO="${DIG_ALERT_REPO:-dynaroars/dig}"
title="${1:-dig.roars.dev alert}"
reason="${2:-}"
host="$(hostname -s 2>/dev/null || echo unknown)"
when="$(date -Is)"

payload="$(TITLE="${title}" REASON="${reason}" HOST="${host}" WHEN="${when}" python3 -c '
import json, os
print(json.dumps({"event_type": "prime-alert", "client_payload": {
    "title": os.environ["TITLE"][:200], "reason": os.environ["REASON"][:500],
    "host": os.environ["HOST"], "time": os.environ["WHEN"]}}))')"

if printf '%s' "${payload}" | gh api -X POST "repos/${REPO}/dispatches" --input - >/dev/null; then
  echo "alert sent to GitHub (${REPO}): ${title}"
else
  echo "ERROR: failed to send alert to GitHub: ${title} -- ${reason}" >&2
  command -v notify-send >/dev/null && notify-send -u critical "${title}" "${reason}" 2>/dev/null
  exit 1
fi
