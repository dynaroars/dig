#!/usr/bin/env bash
# Periodic health check for dig.roars.dev (run by dig-healthcheck.timer).
# Alerts via web/notify.sh after 2 consecutive failures, then at most every
# ALERT_REPEAT_HOURS while the site stays down.

set -uo pipefail

ROOT="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
STATE_DIR="${HOME}/.local/state/dig-web"
STATE="${STATE_DIR}/health.state"
ALERT_REPEAT_HOURS="${ALERT_REPEAT_HOURS:-6}"
mkdir -p "${STATE_DIR}"

problems=()
for unit in dig-web.service dig-cloudflared.service; do
  st="$(systemctl --user is-active "${unit}" 2>/dev/null)"
  [[ "${st}" == active ]] || problems+=("${unit} is ${st:-unknown}")
done
code="$(curl -s -o /dev/null -m 15 -w '%{http_code}' http://127.0.0.1:5001/api/health)"
[[ "${code}" == 200 ]] || problems+=("local /api/health returned HTTP ${code}")
restarts="$(systemctl --user show dig-web.service -p NRestarts --value 2>/dev/null)"

fails=0 last_alert=0
[[ -f "${STATE}" ]] && source "${STATE}"
now="$(date +%s)"

if ((${#problems[@]} == 0)); then
  ((fails > 0)) && echo "recovered after ${fails} failed checks"
  printf 'fails=0\nlast_alert=0\n' > "${STATE}"
  exit 0
fi

fails=$((fails + 1))
reason="$(IFS='; '; echo "${problems[*]}"); dig-web restarts=${restarts:-?}"
echo "check failed (${fails}): ${reason}"
if ((fails >= 2 && now - last_alert >= ALERT_REPEAT_HOURS * 3600)); then
  "${ROOT}/web/notify.sh" "dig.roars.dev is DOWN" "${reason}" && last_alert="${now}"
fi
printf 'fails=%d\nlast_alert=%d\n' "${fails}" "${last_alert}" > "${STATE}"
exit 1
