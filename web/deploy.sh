#!/usr/bin/env bash
# Serve this DIG checkout at https://dig.roars.dev as the current user.
# Re-run after pulling changes to rebuild the sandbox and restart.
#   ./web/deploy.sh
#
# Runs two systemd *user* services (no root, no extra accounts):
#   dig-web.service        gunicorn on 127.0.0.1:5001, jobs run in dig-sandbox
#   dig-cloudflared.service Cloudflare Tunnel "dig-prime"
#                           (route dig.roars.dev -> http://127.0.0.1:5001)
# Secrets live in ~/.config/dig-web/env (mode 600):
#   TUNNEL_TOKEN=...        connector token of the dig-prime tunnel
#   ANTHROPIC_API_KEY=...   optional

set -Eeuo pipefail

ROOT="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
CONF_DIR="${HOME}/.config/dig-web"
ENV_FILE="${CONF_DIR}/env"
JOB_DIR="${HOME}/.local/state/dig-web/jobs"
UNIT_DIR="${HOME}/.config/systemd/user"
CLOUDFLARED="${HOME}/.local/bin/cloudflared"
PY="${ROOT}/.venv/bin/python"

fail() { echo "ERROR: $*" >&2; exit 1; }

command -v docker >/dev/null || fail "docker is not installed."
docker info >/dev/null 2>&1 || fail "cannot talk to docker (is ${USER} in the docker group?)"

echo "[1/5] Python environment (${ROOT}/.venv)"
[[ -x "${PY}" ]] || python3 -m venv "${ROOT}/.venv"
"${PY}" -m pip install -q -r "${ROOT}/web/requirements.txt"

echo "[2/5] Building dig-sandbox image"
docker build -q -f "${ROOT}/web/Dockerfile.sandbox" -t dig-sandbox:latest "${ROOT}"

echo "[3/5] cloudflared"
if [[ ! -x "${CLOUDFLARED}" ]]; then
  mkdir -p "$(dirname "${CLOUDFLARED}")"
  curl -fsSL -o "${CLOUDFLARED}" \
    https://github.com/cloudflare/cloudflared/releases/latest/download/cloudflared-linux-amd64
  chmod +x "${CLOUDFLARED}"
fi

mkdir -p "${CONF_DIR}" "${JOB_DIR}"
touch "${ENV_FILE}"
chmod 600 "${ENV_FILE}"
if ! grep -q '^TUNNEL_TOKEN=.' "${ENV_FILE}"; then
  read -r -s -p "Cloudflare dig-prime tunnel token: " token; echo
  [[ -n "${token}" ]] || fail "A tunnel token is required."
  printf 'TUNNEL_TOKEN=%s\n' "${token}" >> "${ENV_FILE}"
  unset token
fi

echo "[4/5] systemd user services"
mkdir -p "${UNIT_DIR}"
cat > "${UNIT_DIR}/dig-web.service" <<UNIT
[Unit]
Description=DIG web backend (${ROOT})

[Service]
WorkingDirectory=${ROOT}/web
EnvironmentFile=${ENV_FILE}
Environment=PORT=5001
Environment=DIG_ROOT=${ROOT}
Environment=USE_DOCKER=true
Environment=DIG_DOCKER_IMAGE=dig-sandbox:latest
Environment=DIG_JOB_DIR=${JOB_DIR}
ExecStart=${PY} -m gunicorn --bind 127.0.0.1:5001 --timeout 600 --workers 1 --threads 8 server:app
Restart=always
RestartSec=5

[Install]
WantedBy=default.target
UNIT

cat > "${UNIT_DIR}/dig-cloudflared.service" <<UNIT
[Unit]
Description=Cloudflare Tunnel for dig.roars.dev
After=dig-web.service

[Service]
EnvironmentFile=${ENV_FILE}
ExecStart=${CLOUDFLARED} --no-autoupdate tunnel run
Restart=always
RestartSec=5

[Install]
WantedBy=default.target
UNIT

systemctl --user daemon-reload
systemctl --user enable dig-web.service dig-cloudflared.service >/dev/null
systemctl --user restart dig-web.service dig-cloudflared.service

# Keep user services running after logout and across reboots.
if [[ "$(loginctl show-user "${USER}" -p Linger --value 2>/dev/null)" != yes ]]; then
  loginctl enable-linger "${USER}" 2>/dev/null \
    || echo "NOTE: run 'sudo loginctl enable-linger ${USER}' so the site survives logout/reboot."
fi

echo "[5/5] Health check"
for _ in {1..20}; do
  curl -fsS http://127.0.0.1:5001/api/health >/dev/null 2>&1 && break
  sleep 1
done
curl -fsS http://127.0.0.1:5001/api/health >/dev/null \
  || { journalctl --user -u dig-web -n 50 --no-pager >&2; fail "backend health check failed"; }
systemctl --user is-active --quiet dig-cloudflared.service \
  || { journalctl --user -u dig-cloudflared -n 50 --no-pager >&2; fail "cloudflared is not running"; }

echo
echo "OK: https://dig.roars.dev  (local: http://127.0.0.1:5001)"
echo "Logs: journalctl --user -u dig-web -f   |   journalctl --user -u dig-cloudflared -f"
