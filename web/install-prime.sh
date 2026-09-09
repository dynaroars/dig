#!/usr/bin/env bash
# Install the current DIG checkout on Prime and expose it through a remotely
# managed Cloudflare Tunnel. Run from this repository with:
#   sudo ./web/install-prime.sh
#
# Before running, create a Cloudflare Tunnel named "dig-prime", add the public
# hostname dig.roars.dev -> http://127.0.0.1:5001, and have its connector token
# ready. The script prompts for secrets without echoing them.

set -Eeuo pipefail

readonly APP_USER="webapp"
readonly APP_ROOT="/opt/dig"
readonly RELEASES_DIR="${APP_ROOT}/releases"
readonly CURRENT_LINK="${APP_ROOT}/current"
readonly ENV_DIR="/etc/dig"
readonly ENV_FILE="${ENV_DIR}/dig.env"
readonly BACKEND_UNIT="/etc/systemd/system/dig-backend.service"
readonly PUBLIC_URL="https://dig.roars.dev"

fail() {
  echo "ERROR: $*" >&2
  exit 1
}

if [[ ${EUID} -ne 0 ]]; then
  fail "Run this installer with sudo."
fi

SCRIPT_DIR="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
SOURCE_DIR="$(cd -- "${SCRIPT_DIR}/.." && pwd)"
[[ -f "${SOURCE_DIR}/web/server.py" ]] || fail "Could not locate the DIG repository."

case "$(uname -m)" in
  x86_64|amd64) ;;
  *) fail "web/Dockerfile.sandbox currently requires an x86-64 Prime host." ;;
esac

export DEBIAN_FRONTEND=noninteractive

echo "[1/9] Installing system packages..."
apt-get update
apt-get install -y ca-certificates curl git python3 python3-pip python3-venv rsync
if ! command -v docker >/dev/null 2>&1; then
  apt-get install -y docker.io
fi
systemctl enable --now docker

if ! id "${APP_USER}" >/dev/null 2>&1; then
  useradd --create-home --shell /bin/bash "${APP_USER}"
fi
usermod -aG docker "${APP_USER}"

echo "[2/9] Installing cloudflared..."
if ! command -v cloudflared >/dev/null 2>&1; then
  install -d -m 0755 /usr/share/keyrings
  curl -fsSL https://pkg.cloudflare.com/cloudflare-main.gpg \
    -o /usr/share/keyrings/cloudflare-main.gpg
  printf '%s\n' \
    'deb [signed-by=/usr/share/keyrings/cloudflare-main.gpg] https://pkg.cloudflare.com/cloudflared any main' \
    > /etc/apt/sources.list.d/cloudflared.list
  apt-get update
  apt-get install -y cloudflared
fi

echo "[3/9] Creating an immutable application release..."
install -d -o "${APP_USER}" -g "${APP_USER}" -m 0755 "${RELEASES_DIR}"
RELEASE_ID="$(date -u +%Y%m%dT%H%M%SZ)"
RELEASE_DIR="${RELEASES_DIR}/${RELEASE_ID}"
[[ ! -e "${RELEASE_DIR}" ]] || fail "Release path already exists: ${RELEASE_DIR}"
install -d -o "${APP_USER}" -g "${APP_USER}" -m 0755 "${RELEASE_DIR}"

rsync -a \
  --exclude='.git/' \
  --exclude='.venv/' \
  --exclude='venv/' \
  --exclude='__pycache__/' \
  --exclude='*.pyc' \
  "${SOURCE_DIR}/" "${RELEASE_DIR}/"
chown -R "${APP_USER}:${APP_USER}" "${RELEASE_DIR}"

echo "[4/9] Creating the Python environment..."
runuser -u "${APP_USER}" -- python3 -m venv "${RELEASE_DIR}/venv"
runuser -u "${APP_USER}" -- "${RELEASE_DIR}/venv/bin/pip" install --upgrade pip
runuser -u "${APP_USER}" -- "${RELEASE_DIR}/venv/bin/pip" install \
  -r "${RELEASE_DIR}/web/requirements.txt"

echo "[5/9] Building the DIG sandbox image..."
docker build \
  -f "${RELEASE_DIR}/web/Dockerfile.sandbox" \
  -t dig-sandbox:latest \
  "${RELEASE_DIR}"

echo "[6/9] Configuring application secrets..."
install -d -o root -g "${APP_USER}" -m 0750 "${ENV_DIR}"
if [[ ! -f "${ENV_FILE}" ]]; then
  read -r -s -p "Anthropic API key (press Enter to leave unset): " ANTHROPIC_KEY
  echo
  if [[ -n "${ANTHROPIC_KEY}" ]]; then
    printf 'ANTHROPIC_API_KEY=%s\n' "${ANTHROPIC_KEY}" > "${ENV_FILE}"
  else
    : > "${ENV_FILE}"
  fi
  unset ANTHROPIC_KEY
fi
chown root:"${APP_USER}" "${ENV_FILE}"
chmod 0640 "${ENV_FILE}"

if [[ -e "${CURRENT_LINK}" && ! -L "${CURRENT_LINK}" ]]; then
  fail "${CURRENT_LINK} exists but is not a symlink; refusing to replace it."
fi
ln -sfn "${RELEASE_DIR}" "${CURRENT_LINK}"

echo "[7/9] Installing the backend service..."
install -m 0644 /dev/null "${BACKEND_UNIT}"
tee "${BACKEND_UNIT}" >/dev/null <<'UNIT'
[Unit]
Description=DIG Web Backend on Prime
After=network-online.target docker.service
Wants=network-online.target
Requires=docker.service

[Service]
Type=simple
User=webapp
Group=webapp
SupplementaryGroups=docker
WorkingDirectory=/opt/dig/current/web
EnvironmentFile=-/etc/dig/dig.env
Environment=PORT=5001
Environment=DIG_ROOT=/opt/dig/current
Environment=USE_DOCKER=true
Environment=DIG_DOCKER_IMAGE=dig-sandbox:latest
Environment=DIG_JOB_DIR=/var/lib/dig
ExecStart=/opt/dig/current/venv/bin/gunicorn --bind 127.0.0.1:5001 --timeout 600 --workers 1 --threads 8 server:app
Restart=always
RestartSec=5
PrivateTmp=true
StateDirectory=dig
StateDirectoryMode=0700

[Install]
WantedBy=multi-user.target
UNIT

systemctl daemon-reload
systemctl enable --now dig-backend.service

echo "[8/9] Configuring the Cloudflare Tunnel connector..."
if systemctl is-active --quiet cloudflared.service 2>/dev/null; then
  echo "cloudflared is already active; keeping its existing tunnel configuration."
elif systemctl cat cloudflared.service >/dev/null 2>&1; then
  systemctl enable --now cloudflared.service
else
  read -r -s -p "Paste the Cloudflare dig-prime tunnel token: " TUNNEL_TOKEN
  echo
  [[ -n "${TUNNEL_TOKEN}" ]] || fail "A Cloudflare Tunnel token is required."
  cloudflared service install "${TUNNEL_TOKEN}"
  unset TUNNEL_TOKEN
  systemctl enable --now cloudflared.service
fi

echo "[9/9] Running health checks..."
for attempt in {1..20}; do
  if curl --fail --silent http://127.0.0.1:5001/api/health >/dev/null; then
    break
  fi
  if [[ ${attempt} -eq 20 ]]; then
    journalctl -u dig-backend.service -n 100 --no-pager >&2
    fail "The local DIG health check did not pass."
  fi
  sleep 1
done

systemctl is-active --quiet cloudflared.service \
  || fail "cloudflared is not running."

echo
echo "Prime installation completed."
echo "Local health check: OK"
echo "Release: ${RELEASE_DIR}"
echo "Public URL: ${PUBLIC_URL}"
echo
echo "If the public URL is not live yet, confirm in Cloudflare that the dig-prime"
echo "tunnel has this Published application route:"
echo "  dig.roars.dev -> http://127.0.0.1:5001"
echo
echo "Useful logs:"
echo "  sudo journalctl -u dig-backend -f"
echo "  sudo journalctl -u cloudflared -f"
