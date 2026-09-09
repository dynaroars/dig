#!/usr/bin/env bash
# Upgrade an existing Prime installation to use DIG's explicit host-visible
# job directory, while retaining systemd's PrivateTmp isolation.
# Run with: sudo ./web/fix-prime-jobs.sh

set -Eeuo pipefail

readonly APP_USER="webapp"
readonly APP_DIR="/opt/dig/current"
readonly JOBS_DIR="/var/lib/dig"
readonly UNIT_NAME="dig-backend.service"
readonly DROPIN_DIR="/etc/systemd/system/${UNIT_NAME}.d"
readonly DROPIN_FILE="${DROPIN_DIR}/10-docker-visible-tmp.conf"

fail() {
  echo "ERROR: $*" >&2
  exit 1
}

if [[ ${EUID} -ne 0 ]]; then
  fail "Run this repair with sudo."
fi

SCRIPT_DIR="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
SOURCE_RUNNER="${SCRIPT_DIR}/docker_runner.py"

id "${APP_USER}" >/dev/null 2>&1 || fail "User ${APP_USER} does not exist."
systemctl cat "${UNIT_NAME}" >/dev/null 2>&1 \
  || fail "${UNIT_NAME} is not installed."
[[ -f "${SOURCE_RUNNER}" ]] || fail "Could not find ${SOURCE_RUNNER}."
[[ -d "${APP_DIR}/web" ]] || fail "Could not find the installed DIG web directory."

echo "[1/5] Installing the updated DIG web runner..."
install -o "${APP_USER}" -g "${APP_USER}" -m 0644 \
  "${SOURCE_RUNNER}" "${APP_DIR}/web/docker_runner.py"

echo "[2/5] Installing the systemd job-directory configuration..."
install -d -o root -g root -m 0755 "${DROPIN_DIR}"
tee "${DROPIN_FILE}" >/dev/null <<'UNIT'
[Service]
Environment=DIG_JOB_DIR=/var/lib/dig
StateDirectory=dig
StateDirectoryMode=0700
UNIT
chmod 0644 "${DROPIN_FILE}"

echo "[3/5] Restarting the DIG backend..."
systemctl daemon-reload
systemctl restart "${UNIT_NAME}"

for attempt in {1..20}; do
  if curl --fail --silent http://127.0.0.1:5001/api/health >/dev/null; then
    break
  fi
  if [[ ${attempt} -eq 20 ]]; then
    journalctl -u "${UNIT_NAME}" -n 100 --no-pager >&2
    fail "DIG did not pass its local health check after restart."
  fi
  sleep 1
done

echo "[4/5] Confirming Docker can see submitted job files..."
MOUNT_TEST="${JOBS_DIR}/.docker-mount-test-$$"
trap 'rm -f -- "${MOUNT_TEST}"' EXIT
printf '%s\n' 'DIG Docker mount test' > "${MOUNT_TEST}"
chown "${APP_USER}:${APP_USER}" "${MOUNT_TEST}"

docker run --rm --network none \
  -v "${MOUNT_TEST}:/dig-mount-test:ro" \
  dig-sandbox:latest \
  test -f /dig-mount-test

echo "[5/5] Confirming the service received DIG_JOB_DIR..."
systemctl show "${UNIT_NAME}" --property=Environment --value \
  | grep -q 'DIG_JOB_DIR=/var/lib/dig' \
  || fail "The DIG_JOB_DIR environment setting was not applied."

echo
echo "Repair completed successfully."
echo "DIG health check: OK"
echo "Docker job-file mount: OK"
echo "DIG job directory: ${JOBS_DIR}"
echo "Reload https://dig.roars.dev and click Run DIG again."
