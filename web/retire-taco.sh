#!/usr/bin/env bash
# Retire DIG from Taco after migration to Prime.
#
# Reversible retirement (run now):
#   sudo ./web/retire-taco.sh
#
# Final archive of service definitions/configuration (run after the rollback
# period):
#   sudo ./web/retire-taco.sh --finalize
# If Taco has multiple retired forced deployment keys:
#   sudo ./web/retire-taco.sh --finalize --all-deploy-keys

set -Eeuo pipefail

readonly APP_USER="webapp"
readonly APP_DIR="/home/webapp/dig"
readonly AUTHORIZED_KEYS="/home/webapp/.ssh/authorized_keys"
readonly NGROK_CONFIG="/home/webapp/ngrok-dig.yml"
readonly BACKUP_ROOT="/var/backups/dig-taco-retired"
readonly PRIME_HEALTH_URL="https://dig.roars.dev/api/health"
readonly -a DIG_UNITS=("dig-ngrok-tunnel.service" "dig-backend.service")

FINALIZE=false
REMOVE_ALL_DEPLOY_KEYS=false
for argument in "$@"; do
  case "${argument}" in
    --finalize) FINALIZE=true ;;
    --all-deploy-keys) REMOVE_ALL_DEPLOY_KEYS=true ;;
    *)
      echo "Usage: sudo $0 [--finalize] [--all-deploy-keys]" >&2
      exit 2
      ;;
  esac
done

fail() {
  echo "ERROR: $*" >&2
  exit 1
}

if [[ ${EUID} -ne 0 ]]; then
  fail "Run this script as root with sudo."
fi

TACO_HOSTNAME="$(hostname -s)"
[[ "${TACO_HOSTNAME,,}" == "taco" ]] \
  || fail "This script only runs on Taco; hostname is ${TACO_HOSTNAME}."

echo "[1/6] Verifying that Prime is serving DIG..."
curl --fail --silent --show-error "${PRIME_HEALTH_URL}" >/dev/null \
  || fail "Prime's public DIG health check failed; Taco was not changed."

echo "[2/6] Resolving Taco resources and deployment key..."
declare -A UNIT_PATHS=()
for unit in "${DIG_UNITS[@]}"; do
  if systemctl cat "${unit}" >/dev/null 2>&1; then
    unit_path="$(systemctl show "${unit}" --property=FragmentPath --value)"
    [[ -n "${unit_path}" && -f "${unit_path}" ]] \
      || fail "Could not resolve the unit file for ${unit}."
    UNIT_PATHS["${unit}"]="${unit_path}"
  else
    echo "  ${unit}: already absent"
  fi
done

KEY_MATCH_COUNT=0
if [[ -f "${AUTHORIZED_KEYS}" ]]; then
  KEY_MATCH_COUNT="$(grep -Ec 'command="[^"]*deploy[^"]*"' "${AUTHORIZED_KEYS}" || true)"
  if [[ "${KEY_MATCH_COUNT}" -gt 1 && "${REMOVE_ALL_DEPLOY_KEYS}" == false ]]; then
    echo "Matching forced-command entries (public key bodies redacted):" >&2
    grep -nE 'command="[^"]*deploy[^"]*"' "${AUTHORIZED_KEYS}" \
      | sed -E 's/(ssh-(rsa|ed25519)|ecdsa-[^ ]+) [A-Za-z0-9+\/=]+/\1 <public-key-redacted>/' \
      >&2
    fail "Found ${KEY_MATCH_COUNT} forced deploy keys. Re-run with --all-deploy-keys only if all belong to this retired deployment."
  fi
fi

RETIREMENT_ID="$(date -u +%Y%m%dT%H%M%SZ)"
BACKUP_DIR="${BACKUP_ROOT}/${RETIREMENT_ID}"
install -d -o root -g root -m 0700 "${BACKUP_DIR}"

for unit in "${!UNIT_PATHS[@]}"; do
  cp -a "${UNIT_PATHS[${unit}]}" "${BACKUP_DIR}/${unit}.backup"
done
if [[ -f "${AUTHORIZED_KEYS}" ]]; then
  cp -a "${AUTHORIZED_KEYS}" "${BACKUP_DIR}/authorized_keys.backup"
fi
if [[ -f "${NGROK_CONFIG}" ]]; then
  cp -a "${NGROK_CONFIG}" "${BACKUP_DIR}/ngrok-dig.yml.backup"
fi

echo "[3/6] Stopping and disabling Taco's DIG services..."
for unit in "${DIG_UNITS[@]}"; do
  if [[ -n "${UNIT_PATHS[${unit}]:-}" ]]; then
    systemctl disable --now "${unit}"
  fi
done

echo "[4/6] Revoking the forced DIG deployment key..."
if [[ "${KEY_MATCH_COUNT}" -eq 1 || ( "${KEY_MATCH_COUNT}" -gt 1 && "${REMOVE_ALL_DEPLOY_KEYS}" == true ) ]]; then
  KEYS_TMP="$(mktemp)"
  trap 'rm -f -- "${KEYS_TMP:-}"' EXIT
  awk '!/command="[^"]*deploy[^"]*"/' "${AUTHORIZED_KEYS}" > "${KEYS_TMP}"
  install -o "${APP_USER}" -g "${APP_USER}" -m 0600 \
    "${KEYS_TMP}" "${AUTHORIZED_KEYS}"
  echo "  Removed ${KEY_MATCH_COUNT} forced deployment key(s); backup saved."
else
  echo "  No forced deployment key containing 'deploy' was found."
fi

echo "[5/6] Checking retirement state..."
for unit in "${DIG_UNITS[@]}"; do
  if systemctl is-active --quiet "${unit}" 2>/dev/null; then
    fail "${unit} is still active."
  fi
done

if [[ "${FINALIZE}" == true ]]; then
  echo "  Finalizing: archiving unit definitions and ngrok configuration..."
  for unit in "${!UNIT_PATHS[@]}"; do
    expected_path="/etc/systemd/system/${unit}"
    [[ "${UNIT_PATHS[${unit}]}" == "${expected_path}" ]] \
      || fail "Refusing to move unexpected unit path: ${UNIT_PATHS[${unit}]}"
    mv "${expected_path}" "${BACKUP_DIR}/${unit}.retired"
  done
  if [[ -f "${NGROK_CONFIG}" ]]; then
    mv "${NGROK_CONFIG}" "${BACKUP_DIR}/ngrok-dig.yml.retired"
  fi
  systemctl daemon-reload
fi

echo "[6/6] Verifying Prime again..."
curl --fail --silent --show-error "${PRIME_HEALTH_URL}" >/dev/null \
  || fail "Prime stopped responding after Taco retirement."

echo
echo "Taco DIG retirement completed successfully."
echo "Backup directory: ${BACKUP_DIR}"
echo "Application checkout retained for rollback: ${APP_DIR}"
if [[ "${FINALIZE}" == false ]]; then
  echo "After the rollback period, optionally run:"
  echo "  sudo $0 --finalize"
fi
echo
echo "The ngrok dashboard endpoint must still be deleted separately if desired."
