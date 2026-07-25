#!/bin/bash
# Invoked as a forced SSH command (see authorized_keys on the deploy host) by
# the "Deploy backend to taco" GitHub Actions workflow. Pulls the latest dev
# branch and restarts the dig-backend systemd service, which is permitted
# passwordlessly for the deploying user via a scoped sudoers NOPASSWD rule
# (sudo -l shows exactly which commands are allowed).
#
# Named deploy-backend.sh (not deploy.sh) to avoid colliding with the
# existing web/deploy.sh, which publishes frontend-classic to gh-pages.
set -e
cd "$(dirname "$0")/.."
git pull origin dev
sudo systemctl restart dig-backend
echo "[deploy] dig-backend restarted at $(date)"
