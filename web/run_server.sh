#!/bin/bash
set -e

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
REPO_DIR="$(dirname "$SCRIPT_DIR")"
PORT="${1:-5001}"

echo "=== DIG Web Server ==="
echo "Repo:   $REPO_DIR"
echo "Port:   $PORT"

if [ -d "$REPO_DIR/venv" ]; then
    source "$REPO_DIR/venv/bin/activate"
elif [ -d "$HOME/dig_env" ]; then
    source "$HOME/dig_env/bin/activate"
fi

pip install -q -r "$SCRIPT_DIR/requirements.txt" 2>/dev/null || true

export DIG_ROOT="$REPO_DIR"
export PORT="$PORT"

echo "Starting DIG server on port $PORT..."
cd "$SCRIPT_DIR"
exec gunicorn --bind "0.0.0.0:$PORT" --timeout 600 --workers 2 --threads 4 server:app
