#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
if [[ -n "${LEAN_BIN:-}" ]]; then
  export PATH="$LEAN_BIN:$PATH"
fi
exec python3 check.py
