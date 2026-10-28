#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
python3 scripts/check-audit-imports.py
export LEAN_NUM_THREADS=4
export PROPERTYF_AUDIT_CORES="${PROPERTYF_AUDIT_CORES:-0-3}"
taskset -c "$PROPERTYF_AUDIT_CORES" lake build
python3 scripts/audit_new_libraries.py
python3 scripts/conjecture_status.py --check
