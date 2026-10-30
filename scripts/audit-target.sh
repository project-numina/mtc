#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
python3 scripts/check-audit-imports.py
python3 scripts/check_statement_equivalence.py
export LEAN_NUM_THREADS="${LEAN_NUM_THREADS:-4}"
exec taskset -c "${PROPERTYF_AUDIT_CORES:-0-3}" lake build MTC.PropertyF.Audit.TargetAudit
