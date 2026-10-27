#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
export LEAN_NUM_THREADS=4
exec taskset -c "${PROPERTYF_AUDIT_CORES:-0-3}" lake build PropertyF.Ground.Integrate.TargetAudit
