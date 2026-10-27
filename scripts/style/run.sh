#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/../.."
export LEAN_NUM_THREADS=4
export PROPERTYF_AUDIT_CORES=28-31
taskset -c 28-31 lake build PropertyF > scripts/style/.build.log 2>&1
python3 scripts/style/build_warnings.py
scripts/audit-target.sh > scripts/style/.audit.log 2>&1
if ! rg -Fq "Final theorem axiom dependencies: [propext, Classical.choice, Quot.sound]" scripts/style/.audit.log; then
  echo "The audit did not report the required exact axiom list; see scripts/style/.audit.log" >&2
  exit 1
fi
python3 scripts/style/envlint.py
taskset -c 28-31 lake env lean scripts/style/ExistingMathlib.lean
taskset -c 28-31 python3 scripts/style/survey.py
