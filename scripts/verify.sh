#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
lake --version
lake env lean --version
lake build
lake env lean -DwarningAsError=true Examples.lean
audit_output="$(mktemp)"
trap 'rm -f "$audit_output"' EXIT
lake env lean -DwarningAsError=true Audit.lean | tee "$audit_output"
python3 scripts/check_axioms.py "$audit_output"
