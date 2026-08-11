#!/usr/bin/env bash
# setup.sh — creates a Python virtual environment with everything the harness needs.
#
# This script is safe to re-run. It reuses an existing venv instead of
# recreating it. Also, the pip install is idempotent.
#
# What this script installs, and why:
#   qiskit              circuit representation, OpenQASM I/O, and transpilation
#   qiskit-aer          local noise-model simulation (harness/sim/)
#   qiskit-ibm-runtime  IBM backend access, and the offline "fake backend" topology
#                       and calibration snapshots used by harness/devices/ (this
#                       path needs no account and no token)
#   mqt.qcec            only for harness/eval-scripts/run_qcec.py (the capability
#                       comparison table against an external equivalence checker).
#                       This dependency is heavier than the others. If you want
#                       only the core reproduction path, skip it.
set -euo pipefail

HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
VENV="$HERE/.venv"

if [ ! -d "$VENV" ]; then
  echo "creating venv at $VENV"
  python3 -m venv "$VENV"
else
  echo "reusing existing venv at $VENV"
fi

# shellcheck disable=SC1091
source "$VENV/bin/activate"

pip install --upgrade pip >/dev/null
echo "installing qiskit, qiskit-aer, qiskit-ibm-runtime, mqt.qcec ..."
pip install qiskit qiskit-aer qiskit-ibm-runtime "mqt.qcec"

echo
echo "=== setup complete ==="
echo "Activate the venv in new shells with:"
echo "    source $VENV/bin/activate"
echo
echo "Next step: run every check with"
echo "    bash run_artifact.sh"
echo "See README.md for what each stage does."
