#!/usr/bin/env bash
# run_artifact.sh — one entry point that reproduces the results of this artifact.
#
# The script has four tiers. Each tier says what it needs:
#
#   A. core        Lean build, kernel checks, device corpus, sample circuits,
#                  timing, offline simulator suite, hardware reconciliation.
#                  Needs: elan/lake + Python. Costs no money and no QPU time.
#                  Runs always.
#
#   B. benchmarks  Axis-2 sweep over real QASMBench circuits, front-end fuzzing,
#                  buffered-policy sweeps, external equivalence-checker context.
#                  Needs: the QASMBench suite, which this artifact does not ship.
#                  Runs when QASMBench is present, or with --fetch-benchmarks.
#
#   C. hardware    Recovery of the raw IBM job records for the published
#                  hardware campaign. Read-only retrieval, no QPU time.
#                  Needs: apikey.json in this directory.
#                  Runs when apikey.json is present.
#
#   D. live QPU    Submission of new jobs to real IBM devices.
#                  Needs: apikey.json AND the --submit-qpu flag.
#                  Costs about 8 minutes of metered QPU time. Before you use
#                  it, read the warning in the "--submit-qpu" block.
#
# All output goes to artifact-run/. The script does not change the results
# that this repository ships. Tier D is the one exception. It makes a
# backup first.
#
# Usage:
#   bash run_artifact.sh                    # tiers A and C
#   bash run_artifact.sh --fetch-benchmarks # tiers A, B and C
#   bash run_artifact.sh --core-only        # tier A only
#   bash run_artifact.sh --submit-qpu       # tiers A, C and D
#   bash run_artifact.sh --help

set -uo pipefail

HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "$HERE" || exit 1

OUT="$HERE/artifact-run"
LOGS="$OUT/logs"
SUMMARY="$OUT/SUMMARY.md"

FETCH_BENCH=0
CORE_ONLY=0
SUBMIT_QPU=0

while [ $# -gt 0 ]; do
  case "$1" in
    --fetch-benchmarks) FETCH_BENCH=1 ;;
    --core-only)        CORE_ONLY=1 ;;
    --submit-qpu)       SUBMIT_QPU=1 ;;
    -h|--help)
      sed -n '2,35p' "$0" | sed 's/^# \{0,1\}//'
      exit 0 ;;
    *) echo "unknown option: $1 (use --help)"; exit 2 ;;
  esac
  shift
done

mkdir -p "$LOGS"

# ---------------------------------------------------------------- tool paths
export PATH="$HOME/.elan/bin:$PATH"
PY="$HERE/.venv/bin/python"
[ -x "$PY" ] || PY="$(command -v python3)"

PASS=0
FAIL=0
SKIP=0
ROWS=()

# Run a command with artifact-run/ as the working directory. Some eval
# scripts write an output file next to the working directory. This practice
# keeps those files out of the shipped result directories.
in_out() { ( cd "$OUT" && "$@" ); }

say() { printf '\n\033[1m== %s\033[0m\n' "$1"; }

# stage <id> <title> <command...>
# Runs one stage, writes its log, and records the verdict. A failed stage does
# not stop the script. The exit code of the script tells you if every stage
# that ran passed.
stage() {
  local id="$1"; shift
  local title="$1"; shift
  local log="$LOGS/$id.log"
  say "$id — $title"
  local t0 t1 rc
  t0=$(date +%s)
  "$@" > "$log" 2>&1
  rc=$?
  t1=$(date +%s)
  tail -6 "$log"
  if [ $rc -eq 0 ]; then
    printf '\033[32mPASS\033[0m  %s  (%ss, log: %s)\n' "$id" "$((t1-t0))" "${log#$HERE/}"
    PASS=$((PASS+1)); ROWS+=("| $id | $title | PASS | $((t1-t0))s |")
  else
    printf '\033[31mFAIL\033[0m  %s  rc=%s  (%ss, log: %s)\n' "$id" "$rc" "$((t1-t0))" "${log#$HERE/}"
    FAIL=$((FAIL+1)); ROWS+=("| $id | $title | FAIL (rc=$rc) | $((t1-t0))s |")
  fi
  return 0
}

skip() {
  local id="$1" title="$2" why="$3"
  printf '\033[33mSKIP\033[0m  %s — %s\n' "$id" "$why"
  SKIP=$((SKIP+1)); ROWS+=("| $id | $title | SKIP — $why | — |")
}

# ============================================================ tier A: core
say "preflight"
if ! command -v lake >/dev/null; then
  echo "error: lake is not on PATH. Install the Lean toolchain first:"
  echo "  curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh"
  exit 1
fi
echo "lake:   $(command -v lake)"
if [ ! -x "$HERE/.venv/bin/python" ]; then
  echo "no .venv found — creating it with setup.sh"
  bash "$HERE/setup.sh" > "$LOGS/A0-setup.log" 2>&1 || {
    echo "setup.sh failed; read $LOGS/A0-setup.log"; exit 1; }
  PY="$HERE/.venv/bin/python"
fi
echo "python: $PY ($("$PY" --version 2>&1))"

stage A1 "build and kernel-check the Lean library" lake build

cat > "$OUT/axioms.lean" <<'EOF'
import QpuCompiler
#print axioms QpuCompiler.certifySecurity_sound
#print axioms QpuCompiler.compile_hh_confine_correct
#print axioms QpuCompiler.compile_hh_confine_buffered
#print axioms QpuCompiler.EdgeSpec.toCoupling
#print axioms QpuCompiler.checkerSteps_seq
def main : IO Unit := pure ()
EOF
# The soundness theorem of the certifier must rest on `propext` alone. The other
# results can also use the two remaining standard axioms. Any further axiom is a
# failure.
check_axioms() {
  lake env lean --run "$OUT/axioms.lean" | tee "$OUT/axioms.txt"
  local rc=0
  grep -q "'QpuCompiler.certifySecurity_sound' depends on axioms: \[propext\]$" "$OUT/axioms.txt" \
    || { echo "FAIL: certifySecurity_sound does not rest on [propext] alone"; rc=1; }
  grep -q "'QpuCompiler.checkerSteps_seq' does not depend on any axioms" "$OUT/axioms.txt" \
    || { echo "FAIL: checkerSteps_seq gained an axiom"; rc=1; }
  # Nothing anywhere can use an axiom outside the standard three.
  if grep -oE '\[[^]]*\]' "$OUT/axioms.txt" | tr -d '[],' | tr ' ' '\n' \
       | grep -vE '^(propext|Classical.choice|Quot.sound)?$' ; then
    echo "FAIL: an axiom outside the standard three appears above"; rc=1
  fi
  [ $rc -eq 0 ] && echo "axiom base as expected"
  return $rc
}
stage A2 "check the axiom base of the main theorems" check_axioms

# The tree must contain no sorry, no native_decide and no ofReduceBool. Each of
# those three moves a proof out of the kernel. The pattern ignores the names
# when they occur in backticks, because prose refers to them.
check_tactics() {
  if grep -rnE '(^|[^`_[:alnum:]])(sorry|native_decide|ofReduceBool)([^`_[:alnum:]]|$)' \
       QpuCompiler/ harness/*.lean; then
    echo "FORBIDDEN TACTIC FOUND"; return 1
  fi
  echo "clean: no sorry / native_decide / ofReduceBool in QpuCompiler/ or harness/*.lean"
}
stage A3 "check that no proof leaves the kernel" check_tactics

stage A4 "re-verify the 11-device corpus" bash harness/devices/verify_corpus.sh
stage A5 "certify the 4 sample circuits" "$PY" harness/certify_qasm.py --samples
stage A6 "measure the checker cost against gate count" \
  lake env lean --run harness/Timing.lean
stage A7 "run the 9-test offline simulator suite" "$PY" harness/sim/test_e2e.py
stage A8 "design the alias-resolving follow-up measurement" \
  "$PY" harness/sim/tau_discriminator.py
stage A9 "recompute the published hardware cells from raw counts" \
  "$PY" harness/ibm-hardware/reconcile_provenance.py \
      --out "$OUT/reconciliation.json"

# ====================================================== tier B: benchmarks
BENCH="${QASMBENCH_SMALL:-$HERE/harness/QASMBench/small}"
if [ "$CORE_ONLY" -eq 1 ]; then
  skip B "QASMBench axis-2 tier" "--core-only"
elif [ ! -d "$BENCH" ] && [ "$FETCH_BENCH" -eq 1 ]; then
  say "fetching QASMBench (external suite, not shipped with this artifact)"
  git clone --depth 1 https://github.com/pnnl/QASMBench "$HERE/harness/QASMBench" \
    > "$LOGS/B0-clone.log" 2>&1 && BENCH="$HERE/harness/QASMBench/small"
fi

if [ "$CORE_ONLY" -eq 1 ]; then
  :
elif [ ! -d "$BENCH" ]; then
  skip B "QASMBench axis-2 tier" "QASMBench not found (re-run with --fetch-benchmarks)"
else
  echo "QASMBench small suite: $BENCH"
  export QASMBENCH_SMALL="$BENCH"
  export ARTIFACT_ROOT="$HERE"
  export AXIS2_OUT="$OUT/axis2-out"
  export FUZZ_OUT="$OUT/fuzz-out"
  mkdir -p "$AXIS2_OUT" "$FUZZ_OUT"

  # These scripts write some outputs next to the working directory, so run them
  # from artifact-run/. The results this repository ships stay untouched.
  stage B1 "transpile the benchmark suite at optimisation levels 0-3" \
    in_out "$PY" "$HERE/harness/eval-scripts/run_optlevel.py"
  stage B2 "certify every transpiled circuit (axis-2 verdicts)" \
    in_out "$PY" "$HERE/harness/eval-scripts/run_e5b.py"
  stage B3 "generate the 1120-mutant fuzz corpus" \
    in_out "$PY" "$HERE/harness/eval-scripts/fuzz_e3.py"
  stage B4 "fuzz both lexers and count false accepts" \
    in_out "$PY" "$HERE/harness/eval-scripts/fuzz_certify.py"
  stage B5 "sweep the buffered policy over k" \
    "$PY" harness/eval-scripts/run_buffered.py --out "$OUT/buffered_results.json"
  stage B6 "test whether the buffered policy is operable" \
    "$PY" harness/eval-scripts/run_buffered_alloc.py --out "$OUT/buffered_alloc_results.json"
  stage B7 "compare with an external equivalence checker" \
    in_out "$PY" "$HERE/harness/eval-scripts/run_qcec.py"
fi

# ======================================================== tier C: hardware
KEY="$HERE/apikey.json"
if [ "$CORE_ONLY" -eq 1 ]; then
  skip C "IBM job-record recovery" "--core-only"
elif [ ! -f "$KEY" ]; then
  skip C "IBM job-record recovery" "no apikey.json (see apikey.json.example)"
else
  echo
  echo "apikey.json found — recovering the raw IBM job records."
  echo "This retrieves jobs that already ran. It consumes no QPU time."
  stage C1 "recover per-job provenance from the IBM job history" \
    "$PY" harness/ibm-hardware/collect_provenance.py --counts \
        --out "$OUT/provenance.json"
  stage C2 "recompute the published cells from the recovered counts" \
    "$PY" harness/ibm-hardware/reconcile_provenance.py \
        --provenance "$OUT/provenance.json" --out "$OUT/reconciliation-live.json"
fi

# ======================================================== tier D: live QPU
if [ "$SUBMIT_QPU" -eq 1 ] && [ "$CORE_ONLY" -eq 1 ]; then
  skip D "live QPU campaign" "--core-only"
elif [ "$SUBMIT_QPU" -eq 1 ] && [ ! -f "$KEY" ]; then
  skip D "live QPU campaign" "no apikey.json"
elif [ "$SUBMIT_QPU" -eq 1 ]; then
  cat <<'WARN'

  ####################################################################
  #  --submit-qpu SUBMITS NEW JOBS TO REAL IBM HARDWARE.             #
  #                                                                  #
  #  Cost: about 8 minutes of metered QPU time. The IBM open plan     #
  #  grants 10 minutes per month, so one full run uses nearly all of  #
  #  a month's allowance.                                             #
  #                                                                  #
  #  The submission scripts overwrite sweep_prereg.json and the       #
  #  result files. Those files hold the pre-registration and the      #
  #  measurements that the paper reports. This script copies them to  #
  #  artifact-run/shipped-backup/ first. Git also holds them, so      #
  #  "git checkout -- harness/ibm-hardware" restores them.            #
  #                                                                  #
  #  Press Ctrl-C in the next 15 seconds to stop.                     #
  ####################################################################

WARN
  sleep 15
  mkdir -p "$OUT/shipped-backup"
  cp harness/ibm-hardware/*.json harness/ibm-hardware/*.md "$OUT/shipped-backup/" 2>/dev/null
  echo "backed up the shipped hardware records to artifact-run/shipped-backup/"

  stage D1 "check the IBM connection and list the backends" \
    "$PY" harness/ibm-hardware/connect_ibm.py
  stage D2 "submit the distance-resolved leak job" \
    "$PY" harness/ibm-hardware/submit_ibm.py
  # wait_ibm.py stops polling after about 9 minutes and asks you to run it
  # again. Call it in a loop until it gives a verdict.
  wait_primary() {
    for _ in 1 2 3 4 5 6 7 8 9 10; do
      "$PY" harness/ibm-hardware/wait_ibm.py || return 1
      [ -f harness/ibm-hardware/ibm_results.json ] && return 0
    done
    echo "job did not finish within the polling budget"; return 1
  }
  stage D3 "wait for the leak job and analyse it" wait_primary
  stage D4 "submit the mechanism-control job" \
    "$PY" harness/ibm-hardware/submit_control.py
  wait_control() {
    for _ in 1 2 3 4 5 6 7 8 9 10; do
      "$PY" harness/ibm-hardware/wait_ctrl.py || return 1
      [ -f harness/ibm-hardware/ibm_ctrl_results.json ] && return 0
    done
    echo "control job did not finish within the polling budget"; return 1
  }
  stage D5 "wait for the control job and analyse it" wait_control
  stage D6 "submit the 8-pair leak sweep on two devices" \
    "$PY" harness/ibm-hardware/submit_sweep.py
  collect_sweep() {
    for _ in 1 2 3 4 5 6 7 8 9 10 11 12; do
      "$PY" harness/ibm-hardware/collect_sweep.py && return 0
      sleep 60
    done
    echo "sweep jobs did not all finish"; return 1
  }
  stage D7 "wait for the sweep and analyse it" collect_sweep
  stage D8 "submit the second-snapshot replication" \
    "$PY" harness/ibm-hardware/submit_repeat.py
  stage D9 "wait for the replication and analyse it" \
    "$PY" harness/ibm-hardware/collect_repeat.py --wait
elif [ -f "$KEY" ]; then
  skip D "live QPU campaign" "not requested (add --submit-qpu)"
fi

# =========================================================== the summary
{
  echo "# Artifact run summary"
  echo
  echo "Host: $(uname -s) $(uname -m)"
  echo
  echo "| stage | what it does | verdict | time |"
  echo "|---|---|---|---|"
  printf '%s\n' "${ROWS[@]}"
  echo
  echo "pass $PASS · fail $FAIL · skip $SKIP"
  echo
  echo "Logs are in \`artifact-run/logs/\`."
} > "$SUMMARY"

say "summary"
printf '%s\n' "${ROWS[@]}" | sed 's/|/ /g'
echo
echo "pass $PASS · fail $FAIL · skip $SKIP"
echo "wrote ${SUMMARY#$HERE/}"

# Report whether the shipped results changed. They must not.
if command -v git >/dev/null && [ -d "$HERE/.git" ]; then
  CHANGED="$(git -C "$HERE" status --porcelain -- harness QpuCompiler)"
  if [ -n "$CHANGED" ]; then
    echo
    echo "note: this run changed files that the repository ships:"
    echo "$CHANGED"
    echo "'git checkout -- harness QpuCompiler' restores them."
  fi
fi

[ "$FAIL" -eq 0 ] || exit 1
