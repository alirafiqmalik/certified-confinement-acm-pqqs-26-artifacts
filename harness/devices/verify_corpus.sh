#!/usr/bin/env bash
# verify_corpus.sh — independently re-verify the device corpus.
#
# Two things this does that a plain `lake build` does not:
#
#   1. DEFEATS THE REPLAY CACHE. Lake can report "Build completed successfully"
#      while it replays a cached .olean. In that case, Lake does not re-check
#      `decide` at all. This script deletes the module's build products first.
#      Then the kernel genuinely re-verifies all 44 `by decide` verdicts from
#      scratch.
#
#   2. RECOMPUTES EVERY VERDICT OUTSIDE THE GENERATED FILE. The corpus is
#      machine-generated. A codegen bug can emit a claim that is vacuous, or
#      that asserts the wrong expected value. Even so, such a claim can still
#      succeed when Lean checks it. The IO harness below recomputes all four
#      verdicts per device. It checks the expected true/false/true/true
#      pattern, so a bug like this surfaces as a FAIL.
#
# Usage:  bash verify_corpus.sh          (from anywhere)
set -uo pipefail
# Locate the project root relative to this script. This keeps the artifact portable.
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "$SCRIPT_DIR/../.." && pwd)"
export PATH="$HOME/.elan/bin:$PATH"
cd "$ROOT" || exit 1
[ -f lakefile.toml ] || { echo "error: project root not found (looked in $ROOT)"; exit 1; }

echo "=== 1. defeating Lake's replay cache for DeviceCorpus ==="
rm -f .lake/build/lib/lean/QpuCompiler/DeviceCorpus.olean \
      .lake/build/lib/lean/QpuCompiler/DeviceCorpus.ilean \
      .lake/build/lib/lean/QpuCompiler/DeviceCorpus.trace 2>/dev/null
echo "removed .olean/.ilean/.trace — kernel must re-check all 'by decide' verdicts"

echo
echo "=== 2. genuine kernel re-verification ==="
START=$(date +%s)
lake build QpuCompiler.DeviceCorpus 2>&1 | grep -viE "^warning|^Note:|^Hint:|linter|binding can be" | tail -4
END=$(date +%s)
echo "elapsed: $((END-START))s"

echo
echo "=== 3. independent recomputation of every verdict (guards against codegen bugs) ==="
HARNESS="$(mktemp -t verify_corpus.XXXXXX.lean)"
trap 'rm -f "$HARNESS"' EXIT
cat > "$HARNESS" <<'LEAN'
import QpuCompiler.DeviceCorpus
open QpuCompiler

/-- Recompute the four verdicts for one device, independently of the `example`s in
the generated file, and report whether they match the expected pattern. -/
def check (name : String) (nq ne : Nat)
    (gap fix noblock legal : Bool) : IO Bool := do
  let ok := gap == true && fix == false && noblock == true && legal == true
  IO.println s!"{if ok then "PASS" else "FAIL"} {name} ({nq}q, {ne}e)  gap={gap} fix={fix} noblock={noblock} legal={legal}"
  return ok

def main : IO Unit := do
  let mut fails := 0
  let run (n : String) (nq ne : Nat) (g f nb l : Bool) : IO Bool := check n nq ne g f nb l
  let rs ← #[
    (← run "FakeLagosV2" 7 6
      (certifySecurity dev_lagos F_lagos adj_lagos).accepted
      (certifySecurity dev_lagos (bufferF dev_lagos F_lagos) adj_lagos).accepted
      (certifySecurity dev_lagos (bufferF dev_lagos F_lagos) far_lagos).accepted
      (certifySecurity dev_lagos (bufferF dev_lagos F_lagos) adj_lagos).hardwareLegal),
    (← run "FakeGuadalupeV2" 16 16
      (certifySecurity dev_guadalupe F_guadalupe adj_guadalupe).accepted
      (certifySecurity dev_guadalupe (bufferF dev_guadalupe F_guadalupe) adj_guadalupe).accepted
      (certifySecurity dev_guadalupe (bufferF dev_guadalupe F_guadalupe) far_guadalupe).accepted
      (certifySecurity dev_guadalupe (bufferF dev_guadalupe F_guadalupe) adj_guadalupe).hardwareLegal),
    (← run "FakeHanoiV2" 27 28
      (certifySecurity dev_hanoi F_hanoi adj_hanoi).accepted
      (certifySecurity dev_hanoi (bufferF dev_hanoi F_hanoi) adj_hanoi).accepted
      (certifySecurity dev_hanoi (bufferF dev_hanoi F_hanoi) far_hanoi).accepted
      (certifySecurity dev_hanoi (bufferF dev_hanoi F_hanoi) adj_hanoi).hardwareLegal),
    (← run "FakeBrooklynV2" 65 72
      (certifySecurity dev_brooklyn F_brooklyn adj_brooklyn).accepted
      (certifySecurity dev_brooklyn (bufferF dev_brooklyn F_brooklyn) adj_brooklyn).accepted
      (certifySecurity dev_brooklyn (bufferF dev_brooklyn F_brooklyn) far_brooklyn).accepted
      (certifySecurity dev_brooklyn (bufferF dev_brooklyn F_brooklyn) adj_brooklyn).hardwareLegal),
    (← run "FakeNighthawk" 120 218
      (certifySecurity dev_nighthawk F_nighthawk adj_nighthawk).accepted
      (certifySecurity dev_nighthawk (bufferF dev_nighthawk F_nighthawk) adj_nighthawk).accepted
      (certifySecurity dev_nighthawk (bufferF dev_nighthawk F_nighthawk) far_nighthawk).accepted
      (certifySecurity dev_nighthawk (bufferF dev_nighthawk F_nighthawk) adj_nighthawk).hardwareLegal),
    (← run "FakeSherbrooke" 127 144
      (certifySecurity dev_sherbrooke F_sherbrooke adj_sherbrooke).accepted
      (certifySecurity dev_sherbrooke (bufferF dev_sherbrooke F_sherbrooke) adj_sherbrooke).accepted
      (certifySecurity dev_sherbrooke (bufferF dev_sherbrooke F_sherbrooke) far_sherbrooke).accepted
      (certifySecurity dev_sherbrooke (bufferF dev_sherbrooke F_sherbrooke) adj_sherbrooke).hardwareLegal),
    (← run "FakeWashingtonV2" 127 142
      (certifySecurity dev_washington F_washington adj_washington).accepted
      (certifySecurity dev_washington (bufferF dev_washington F_washington) adj_washington).accepted
      (certifySecurity dev_washington (bufferF dev_washington F_washington) far_washington).accepted
      (certifySecurity dev_washington (bufferF dev_washington F_washington) adj_washington).hardwareLegal),
    (← run "FakeTorino" 133 150
      (certifySecurity dev_torino F_torino adj_torino).accepted
      (certifySecurity dev_torino (bufferF dev_torino F_torino) adj_torino).accepted
      (certifySecurity dev_torino (bufferF dev_torino F_torino) far_torino).accepted
      (certifySecurity dev_torino (bufferF dev_torino F_torino) adj_torino).hardwareLegal),
    (← run "FakeMarrakesh" 156 176
      (certifySecurity dev_marrakesh F_marrakesh adj_marrakesh).accepted
      (certifySecurity dev_marrakesh (bufferF dev_marrakesh F_marrakesh) adj_marrakesh).accepted
      (certifySecurity dev_marrakesh (bufferF dev_marrakesh F_marrakesh) far_marrakesh).accepted
      (certifySecurity dev_marrakesh (bufferF dev_marrakesh F_marrakesh) adj_marrakesh).hardwareLegal),
    (← run "FakeFez" 156 176
      (certifySecurity dev_fez F_fez adj_fez).accepted
      (certifySecurity dev_fez (bufferF dev_fez F_fez) adj_fez).accepted
      (certifySecurity dev_fez (bufferF dev_fez F_fez) far_fez).accepted
      (certifySecurity dev_fez (bufferF dev_fez F_fez) adj_fez).hardwareLegal),
    (← run "FakeKingston" 156 176
      (certifySecurity dev_kingston F_kingston adj_kingston).accepted
      (certifySecurity dev_kingston (bufferF dev_kingston F_kingston) adj_kingston).accepted
      (certifySecurity dev_kingston (bufferF dev_kingston F_kingston) far_kingston).accepted
      (certifySecurity dev_kingston (bufferF dev_kingston F_kingston) adj_kingston).hardwareLegal)
  ].toList.filterM (fun b => pure (!b))
  fails := rs.length
  IO.println ""
  if fails == 0 then
    IO.println "ALL 11 DEVICES PASS (44 verdicts recomputed independently)"
  else
    IO.println s!"{fails} DEVICE(S) FAILED"
LEAN
lake env lean --run "$HARNESS" 2>&1 | tail -16

echo
echo "=== 4. hygiene ==="
if grep -nE "sorry|native_decide|ofReduceBool|^axiom " QpuCompiler/DeviceCorpus.lean QpuCompiler/DeviceLib.lean; then
  echo "FORBIDDEN TACTIC FOUND"; exit 1
else
  echo "clean: no sorry / native_decide / ofReduceBool / axiom"
fi
echo "devices: $(grep -c '^def dev_' QpuCompiler/DeviceCorpus.lean) · by decide: $(grep -c 'by decide' QpuCompiler/DeviceCorpus.lean)"
