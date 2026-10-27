# Setup

Two toolchains: Lean 4 for the proofs, Python for the harness. Nothing else is
required for the offline reproduction.

## 1. Lean

If `lake` is already on your PATH, skip this step.

```bash
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
export PATH="$HOME/.elan/bin:$PATH"
```

`elan` reads `lean-toolchain` and installs the pinned compiler, Lean 4.31.0.
`lakefile.toml` pins Mathlib to the matching tag.

Build the library once:

```bash
lake build
```

Expected: `Build completed successfully (2381 jobs)`.

**The first build compiles Mathlib and takes 30 minutes or more.** It needs about
5 GB of disk. Every later build replays the cache and takes seconds. Nothing
else in this artifact works until this build succeeds.

## 2. Python

```bash
bash setup.sh
```

This creates `.venv/` and installs four packages:

| package | used for |
|---|---|
| `qiskit` | circuit representation, OpenQASM input and output, transpilation |
| `qiskit-aer` | local noise-model simulation in `harness/sim/` |
| `qiskit-ibm-runtime` | IBM backend access, and the offline device snapshots in `harness/devices/` |
| `mqt.qcec` | only for the external equivalence-checker comparison |

`setup.sh` is safe to re-run: it reuses an existing `.venv` and the install is
idempotent. `run_artifact.sh` calls it for you if `.venv/` is missing.

The reference run used qiskit 2.5.1 and qiskit-aer 0.17.2. `mqt.qcec` is the
heaviest dependency and only stage B7 needs it.

## 3. QASMBench (optional)

Stages B1 to B7 sweep the QASMBench suite. It is an external benchmark set and
this artifact does not vendor it.

```bash
bash run_artifact.sh --fetch-benchmarks
```

That clones `pnnl/QASMBench` into `harness/QASMBench/` and runs the tier. If you
already have a copy:

```bash
QASMBENCH_SMALL=/path/to/QASMBench/small bash run_artifact.sh
```

Without either, the tier is skipped and reported as skipped. Everything else
still runs.

## 4. IBM credentials (optional)

You do **not** need an IBM account to check the hardware numbers. Stage A9
recomputes all 16 published cells offline from `harness/ibm-hardware/provenance.json`.

A token adds two things: recovery of the raw job records from your own IBM job
history (read-only, no QPU time), and the ability to measure again on real
hardware.

```bash
cp apikey.json.example apikey.json
# paste your token from https://quantum.ibm.com/ under Account settings
```

```json
{
  "apikey": "your token here",
  "instance": ""
}
```

Leave `instance` empty to use the default instance of the account. You can also
set `IBM_INSTANCE` in the environment instead.

`.gitignore` excludes every `apikey*.json` file, so a token cannot be committed
by accident. No script prints or writes a token.

**Metered time.** Only `bash run_artifact.sh --submit-qpu` spends QPU time, about
8 minutes for a full campaign. The IBM open plan grants 10 minutes per month.
Check your remaining allowance before you use that flag.

## Verifying the environment

```bash
bash run_artifact.sh --core-only
```

This runs the 9 stages that need neither QASMBench nor a token, and prints a
summary. If it reports 9 passes, the environment is correct.

## Troubleshooting

**`error: lake is not on PATH`** — the shell that runs the script has no Lean.
Run `export PATH="$HOME/.elan/bin:$PATH"` and try again.

**Stage A7 fails on test T8** — T8 calls `lake env lean` for a real kernel
verdict, so it fails if the Lean build is stale. Run `lake build` and re-run.

**Stage B7 fails on an import** — `mqt.qcec` did not install. It is the only
stage that needs it; the rest of the tier is unaffected.

**The run changed tracked files** — the script says so at the end. `git checkout
-- harness QpuCompiler` restores them.
