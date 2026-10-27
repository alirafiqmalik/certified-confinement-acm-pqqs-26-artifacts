# Repository structure and maintenance

All shell commands in these guides run from the repository root.

## Directory responsibilities

| Location | Responsibility |
|---|---|
| `QpuCompiler/` | Lean library modules; preserve this namespace for imports |
| `examples/` | Small, readable input circuits with known verdicts |
| `harness/` | Executable validation and experiment workflows |
| `harness/benchmarks/` | Transpiler and fuzzing experiments, plus their reference data |
| `harness/axis2-results/` | Historical benchmark reports and verdict records |
| `harness/devices/` | Device generation, metadata, and independent verification |
| `harness/sim/` | Offline simulations and regression checks |
| `harness/ibm-hardware/` | Hardware experiments, recorded measurements, and provenance |
| `docs/` | User guides and the mapping between paper claims and code |
| `docs/assets/` | Reproducibly generated presentation figures |
| `scripts/` | Repository maintenance utilities |
| `artifact-run/` | Ignored local reproduction outputs |

Reference measurements stay alongside their experiment workflows to preserve
relative data loading and provenance. Historical result names remain stable;
[the paper map](PAPER.md) explains their relationship to the evaluation questions.

## Paths changed in this reorganization

| Previous path | Current path |
|---|---|
| `SETUP.md` | `docs/SETUP.md` |
| `USAGE.md` | `docs/USAGE.md` |
| `PAPER.md` | `docs/PAPER.md` |
| `harness/samples/` | `examples/` |
| `harness/eval-scripts/` | `harness/benchmarks/` |

The root commands `bash setup.sh`, `lake build`, and `bash run_artifact.sh`
remain the entry points. `certify_qasm.py --samples` discovers `examples/`
relative to its own repository root.

## Regenerate README figures

Use a Python environment with Matplotlib installed:

```bash
python3 scripts/render_readme_figures.py
```

The topology figure reads the CZ operations from `examples/02_cotenant_touch.qasm`.
Its ring geometry and partition follow `heavyHex` in `QpuCompiler/CompileHH.lean`
and `tenantF` in `QpuCompiler/Confine.lean`; update the renderer if those definitions
change. The benchmark chart reads `harness/benchmarks/e5_results.json` directly.
The renderer emits SVGs with selectable text and no changing date metadata.
Matplotlib is only needed for regenerating figures, not for running the artifact.

## Verify changes

```bash
bash -n setup.sh run_artifact.sh
bash run_artifact.sh --core-only
```

For benchmark changes, also run the benchmark tier described in [USAGE.md](USAGE.md).
Review generated result differences before replacing any reference data.
