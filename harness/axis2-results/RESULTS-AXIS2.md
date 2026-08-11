> ⚠️ **SUPERSEDED (2026-07-28).** The **unsound `parseQASM`** produced the numbers below (0/28
> false-reject, 99.9% parse-coverage, 28/35=80% caught). That parser *silently skipped*
> classically-conditioned gates. This was a fuzz-confirmed unsound-accept bug (269/1120
> false-accepts).

> The paper cites the **sound `parseQASMSafe`** re-run instead. That re-run gives
> a **violation rate of 18/53/71/71%** across Qiskit opt-levels 0 to 3, with 0 confinement
> false-rejects. This equals 27 of 28 accepted, plus 1 safe parse-reject of `shor_n5`. See
> `axis2-results/optlevel-results.md` and `fuzz-results.md`. We keep this file as the historical
> first-pass record. **Do not cite its headline numbers.**

# Real transpiled circuits at scale — paper question E1 (RESULTS)

We ran the paper's E1 coverage evaluation on **real benchmark circuits** end to end:
QASMBench (PNNL) `small` suite → Qiskit `transpile` (v2.5.0) to the Lean device model's
**12-node heavy-hex ring** + **basis subset** `{x, sx, rz, cz, id}` → untrusted
`parseQASM` → trusted `certifySecurity heavyHex tenantF` (tenant `A={0..5}`, forbidden
co-tenant `F={6..11}`). Date: 2026-07-23. This does not re-derive the shipped `#eval`s. These are
stock-transpiler outputs. The validator never saw them before this run.

## Method
- **Source:** QASMBench `small` (git `pnnl/QASMBench`, sparse `small/`), 42 circuit directories,
  `n2`–`n10` qubits. We stripped measurements, `reset`, and `barrier`, because the model is
  unitary-support only.

- **Regime A — confined:** We transpiled circuits with ≤6 qubits onto the tenant sub-lattice
  (path `0-1-2-3-4-5`, all ring edges). Expectation: **ACCEPT**, because the support lies in `A`
  and the circuit is legal.

- **Regime B — unconstrained:** We transpiled all circuits onto the full 12-node ring with free
  layout (a *tenant-unaware* stock transpiler — exactly the threat model). Expectation:
  **REJECT** whenever the transpiler spills the circuit of the tenant onto `F={6..11}`.

- **Certification:** We ran one `lake env lean --run CertifyQASM.lean` invocation per regime.
- `transpile_axis2.py` reproduces the transpile step. We ship the verdict logs and
  `manifest.json`.

## Results

| Metric | Regime A (confined to `{0..5}`) | Regime B (unconstrained 12-ring) |
|---|---|---|
| circuits certified | 28 | 35 |
| ACCEPT / REJECT | **28 / 0** | 7 / 28 |
| hardware-legal | 28/28 (100%) | **35/35 (100%)** |
| policy-confined | 28/28 | 7/35 |
| **false-reject rate** (confined wrongly rejected) | **0 / 28** | — |
| **tenant-isolation violations caught** | — | **28 / 35 (80%)** |
| parse-coverage (gate lines lexer recognized) | 3428/3432 (99.9%) | 7104/7108 (99.9%) |

- **Gate scale.** Certified circuits ranged from **10 to 1391 gates** (`basis_trotter_n4`). We
  certified **10,532 gates** across 63 runs. This is real transpiler output, not toy circuits.

- **Headline empirical finding:** a stock, tenant-**unaware** transpiler placed **80%** of
  benchmark circuits partly on forbidden co-tenant qubits. The validator caught **every** one. Each
  showed `legal=true` yet `confined=false`. That is the direct-contact case at benchmark scale:
  hardware legality alone never implies tenant safety.

- **False-reject rate 0 of 28.** When the transpiler *did* respect the tenant region, the
  validator never rejected wrongly. There was no over-blocking.

- The 7 ACCEPTs in Regime B are small circuits (`n2` and a few others) that the transpiler
  happened to place entirely within `{0..5}`. These are genuinely confined, and correctly
  accepted.

## Honesty notes (carried to the paper's Limitations)
- **Skipped classically-conditioned gates.** 8 gate lines (0.1%), all in `shor_n5`, are
  `if (c==k) rz(...) q[i];`. The basis-subset lexer *silently skips* them. This changed **no**
  verdict here. Those lines touch `q[2] ∈ A`, which is harmless. They touch `q[9] ∈ F` only inside
  the full-ring `shor_n5`, and other gates already made that circuit REJECTED.

  **But** if a skipped
  *support-bearing* gate is the sole forbidden contact of a circuit, it can in principle cause an
  *unsound accept*. So the "a lexer gap can only cause a safe rejection" invariant is exact for
  parse-*failures* but **not** for silently-*skipped* constructs. The fix, noted as future
  hardening, is that the untrusted lexer must **reject any unrecognized support-bearing token**
  instead of skipping it. That restores the safe-rejection-only invariant. The trusted core,
  `certifySecurity_sound`, does not change, because it is sound over whatever circuit it gets.

- **Scope, unchanged.** The device is the 12-node ring. The tenant regions stay fixed at
  `{0..5}` and `{6..11}`. We cover only the basis subset. To support larger devices and
  policies, we must first generalize `heavyHex`, `n`, and `tenantF` in the Lean model.

  We skipped 7 QASMBench files at load. Some files contain malformed syntax. Others hold
  mid-circuit conditional QASM that Qiskit cannot import: `hhl_n10, inverseqft_n4, ipea_n2,
  qec_sm_n5, vqe_uccsd_n4, vqe_uccsd_n6, vqe_uccsd_n8`. We did not fabricate any of these numbers.

## Reproduce
```
pip install qiskit          # v2.5.0 used
git clone --depth 1 --filter=blob:none --sparse https://github.com/pnnl/QASMBench.git
(cd QASMBench && git sparse-checkout set small)
python3 transpile_axis2.py  # edit SMALL/OUT paths. Writes axis2/{confinedA,fullB}/*.qasm
# then, from the qpu-compiler/ project root, after `lake build`:
python3 ../CertifyQASM-driver certify_qasm.py --files axis2/confinedA/*.qasm
python3 certify_qasm.py --files axis2/fullB/*.qasm
```
We ship verdict logs (`verdictA.txt`, `verdictB.txt`) and `manifest.json` (per-circuit qubit
counts and parse-coverage) alongside this file.
