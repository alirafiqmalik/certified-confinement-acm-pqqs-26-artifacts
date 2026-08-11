# Multi-device validator testing — paper question E3 (11 real QPU topologies, zero QPU time)

## What this answers

Can we run the Lean validator against *real* hardware graphs without hardware access?
**Yes. This work also removed a limitation that the paper used to disclose.**

`qiskit_ibm_runtime.fake_provider` ships topology and calibration snapshots for ~68 real IBM
devices. It needs no account, no token, and no quota. We encode a diverse slice as Lean
`Coupling n` values. We run the validator against every one.

## The result that matters: the device-size ceiling is gone

The paper previously said, in its limitations:

> *"Encoding larger (20–30-qubit) patches is deferred: the kernel `decide` on the edge relation
> degrades at that size (an implementation limit, not a method limit)."*

That statement named the cause correctly. We have now removed the ceiling. The ceiling came from
*representation*, not from the method. `heavyHex`, `heronPatch` and `heronMarrakesh` each write the
edge relation as an explicit decidable **disjunction**. A 156-qubit device with 176 canonical edges
therefore produced a term that took the kernel a long time to reduce on every `decide`.

`QpuCompiler/DeviceLib.lean` replaces that with the graph as **data**, a canonical ordered edge
list. It discharges the three `Coupling` obligations **once, generically**:

| obligation | how it is now discharged |
|---|---|
| `edge_symm` | free: `edge a b := (min a b, max a b) ∈ edges` is symmetric *by construction* |
| `edge_irrefl` | from `ordered`: every stored pair has `p.1 < p.2`, so `(a,a)` cannot be present |
| `edge_bounds` | from `bounded`: every stored pair has `p.2 < n` |

One further detail was important. If you state the side conditions as `∀ p ∈ edges, p.1 < p.2`,
then `by decide` runs an instance search **for each element**. This exhausts `maxRecDepth` at
about 176 edges. If you state them as a single `List.all (…) = true` Bool fold, the goal reduces
to a straight computation that the kernel handles without difficulty. That one change is the
difference between "impossible" and "3 seconds".

**Measured: all four verdicts on the full 156-qubit Heron r2 topology, kernel-checked by `decide`, in
~3 s.**

## Corpus

| device | qubits | edges | family | verdicts |
|---|---|---|---|---|
| `FakeLagosV2` | 7 | 6 | small linear/T | KERNEL |
| `FakeGuadalupeV2` | 16 | 16 | heavy-hex | KERNEL |
| `FakeHanoiV2` | 27 | 28 | heavy-hex | KERNEL |
| `FakeBrooklynV2` | 65 | 72 | heavy-hex | KERNEL |
| `FakeNighthawk` | 120 | 218 | **square lattice, degree 4** | KERNEL |
| `FakeSherbrooke` | 127 | 144 | heavy-hex Eagle | KERNEL |
| `FakeWashingtonV2` | 127 | 142 | Eagle, different wiring | KERNEL |
| `FakeTorino` | 133 | 150 | Heron r1 | KERNEL |
| `FakeMarrakesh` | 156 | 176 | **Heron r2 — device we measured** | KERNEL |
| `FakeFez` | 156 | 176 | **Heron r2 — also measured** | KERNEL |
| `FakeKingston` | 156 | 176 | **Heron r2 — never measured** | KERNEL |

The generator skips `FakeBelemV2`, which has 5 qubits. It is too small to allow a partition with a
genuine region at distance 2 or more. The generator records that fact instead of inventing a
partition.

**44 kernel-checked verdicts** (11 devices × 4), plus 22 kernel-checked encoding obligations.
The full build is green at **2381 jobs**. The axioms are `[propext, Quot.sound]`. There is no
`sorry`, no `native_decide` and no `ofReduceBool`.

## What is asserted per device

We seed the co-tenant region `F` at the **most interior maximum-degree qubit**. This is
deliberately not a boundary case. A boundary case makes the test trivial. Then, with distances
measured from the whole region:

1. **THE GAP.** The support-only `confinedb` **accepts** a placement that is support-disjoint from
   `F` but sits on its 1-hop ring. `= true`
2. **THE FIX.** The neighbour-buffered policy **rejects** exactly that placement. `= false`
3. **NO OVER-BLOCK.** A placement at distance ≥2 is still **accepted**. `= true`
4. **POLICY, NOT LEGALITY.** The rejected placement is `hardwareLegal = true`. So the refusal
   comes from the tenant policy, not from the hardware graph. `= true`

Every one of these four checks held on every device, including a **degree-4 square lattice**
(`Nighthawk`). We built the paper around the heavy-hex family. This topology family is
genuinely different from it.

## Honest scope

- These are **topologies**, exactly as published. This encoding work shows that the validator
  handles real device graphs at real scale. It says nothing about leaks on those devices. That is
  a physics question, and it needs hardware. Read `sim/BLIND-EMULATION.md`.
- `Nighthawk` widens topology coverage, but it is still an IBM device. This work does not
  cover non-IBM architectures (ion-trap all-to-all, neutral-atom reconfigurable).
- The guarantee of the validator does not change. This is a result about scale and coverage, not a
  new theorem.

## Reproduce

```
python gen_device_corpus.py     # writes QpuCompiler/DeviceCorpus.lean + corpus_meta.json
bash verify_corpus.sh           # the real check — see below
```

`verify_corpus.sh` does two things that a plain `lake build` does **not**:

1. **It defeats the replay cache of Lake.** Lake reports "Build completed successfully" while it
   replays a cached `.olean`. In that case, the kernel does not check any `decide` call again. The script
   deletes `DeviceCorpus.{olean,ilean,trace}` first, so the kernel checks all 44
   verdicts again, from scratch. Measured: **4.9 s** for the module, and 7 s of wall time.

2. **It recomputes every verdict outside the generated file.** The corpus is machine-generated. A
   codegen defect can therefore emit a claim that is vacuous, or that asserts the wrong expected
   value, and the file still "proves". An independent `IO` harness recomputes all four verdicts for
   each device, and tests the `true/false/true/true` pattern. Such a defect then causes a
   `FAIL`, instead of a silent pass.

Last run: **ALL 11 DEVICES PASS (44 verdicts recomputed independently)**. The hygiene check is
clean, with 68 uses of `by decide`.
