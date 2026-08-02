# E6 — QCEC capability contrast (NOT a speed claim)

According to the A2-FINAL ruling, this is a **capability contrast first**. We show timing only
as context, clearly labelled as a different task. We never show it as "we are faster than
QCEC".

## Capability (the load-bearing point)
| tool | decides | complexity | tenant-confinement policy | trust |
|---|---|---|---|---|
| **QCEC (mqt.qcec 3.7.0)** | functional **equivalence** | Θ(2ⁿ) worst case / QMA-hard | **cannot express — no notion of qubit regions** | unverified checker |
| **this work** | hardware-legality + **tenant confinement** | Θ(#gates), decidable | **is the property it certifies** | kernel-checked (`[propext]`) |

QCEC and our certifier answer **different questions**. QCEC verifies that a transpiled circuit is
functionally equivalent to its source. It **does not represent tenant regions**. It can therefore
neither express nor test "the secret shares no qubit or edge with a co-tenant". Our certifier
does not solve equivalence in general, because that is the QMA-hard problem that we deliberately
avoid. It certifies a *decidable structural security property* in linear time.

## Timing context only (different task — do NOT frame as a comparison)
`mqt.qcec 3.7.0` ran equivalence checks over 7 QASMBench-small circuits, against their opt-3
transpilations. The median was **0.0205 s**. The range was 0.012 to 0.109 s. This only documents
that the DD engine of QCEC is itself fast on small structured circuits. That is exactly why a
"we are faster" curve is a strawman. NOTE: several checks returned `not_equivalent`, because the
garbage and ancilla qubit counts did not match while partial equivalence stayed off. That is a
QCEC configuration artifact. We make **no** claim from it.

**Ships as:** the capability row in Table 1, plus one sentence in §8. There is no comparative
speed figure.
