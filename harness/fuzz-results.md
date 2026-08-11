# E3 — Front-end fuzz (Giallar-style: fuzzer found a soundness bug, we fixed it)

> **RE-VERIFIED 2026-07-30.** We re-ran the full 1120-mutant corpus after the `qasmStmts`
> comment-ordering fix in `Frontend.lean` (a `//` comment containing a `;` used to leave a
> fragment that looked like a statement). The result is identical. The OLD `parseQASM`
> produced 269 false accepts. The NEW `parseQASMSafe` produced 0 false accepts, for 100%
> caught. The fix costs no soundness.

**Setup.** We generated 1120 mutants from the confined QASMBench-small transpilations
(seed=7). We used four mutation operators: relocate-gate-onto-F, insert-boundary-cz,
inject-conditioned-token (`if(c==k)…`), and index-alias-into-F. Every mutant is ground-truth
**reject**, because each one introduces either a support violation or an unmodellable token. We
certified each mutant against the ring, with F={6..11}.

## Result — the fuzzer exposed the unsound skip, and `parseQASMSafe` closes it
| lexer | mutants | **false-accepts** | caught | caught-rate |
|---|---|---|---|---|
| OLD `parseQASM` (silent skip) | 1120 | **269** | 851 | 76.0% |
| **NEW `parseQASMSafe`** | 1120 | **0** | 1120 | **100%** |

- The **269 false-accepts** under the old lexer are exactly the conditioned-gate mutants
  (`if(c==k) cz q[a],q[b];`). The old parser silently skipped the guarded gate. It then certified
  the confined-looking remainder as an **unsound accept**. This is the soundness hole flagged in
  the Axis-2 run and in review feedback.

- `parseQASMSafe` rejects any unrecognized support-bearing token. The result is **0 false-accepts,
  100% caught**.

- The invariant "an untrusted-lexer gap can only cause a *safe rejection*" now holds for silent
  *skips*, not just parse failures. The trusted core stays unchanged (`certifySecurity_sound` =
  `[propext]`).

**Paper framing (§7.1, §9):** We fuzzed our own untrusted front-end. It found 269 unsound accepts.
The `parseQASMSafe` fix drives false-accepts to 0 over 1120 adversarial mutants.
