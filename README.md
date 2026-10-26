# Property F and weak integrality

Conditional Lean 4 / Mathlib formalization of the six-page paper in `paper/`.

The main theorem is `PropertyF.propertyF_implies_weaklyIntegral` in
[PropertyF/Main.lean](PropertyF/Main.lean). Matrix trace estimates, overlapping
products, Galois rigidity, modular symmetry, the contradiction and arithmetic
conclusion are proved. The closure and objectwise consequences are also checked.

The theorem has explicit literature and categorical realization inputs. Some
realization bridges remain unconstructed. See the complete
[assumption ledger and limitations](FORMALIZATION.md) before treating this as a
fully constructed categorical development. There are no `sorry` proofs or
global custom axiom declarations; this does not discharge the input structures.

Lean and Mathlib are pinned to `v4.35.0`. Fetch the compiled Mathlib cache first:

```sh
LEAN_NUM_THREADS=8 taskset -c 0-7 lake exe cache get
bash scripts/check.sh
```

The default build includes the axiom audit. Its recorded output is in
[AXIOMS.txt](AXIOMS.txt). The paper-to-Lean map and Mathlib audit are in
[PLAN.md](PLAN.md).
