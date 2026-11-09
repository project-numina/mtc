# Contributing

This repository's primary purpose is the complete pivotal Property F
manuscript formalization. Prefer changes that simplify, explain, or strengthen
its checked proof and reusable mathematical infrastructure.

1. Develop on a branch and preserve others' uncommitted work.
2. Compare statements with the manuscript, including hypotheses, quantifiers,
   categorical constructions and Galois conventions. Passing Lean does not
   establish that a statement matches the intended mathematics.
3. Preserve the frozen original `MTC/PropertyF/Statement.lean` and
   `MTC.PropertyF.weaklyIntegral_of_propertyF`. Preserve the mathematical
   content of the new pivotal targets as well.
4. All library proofs must be complete and depend only on `propext`,
   `Classical.choice` and `Quot.sound`. There is no exception for conjectures:
   do not add `sorry`, `admit`, custom axioms or foreign implementations.
5. Prefer existing mathematical APIs and coherent modules. Use source-size
   distributions to locate review candidates, not as quotas: do not hide
   assumptions, compress formatting or introduce trivial wrappers to improve
   a metric.
6. Update the paper-to-Lean map when public results change. Run
   `python3 scripts/update_roots.py`, maintain both audit import lists, then
   run `scripts/check.sh` and `scripts/audit-target.sh`.
7. Describe the mathematical change, validation and remaining limitations in
   the pull request. Disclose substantial AI assistance.

Existing data encodings are supporting material. A numerical modular datum
alone is not proof that a realizing category exists.
