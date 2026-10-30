# Contributing

Contributions are welcome from mathematicians, Lean users and AI-assisted workflows. The project
needs careful statements and examples as well as proofs and exact data.

1. Pick a problem from the [dashboard](docs/STATUS.md), or propose a precise new one with a source.
   Check open issues and pull requests for overlapping work; claim the problem in an issue or comment
   so others can coordinate. Explain your intended scope and update the claim if you stop.
2. Check the Lean statement against the source, its quantifiers, hypotheses and known examples. Show
   that the hypotheses are satisfiable and add small, proved sanity checks where feasible. A numerical
   modular datum is not automatically a realized modular tensor category.
3. Develop on a branch. Add shared definitions and proved lemmas to `MTC/`; keep conjectures in
   `MTC/Conjectures/` as described in [the template](MTC/Conjectures/README.md). Use the existing frozen
   `PropertyF.Ground` definitions for property F. Do not edit `PropertyF/Ground/Target.lean` or the
   proof of `PropertyF.Ground.target`.
4. Replace the conjecture proof with a complete Lean proof, update its status and reference, and run
   `python3 scripts/conjecture_status.py` and `python3 scripts/update_roots.py`. A result is formalized only when its proof and all
   dependencies use no `sorry` and only `propext`, `Classical.choice` and `Quot.sound` as axioms.
   `PropertyF/` and `MTC/` outside `MTC/Conjectures/` must be sorry-free. Only the designated
   unformalized conjecture proof may use `sorry`; helper lemmas may not depend on an unproved
   conjecture. New axioms or opaque foreign implementations are not accepted.
5. Run `scripts/check.sh` and `scripts/audit-target.sh`, then open a pull request describing the
   result, the source, checks and any remaining limitations. For data, include provenance, coverage,
   the generation method and redistribution terms. Do not claim computational evidence beyond the
   data actually checked.

AI-assisted contributions are welcome. The submitter is responsible for the correctness of the
statement, citations, data provenance and proofs, and should disclose substantial AI assistance in the
pull request. Reviewers should be able to reproduce the checks and inspect the generated Lean code;
passing Lean does not establish that the formal statement matches the intended mathematics.

The metadata convention is inspired by [formal-conjectures](https://github.com/google-deepmind/formal-conjectures/blob/main/CONTRIBUTING.md),
with a smaller project-specific status vocabulary.
