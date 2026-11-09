# Property F implies weak integrality

A Lean 4 formalization of **Property F implies weak integrality for non-degenerate
pivotal braided fusion categories**, together with the degenerate extension and
the manuscript's supporting results.

The main theorem proves that a non-degenerate pivotal braided fusion category
with property F is pseudo-unitary and weakly integral, and every represented
Galois conjugate is pseudo-unitary. The degenerate theorem assumes positivity
of pivotal dimensions on the simple objects of the intersection of the Müger
centre and the adjoint subcategory.

## Start here

- [Main theorems](MTC/PropertyF/Pivotal/MainTheorems.lean):
  `nondegenerateMainStatement_proved` and `degenerateMainStatement_proved`.
- [Exact statements](MTC/PropertyF/Pivotal/Statement.lean), including the positivity
  condition and the semilinear-equivalence definition of Galois conjugates.
- [Manuscript and theorem map](papers/property-f-weak-integrality/README.md):
  trace bound, saturation, centre and normalization lemmas, closure, and the
  eventual infinite-braid-image corollary.
- [Verification record](docs/pivotal-verification.md).
- [Code distribution audit](docs/style/README.md): proof lengths, elaborated
  binders and module sizes compared with the inherited library and Mathlib.

No sphericality or pseudo-unitary Galois conjugate is assumed in the
non-degenerate pivotal theorem. The earlier result with a pseudo-unitary
Galois conjugate is preserved in [Theorem.lean](MTC/PropertyF/Theorem.lean).

## Library

The [MTC](MTC.lean) library contains the fusion-category, pivotal-dimension,
braid-group and Drinfeld-centre infrastructure used by the proofs. Every
library declaration is audited: no `sorry`, custom axioms, or foreign proof
implementations are allowed. Proofs use only `propext`, `Classical.choice`,
and `Quot.sound`.

Existing modular-data, F/R-symbol and Anyon Atlas support remains available,
but the project's primary deliverable is the manuscript formalization.
See [CONTRIBUTING.md](CONTRIBUTING.md) for proof and review requirements.

## Build and verify

Lean and Mathlib are pinned to v4.35.0.

```sh
lake exe cache get
scripts/check.sh
scripts/audit-target.sh
```

These build the library, check generated imports and statement equivalence,
run the script tests, and audit declarations and target dependencies.
The scripts use CPU cores 0–3 by default; set `PROPERTYF_AUDIT_CORES` to change this.
