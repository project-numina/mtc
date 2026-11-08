# Verification of the later pivotal manuscript

The source and its provenance are recorded in the
[paper map](../papers/property-f-weak-integrality/README.md). The new target
definitions and their proofs cover the nondegenerate and degenerate pivotal
theorems, the centre and normalization lemmas, the pseudo-unitary-conjugate
corollary, closure, and the eventual infinite-image corollary.

The target review checked that nondegeneracy is categorical transparency,
that the degenerate positivity condition agrees with positivity on actual
transparent simple objects in the generated adjoint category, and that the
objectwise target uses the constructed generated braided fusion category.
Galois conclusions quantify over every conjugate represented by the project's
semilinear braided equivalence structure. The closure proof uses actual braid
images, categorical colored crossings, pure braids, finite direct sums and
retracts. The general pivotal numerical centrality argument is proved without
assuming a positive spherical structure. The original Property F statement
and `weaklyIntegral_of_propertyF` are unchanged from baseline `56dd74cd`.

At proof commit `48e72d75`, with `LEAN_NUM_THREADS=4`:

- `scripts/check.sh` passed, auditing 5,258 integrated declarations without
  `sorryAx` or custom axioms, and 5,270 declarations across the project.
- `scripts/audit-target.sh` passed; the target dependency audit reported only
  `propext`, `Classical.choice`, and `Quot.sound`.
- An explicit `#print axioms` was run for all 908 public theorem declarations
  in the changed Lean modules. Each output contained only those three axioms
  or a subset. This includes the unconditional main, closure, and objectwise
  theorems. Existing conjectures are excluded from the audited target imports.

The proof and audit do not assert the existence of a particular external
realization for every abstract field automorphism; the Galois statement applies
to every semilinearly represented conjugate in the existing framework.
