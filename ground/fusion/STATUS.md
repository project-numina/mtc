# Fusion workstream status

## Done

- `FusionData.finrank_simple_hom`: Schur's lemma gives the Kronecker-delta
  Hom dimensions of the existing simple representatives.
- `FusionData.simple_endomorphism_scalar`: endomorphisms of each representative
  are complex scalars.
- `FusionData.fpDimension_simple`: the existing object FP-dimension expression
  agrees with the specified character on each representative.

These results use the existing `FusionData`; they do not construct its positive
character or discharge the `FusionData` hypothesis.

## In progress

Construction of fusion rules and the positive character from a genuine finite
semisimple rigid category. Integration has been asked for its target interface.

## Blocked / outstanding

Mathlib has categorical Schur's lemma but a source search found no general
Perron–Frobenius theorem for positive matrices. A constructive proof of a
positive eigenvector and uniqueness, or an alternative elementary argument,
is needed. The categorical bridge from biproduct decompositions to fusion-ring
associativity and rigidity also remains to be developed.

Every field of `FusionData`, plus tensor/dual/inclusion invariance, integrality,
and the centre dimension comparison, remains to be constructed from the target
category definition. The project-scale remaining effort is substantial; no
credible completion-time estimate is yet available.
