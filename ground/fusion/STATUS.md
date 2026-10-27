# Fusion workstream status

## Done

- `FusionData.finrank_simple_hom`: Schur's lemma gives the Kronecker-delta
  Hom dimensions of the existing simple representatives.
- `FusionData.simple_endomorphism_scalar`: endomorphisms of each representative
  are complex scalars.
- `FusionData.fpDimension_simple`: the existing object FP-dimension expression
  agrees with the specified character on each representative.
- `FusionData.fpSimple_isIntegral`, `fpDimension_isIntegral`, and
  `globalFPDimension_isIntegral`: the fusion equations give an integer matrix
  having the positive character as eigenvector, so its values and their finite
  sums and products are algebraic integers.
- `Ground.integer_matrix_eigenvalue_isIntegral`: a reusable matrix theorem
  with no dependency on the old fusion or numerical hypothesis structures.
- `Ground.split_from_simple`: any nonzero map out of a simple object splits,
  using the genuine finite semisimplicity property.
- `Ground.unit_retract_leftDual_tensor`: the tensor unit is a retract of
  `ᘁX ⊗ X` for simple `X`, supplying the cabling strand-inclusion input.
- `Ground.simples_simple`, `simples_injective`, `simples_decompose`,
  `exists_simple_iso`, `exists_unit_iso`, and `finrank_simples_hom`: the
  target's representatives enumerate all simple objects, including the unit,
  and satisfy Schur's Hom formula without using old fusion structures.

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

Construction of `FusionData`, tensor/dual/inclusion invariance, integrality for
the target spectral-radius definition, and the centre dimension comparison
remain. The project-scale remaining effort is substantial; no credible
completion-time estimate is yet available.

Integration requires the target dependency cone to avoid the old hypothesis
bundles entirely. The above results currently use `FusionData` and must be
generalized to the genuine category/character interface before they can be used
directly in the final proof.
