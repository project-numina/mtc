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
- `Ground.integer_matrix_spectralRadius_sq_isIntegral`,
  `Ground.fpSimple_isIntegral`, and `Ground.globalFPDimension_isIntegral`:
  the target's spectral-radius simple dimensions and global dimension are
  algebraic integers, without assuming a positive character or old bundles.
- `Ground.fusionMatrix_unit`, `Ground.fpSimple_unit`, and
  `Ground.one_le_globalFPDimension`: the spectral-radius definition is
  normalized at the unit and the global dimension is at least one.
- `Ground.split_from_simple`: any nonzero map out of a simple object splits,
  using the genuine finite semisimplicity property.
- `Ground.unit_retract_leftDual_tensor`: the tensor unit is a retract of
  `ᘁX ⊗ X` for simple `X`, supplying the cabling strand-inclusion input.
- `Ground.simples_simple`, `simples_injective`, `simples_decompose`,
  `exists_simple_iso`, `exists_unit_iso`, and `finrank_simples_hom`: the
  target's representatives enumerate all simple objects, including the unit,
  and satisfy Schur's Hom formula without using old fusion structures.
- `Ground.homBiproductLinearEquiv`, `finrank_hom_biproduct`,
  `finrank_simple_of_decomposition`, `exists_canonical_decomposition`:
  Hom-space dimensions compute decomposition multiplicities, and every object
  decomposes with those canonical multiplicities.
- `Ground.tensor_multiplicity`, `fusionCoeff_unit`, `fusionCoeff_comm`, and
  `fusionCoeff_assoc`: tensor product acts on multiplicities through the actual
  fusion coefficients, which satisfy the unit, commutativity and associativity
  laws for the genuine target category.
- `Ground.tensorRightHomLinearEquiv`, `finrank_frobenius_reciprocity`, and
  `fusionCoeff_reciprocity`: rigidity gives complex-linear Hom equivalences and
  Frobenius reciprocity with the actual left dual object.
- `Ground.finrank_end_leftDual`, `simple_of_finrank_end_eq_one`,
  `simple_leftDual`, `dualIndex`, `dualIndex_involutive`, `dualEquiv`, and
  `fusionCoeff_reciprocity_labels`: the actual dual of each simple is simple,
  duality gives an involutive permutation of labels, and the usual
  Frobenius reciprocity identity follows.
- `Ground.totalFusionMatrix_symmetric` and `totalFusionMatrix_pos`: the sum of
  the real fusion matrices is symmetric and strictly positive. Positivity uses
  cabling's `tensorLeft_faithful_of_unit_retract` (merged commit 288c894).
- `Ground.positive_matrix_eigenspace_unique`: any eigenspace containing a
  strictly positive eigenvector of a positive real matrix is one-dimensional.
- `Ground.positive_symmetric_matrix_has_positive_eigenvector`: every strictly
  positive symmetric real matrix has a strictly positive eigenvector, proved by
  maximizing its quadratic form on a sphere and applying Mathlib's symmetric
  operator spectral theory.
- `Ground.characterMatrix_commute`, `exists_positive_common_eigenvector`, and
  `exists_positive_character`: the actual fusion rules admit a positive
  normalized character, constructed from the genuine target category.

These results use the existing `FusionData`; they do not construct its positive
character or discharge the `FusionData` hypothesis.

## In progress

Construction of fusion rules and the positive character from a genuine finite
semisimple rigid category. Integration has been asked for its target interface.
Integration independently proved the unit-scalar identification in its own
`PropertyF/Ground/Integrate/UnitScalar.lean`; our duplicate was removed to avoid
declaration conflicts.

## Blocked / outstanding

Mathlib has categorical Schur's lemma but a source search found no general
Perron–Frobenius theorem for positive matrices. The positive fusion character is
now constructed; uniqueness and agreement with the target's spectral-radius
dimensions remain to be established.

Construction of `FusionData`, tensor/dual/inclusion invariance, agreement of
spectral radii with the positive character, and the centre dimension comparison
remain. The project-scale remaining effort is substantial; no credible
completion-time estimate is yet available.

Integration requires the target dependency cone to avoid the old hypothesis
bundles entirely. The above results currently use `FusionData` and must be
generalized to the genuine category/character interface before they can be used
directly in the final proof.
