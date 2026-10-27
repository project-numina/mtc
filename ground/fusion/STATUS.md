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
- `Ground.split_to_simple`, `simple_projective`, `simple_injective`,
  `object_projective`, `object_injective`, `epi_splits`, and `mono_splits`:
  every object is projective and injective, and all epimorphisms and
  monomorphisms split.
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
- `Ground.positive_character_unique`, `fpCharacter`, `fpCharacter_pos`,
  `fpCharacter_unit`, and `fpCharacter_mul`: that character is unique and is
  available as a constructed function with its fundamental laws.
- `Ground.fpSimple_eq_fpCharacter`, `fpSimple_pos`, and `fpSimple_mul`: the
  target's spectral-radius dimensions are exactly that positive character.
  This uses `Dimensions.character_norm_le_fpSimple` from dimensions commit
  e5a83b8 and `complex_eigenvalue_le_positive_eigenvalue` for the reverse bound.
- `Ground.fusionMatrix_dual`, `fpSimple_dual`, and `one_le_fpSimple`: simple
  FP dimensions are invariant under duals and at least one.
- `Ground.fusionData`, `fusionData_globalFPDimension`: every field of the
  earlier `FusionData` is constructed from the genuine target category; this
  compatibility bridge is separate from the strict target dependency cone.
- `Ground.fpDimension` and its `simple`, `iso`, `unit`, `nonneg`, `isIntegral`,
  and `tensor` theorems, plus `one_le_fpDimension`: object FP dimension is
  constructed from Hom multiplicities, tensor-multiplicative, integral over ℤ,
  and at least one on nonzero objects.
- `Ground.fpDimension_biproduct`, `fpDimension_functor_decomposition`, and
  `fpDimension_functor`: finite sums are additive, and every faithful additive
  strong monoidal functor preserves FP dimensions of all objects.
- `Ground.dual_multiplicity`, `fpDimension_leftDual`, and
  `fpDimension_rightDual`: FP dimensions of arbitrary objects are invariant
  under either dual.

The legacy `FusionData` results are separate from the bundle-free ground results.

## In progress

Investigating the adjoint-component integrality argument and its categorical
construction, in coordination with cabling.

## Blocked / outstanding

Mathlib has categorical Schur's lemma but a source search found no general
Perron–Frobenius theorem for positive matrices. Existence, uniqueness and
agreement of the target dimensions with the positive character are proved.

The centre dimension comparison and fusion-subcategory dimension identities
remain. Integration proved representative independence and modular proved
conjugacy invariance; inclusion invariance is now proved above. The project-scale
remaining effort is substantial; no credible completion-time estimate is yet
available.

The ground constructions and functor theorem avoid old hypothesis bundles.
The separate compatibility bridge constructs the old `FusionData`.
