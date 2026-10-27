# Dimensions workstream

## Done

- `PropertyF.Ground.Dimensions.extend_complex_automorphism`: every automorphism of a subfield of ℂ extends to ℂ, using a transcendence basis and uniqueness of algebraic closures.
- `PropertyF.Ground.Dimensions.finite_galois_normal_field`: an algebraic complex number belongs to a finite Galois intermediate field given by its normal closure.
- `PropertyF.Ground.Dimensions.squaredNorm_independent`: intrinsic squared norm is independent of the double-dual isomorphism on each simple; `globalDimensionData_independent` also handles the unit scalar algebra equivalence.
- `dimensionFieldOfGround` constructs `DimensionField` for the target spectral-radius global FP dimension, using fusion’s bundle-free integrality theorem. Integrate has also proved the bundle-free fixed-field arithmetic step.
- `dimensionFieldOfFusionData` constructs the entire old `DimensionField` from fusion’s proven character integrality; the old `FusionData` remains an assumption in this compatibility theorem.
- `PropertyF.Ground.Dimensions.dimensionFieldOfIntegral`: constructs all fields of `DimensionField δ` from `IsIntegral ℤ (δ : ℂ)`.

- `target_globalDimension_independent_simples` proves the target global dimension is unchanged by any complete pairwise nonisomorphic finite simple list.
- `target_squaredNorm_iso` proves representative invariance without assuming a spherical structure; `quantumTraces_iso` transports both traces along compatible double-dual maps.
- `target_squaredNorm_choice_independent`, `target_squaredNorm_eq_dimension_sq`, and `target_globalDimension_eq_sum_squares` apply the choice independence and spherical identities to the genuine-category target, without old hypothesis bundles.
- `PivotalStructure`, `PivotalStructure.rightTrace`, `leftTrace`, `IsSpherical` use actual duality maps; `rightTrace_id`, `leftTrace_id`, and `spherical_norm_eq_dimension_sq` connect them to the existing intrinsic norm. Existence and trace laws remain open.

- `target_globalDimension_real`, `target_globalDimension_le_of_simple_bounds`, `global_sum_squares_positive`, `global_sum_squares_one_le`, and `global_sum_squares_eq_iff` reduce the global realness, inequality, and positivity assertions to explicit simple-dimension hypotheses; those hypotheses remain unproved.

- `rightTrace_biproduct` proves the trace of an endomorphism on a finite biproduct is the sum of diagonal block traces; `rightDimension_biproduct` gives additivity of dimension, and `rightTrace_biproduct_simple` uses Schur to derive dimension-weighted scalar diagonal blocks.

- `target_squaredNorm_rightDual` proves intrinsic norm invariance under duality without a pivotal structure. `spherical_pivotalDimension_rightDual_sq` proves equality of squared dimensions, with the sign still unresolved.
- `rightQuantumTrace_simple_ne_zero`, `leftQuantumTrace_simple_ne_zero`, and `target_squaredNorm_ne_zero` establish nonvanishing for every simple without a pivotal or spherical structure.
- `pivotalDimension_simple_ne_zero` and `spherical_squaredNorm_ne_zero` reuse modular’s genuine categorical nonvanishing theorem. `spherical_squaredNorm_totallyPositive_of_dual` and `pseudoUnitary_galois_fp_bounds_of_dual` establish total positivity and the conjugate positivity/upper bound from the explicit remaining dual-dimension identity.
- `globalDimension_real_one_le_of_spherical` proves the target global dimension is at least one given a spherical structure with real simple dimensions; existence and reality are not yet proved.
- `pseudoUnitary_iff_simple_saturation` establishes the global equality characterization given a spherical structure and real simple dimensions.
- `character_value_isIntegral`, `pivotalDimension_isIntegral`, `spherical_squaredNorm_isIntegral`, and `spherical_globalDimension_isIntegral` prove algebraic integrality of pivotal dimensions and, when spherical structures exist, intrinsic squared norms and global dimension.
- `pivotalDimension_decomposition` proves the Hom-multiplicity formula; `pivotalDimension_character` and `galois_pivotalDimension_norm_le_fpSimple` establish the pivotal fusion character and Galois FP bound with no extra trace-law assumptions.
- `character_norm_le_fpSimple` and `galois_character_norm_le_fpSimple` prove the spectral-radius bound for any nonzero complex fusion character and every complex field conjugate. The character equations now hold for all pivotal structures.

- `rightTrace_unit` and `pivotalDimension_unit` prove the pivotal trace and dimension of the tensor unit equal one, for any pivotal structure.
- `coevaluation_rightDualIso`, `rightDualIso_evaluation`, and their inverse variants prove that Mathlib’s canonical comparison of right duals transports the actual duality maps.

- `isSpherical_iff_simple_dimensions` reduces sphericality on all endomorphisms to equality of left and right dimensions on the finite list of simples.
- `rightTrace_tensor_pairing` rewrites the trace using the tensor-product dual pairing; `rightTrace_partialTrace` proves compatibility of partial and total pivotal traces without extra assumptions.

- `pivotalTrace_tensor`, `rightPartialTrace_tensor`, and `pivotalDimension_tensor` prove tensor multiplicativity and remove the multiplicativity premises from the spectral bound and pseudo-unitarity characterization.

## In progress

- `PivotalStructure.rightTrace_add`, `rightTrace_smul`, `leftTrace_add`, and `leftTrace_smul` establish linearity. `rightTrace_cyclic`, `leftTrace_cyclic`, and `rightTrace_id_iso` also hold for any pivotal structure. `pivotalTrace_tensor` proves multiplicativity; semilinear trace transport remains open.

- Prove elementary dimension consequences and trace infrastructure while waiting for the shared category interface.

## Dependencies and remaining work

- Fusion: positive-character theory and spectral-radius agreement, needed for ENO dimension bounds and canonical spherical construction. Target spectral FP integrality is proved.
- Category interfaces, simple representatives, unit scalars and target FP integrality are available. Remaining categorical dependencies are the construction of canonical spherical structure and the identity of spherical dimensions on dual objects.
- Remaining: positivity/total positivity of squared norms; categorical global dimension ≥ 1; ENO 8.21/8.22 inequalities and equality case; ENO 8.23 canonical spherical structure; construction of pseudo-unitary conjugate real/positive/bounded dimensions and transport. These are substantial mathematical developments, not completed by the arithmetic construction.

Estimate: the finite-field arithmetic is finished and the categorical integrality is established for spherical structures; the category-theoretic dimension program remains substantially open and its duration is currently uncertain.
