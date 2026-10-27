# Dimensions workstream

## Done

- `PropertyF.Ground.Dimensions.extend_complex_automorphism`: every automorphism of a subfield of ℂ extends to ℂ, using a transcendence basis and uniqueness of algebraic closures.
- `PropertyF.Ground.Dimensions.finite_galois_normal_field`: an algebraic complex number belongs to a finite Galois intermediate field given by its normal closure.
- `PropertyF.Ground.Dimensions.squaredNorm_independent`: intrinsic squared norm is independent of the double-dual isomorphism on each simple; `globalDimensionData_independent` also handles the unit scalar algebra equivalence.
- `PropertyF.Ground.Dimensions.dimensionFieldOfIntegral`: constructs all fields of `DimensionField δ` from `IsIntegral ℤ (δ : ℂ)`.

- `target_squaredNorm_iso` proves representative invariance without assuming a spherical structure; `quantumTraces_iso` transports both traces along compatible double-dual maps.
- `target_squaredNorm_choice_independent`, `target_squaredNorm_eq_dimension_sq`, and `target_globalDimension_eq_sum_squares` apply the choice independence and spherical identities to the genuine-category target, without old hypothesis bundles.
- `PivotalStructure`, `PivotalStructure.rightTrace`, `leftTrace`, `IsSpherical` use actual duality maps; `rightTrace_id`, `leftTrace_id`, and `spherical_norm_eq_dimension_sq` connect them to the existing intrinsic norm. Existence and trace laws remain open.

- `target_globalDimension_real`, `target_globalDimension_le_of_simple_bounds`, `global_sum_squares_positive`, `global_sum_squares_one_le`, and `global_sum_squares_eq_iff` reduce the global realness, inequality, and positivity assertions to explicit simple-dimension hypotheses; those hypotheses remain unproved.

## In progress

- `PivotalStructure.rightTrace_add`, `rightTrace_smul`, `leftTrace_add`, and `leftTrace_smul` establish linearity. `rightTrace_cyclic`, `leftTrace_cyclic_of_spherical`, and `rightTrace_id_iso` also hold. Multiplicativity and semilinear trace transport remain open.

- Prove elementary dimension consequences and trace infrastructure while waiting for the shared category interface.

## Dependencies and remaining work

- Fusion: global FP dimension integrality over ℤ. Once obtained it discharges the input to `dimensionFieldOfIntegral`.
- Integrate/fusion: genuine category and semisimplicity interface needed to construct pivotal and spherical structures, intrinsic norms and their ENO properties.
- Remaining: positivity/total positivity of squared norms, and independence of the global sum under reindexing simple representatives; categorical global dimension ≥ 1; ENO 8.21/8.22 inequalities and equality case; ENO 8.23 canonical spherical structure; construction of pseudo-unitary conjugate real/positive/bounded dimensions and transport. These are substantial mathematical developments, not completed by the arithmetic construction.

Estimate: the finite-field arithmetic is finished modulo global FP integrality; the category-theoretic dimension program remains substantially open and its duration is currently uncertain.
