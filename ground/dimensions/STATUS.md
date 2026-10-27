# Dimensions workstream

## Done

- `PropertyF.Ground.Dimensions.extend_complex_automorphism`: every automorphism of a subfield of ℂ extends to ℂ, using a transcendence basis and uniqueness of algebraic closures.
- `PropertyF.Ground.Dimensions.finite_galois_normal_field`: an algebraic complex number belongs to a finite Galois intermediate field given by its normal closure.
- `PropertyF.Ground.Dimensions.dimensionFieldOfIntegral`: constructs all fields of `DimensionField δ` from `IsIntegral ℤ (δ : ℂ)`.

## In progress

- Prove elementary dimension consequences and trace infrastructure while waiting for the shared category interface.

## Dependencies and remaining work

- Fusion: global FP dimension integrality over ℤ. Once obtained it discharges the input to `dimensionFieldOfIntegral`.
- Integrate/fusion: genuine category and semisimplicity interface needed to construct pivotal and spherical structures, intrinsic norms and their ENO properties.
- Remaining: independence/positivity/total positivity of squared norms; categorical global dimension ≥ 1; ENO 8.21/8.22 inequalities and equality case; ENO 8.23 canonical spherical structure; construction of pseudo-unitary conjugate real/positive/bounded dimensions and transport. These are substantial mathematical developments, not completed by the arithmetic construction.

Estimate: the finite-field arithmetic is finished modulo global FP integrality; the category-theoretic dimension program remains substantially open and its duration is currently uncertain.
