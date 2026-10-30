# Known results to formalize

These results are established in the literature but not yet proved in this library. They are
not conjectures, so they are kept out of `Conjectures/`. Their Lean statements were written and
checked during seeding and are preserved in commit `5966c406` at the paths listed; restore a
statement from there when starting its proof, and add the finished proof under `MTC/`.

| Topic | Result | Statement | Source | Lean statement (commit 5966c406) |
| --- | --- | --- | --- | --- |
| Exotic | `b11_not_weaklyIntegral` | # The rank-11 Atlas example is not weakly integral | The Anyon Atlas, arXiv:2610.25439, Section 5 and equations (5.2)–(5.3); exact corollary verified by scripts/propf/exotic_b11.py. | `Conjectures/Exotic/B11WeakIntegrality.lean` |
| Fusion | `dual_dimensions` | FP dimensions of dual simple objects | Etingof–Nikshych–Ostrik, arXiv:math/0203060, Section 8. | `Conjectures/Fusion/DualDimensions.lean` |
| Fusion | `fusion_dimension_character` | FP dimension is a fusion-ring character | Etingof–Nikshych–Ostrik, arXiv:math/0203060, Theorem 8.6. | `Conjectures/Fusion/FusionDimensionCharacter.lean` |
| Fusion | `globalDimension_algebraicInteger` | Global FP dimension is an algebraic integer | Drinfeld–Gelaki–Nikshych–Ostrik, arXiv:0906.0620, Section 2.4.1. | `Conjectures/Fusion/GlobalDimensionAlgebraicInteger.lean` |
| Fusion | `invertible_iff_dimension_one` | Invertible simples and dimension one | Bruillard–Ng–Rowell–Wang, arXiv:1310.7050, Remark 2.2. | `Conjectures/Fusion/InvertibleDimension.lean` |
| Fusion | `oddDimension_integral` | Odd weak dimension implies integrality | Drinfeld–Gelaki–Nikshych–Ostrik, arXiv:0906.0620, Corollary 2.22. | `Conjectures/Fusion/OddDimensionIntegral.lean` |
| Fusion | `simpleDimension_algebraicInteger` | Simple FP dimensions are algebraic integers | Drinfeld–Gelaki–Nikshych–Ostrik, arXiv:0906.0620, Section 2.4.1; | `Conjectures/Fusion/SimpleDimensionAlgebraicInteger.lean` |
| Fusion | `simpleDimension_lowerBound` | Lower bound on simple FP dimensions | Drinfeld–Gelaki–Nikshych–Ostrik, arXiv:0906.0620, Section 2.4.1. | `Conjectures/Fusion/SimpleDimensionLowerBound.lean` |
| Fusion | `weaklyIntegral_pseudoUnitary` | Weak integrality implies pseudo-unitarity | Drinfeld–Gelaki–Nikshych–Ostrik, arXiv:0906.0620, Proposition 2.18(i). | `Conjectures/Fusion/WeaklyIntegralPseudoUnitary.lean` |
| Fusion | `weaklyIntegral_squares` | Squared dimensions of a weakly integral fusion category | Drinfeld–Gelaki–Nikshych–Ostrik, arXiv:0906.0620, Proposition 2.18(ii). | `Conjectures/Fusion/WeaklyIntegralSquares.lean` |
| Galois | `globalFPDimension_dNumber` | Galois invariance of the global FP dimension ideal | Ostrik, arXiv:0810.3242, Corollary 1.3. | `Conjectures/Galois/GlobalFPDimension.lean` |
| Galois | `squaredNorm_dNumber` | Galois divisibility of simple squared norms | Ostrik, arXiv:0810.3242, Theorem 1.8. | `Conjectures/Galois/SquaredNorm.lean` |
| RankFiniteness | `dimensionValuesFinite` | Rank-finiteness for global FP-dimension values | Bruillard–Ng–Rowell–Wang, arXiv:1310.7050, Theorem 3.1 and Corollary 3.13. | `Conjectures/RankFiniteness/DimensionValues.lean` |
| RankFiniteness | `rankFiniteness` | Rank-finiteness for modular categories | Bruillard–Ng–Rowell–Wang, arXiv:1310.7050, Theorem 3.1. | `Conjectures/RankFiniteness/RankFiniteness.lean` |
| Realizability | `pointedFusionRules` | Realization of pointed fusion rules | Etingof, Gelaki, Nikshych and Ostrik, Tensor Categories, Sections 2.6 and 8.4, https://math.mit.edu/~etingof/egnobookfinal.pdf. | `Conjectures/Realizability/PointedFusionRules.lean` |
