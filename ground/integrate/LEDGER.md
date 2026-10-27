# Ground integration ledger

Baseline: 094175c. Frozen target definition: 45da64d. As of 2026-10-27 all old
interfaces below are unconstructed unless explicitly marked otherwise. Exact
field types are in `PropertyF/Axioms.lean` and `PropertyF/Definitions.lean`;
`FORMALIZATION.md` explains their mathematical content. All owners are the
workstreams specified in the coordination board. The target was frozen after
fusion and dimensions review; unresolved mathematical obligations are noted below.

## Target and dependency graph

`target_of_spherical_and_witness` reduces the frozen statement to two
explicit categorical obligations: a spherical pivotal structure with self-dual
simple dimensions, and a centre/rigidity witness for each smaller conjugate. Global FP positivity
is proved from the tensor unit; the numerical contradiction is bundle-free. Global FP
invariance under semilinear braided equivalence is proved by
`Modular.conjugate_globalFPDimension`.

`Ground.TargetStatement` → genuine fusion properties and simple representatives
(fusion); FPdim via spectral radius and independence (fusion); squared norms and
global categorical dimension (dimensions); braided semilinear conjugacy
(modular/integrate); property F on actual braid images (already defined).

A conditional prototype can construct from each ground category:
`FusionData` (fusion) + `GlobalDimensionData` (dimensions) + proofs ground
and old global FP/categorical dimensions agree (fusion, dimensions). Construct
`StandardInputs` (below) or specialize its pieces to the categories actually
needed (integrate). Transport the Galois equivalence and property F (integrate /
modular). The strict final audit rejects the old theorem and its input structures anywhere
in the dependency cone even if their instances are constructed. Refactor or
reprove the conditional argument using ground constructions and helper results
whose types and values avoid those structures, then run the target audit. `GeneratedInputs` and cabling are NOT used by the main target;
they remain obligations for the separate corollary.

The category interface is inhabited by `Example.complexVectorSpaces`, based
on finite-dimensional complex vector spaces. Both global dimensions equal one
and the pseudo-unitary conjugate is constructed; property F for that example
has not yet been established.

Simple representatives are proved complete; both global dimensions are
proved independent of their presentation. FP spectral radii form the unique
positive fusion character, and the intrinsic squared norm is independent of
the scalar and double-dual choices. `Ground.doubleDualIso` is constructed
from Mathlib’s braided swapped pairing and uniqueness of duals. Comparison
of complex-automorphism conjugacy with the paper’s algebraic-closure
formulation remains an explicit review obligation.

## Fields and ownership

| Interface | Field(s) | Owner | Status |
|---|---|---|---|
| `FusionData` | `rank`, `simpleObject`, `simple_is_simple`, `simple_injective`, `unitIndex`, `unit_iso`, `hom_finite`, `decomposition` | fusion | Constructed by `Ground.legacyFusionData` from ground category. |
| `FusionData` | `fpSimple`, `fp_positive`, `fp_unit`, `fp_character` | fusion | Constructed by `Ground.legacyFusionData` using the ground spectral character. |
| `GlobalDimensionData` | `unitScalar`, `doubleDualIso` | dimensions | Constructed by `Ground.legacyGlobalDimensionData`; norm and representative independence proved. |
| `MultiplicityData` | `simpleCount`, `dimension`, `fpDimension`, `multiplicity`, `dimension_bound` | calculus; dimensions for bound | Open: group-representation decomposition and spherical dimension bound. |
| `OverlapModel` | `stage`, `decomposition`, `fpMass_eq` | calculus, fusion | Actual braid-image algebras and unitary Wedderburn blocks constructed; categorical multiplicity and FP mass remain. |
| `OverlapModel` | `left`, `right`, `partialTrace`, `trace_partial`, `partial_left`, `partial_right` | calculus, dimensions | Both strand star maps and iterated partial trace proved on calculus/dimensions branches; overlap recurrence iteration remains. |
| `ThreeStrandModel` | `overlap`, `pair`, `pair_nonzero`, `cSquared`, `a`, `b`, `braid_relation`, `a_unitary`, `b_unitary` | calculus | Actual unitary pair/three-strand blocks, braid relation, nonzero blocks and finite order proved on calculus b0fe84a; full model assembly remains. |
| `ThreeStrandModel` | `leftPair`, `rightPair`, `left_cSquared`, `right_cSquared` | calculus | Actual left/right identity-strand block maps and square-braiding identities proved on calculus b0fe84a; model assembly remains. |
| `ThreeStrandModel` | `pairTrace`, `simplePartial`, `pair_trace_partial`, `thirdPartial`, `trace_third`, `third_left`, `third_right`, `third_bimodule` | calculus, dimensions | Open: spherical trace realization. |
| `ThreeStrandModel` | `finite_order` | calculus | Finite order of the actual represented square proved on calculus b0fe84a; model assembly remains. |
| `ThreeStrandRealization` | `model`, `positive`, `transport`, `retained`, `trace_formula` | calculus; dimensions/modular for transported dimensions and S | Unitary braid blocks with categorical trace weights and integer multiplicities are constructed; transport, partial traces and full overlap bridge remain. |
| `ProductImageWitness` | `subgroup`, `map`, `surjective` | centre | Actual product-functor/retract quotient maps constructed on centre f031e99; dominance onto the generated subcategory remains. |
| `ModularData` | `rank`, `unit`, `dual`, `dimension`, `globalDimension`, `S` | modular, centre | Actual categorical S defined for a chosen pivotal structure; modular centre and remaining data open. |
| `ModularData` | `dimension_ne_zero`, `global_ne_zero`, `global_eq`, `S_symmetric`, `S_unit`, `unit_dimension`, `S_square` | modular | S symmetry, unit column and nonvanishing proved; Verlinde proved on modular a002b9d; S² remains open. |
| `ModularData` | `galoisLabel`, `galois_character` | modular | Constructed from a normalized-column character classification; modular-category realization and classification hypotheses remain. |
| `CenterInputs` | `data`, `object`, `dim`, `dimension_real`, `positive`, `at_least_one`, `conjugate_real` | centre, dimensions, modular | Open: canonical spherical modular centre and dimension properties. |
| `CenterInputs` | `global_square`, `symmetric_integrality`, `generated`, `double_centralizer` | centre | Open: centre dimension, symmetric core and double centralizer. |
| `CenterInputs` | `product_witness` | centre | Subgroup/quotient and retract finite-image transfer are constructed; dominance onto generated centre category remains. |
| `CenterInputs` | `realize` | calculus | Open: construct `ThreeStrandRealization` from categorical finite braid image. |
| `DimensionField` | `field`, `finite`, `galois`, `element`, `element_eq`, `integral`, `extend` | dimensions, fusion for algebraic integrality | Ground spectral global FP integrality is proved; bundle-free normal-field descent is wired by `weaklyIntegral_of_globalFPDimension_fixed`. |
| `PseudoUnitaryInputs` | `conjugateGlobal`, `conjugate_eq`, `conjugate_positive`, `conjugate_le` | dimensions | Open: conjugate categorical dimensions, positivity and bounds. |
| `PseudoUnitaryInputs` | `center`, `arithmetic` | centre, dimensions | Open: package above constructions. |
| `StandardInputs` | `pseudo` | dimensions, centre, calculus, modular | Open: package above constructions for pseudo-unitary categories. |
| `StandardInputs` | `conjugate_labels`, `conjugate_images` | modular, fusion | Braid-image equivalences, ground property-F transport, simple-label equivalence and spectral global FP preservation are proved. |
| `CablingWitness` | `blockCount`, `lengths`, `pureImage`, `finiteIndex`, `cableImage`, `restriction`, `restriction_surjective` | cabling | Finite index and abstract pure-word quotient constructed; categorical cabling map pending. Only used by corollary. |
| `GeneratedInputs` | `cabling`, `category`, `inclusion`, `inclusion_braided`, `inclusion_full`, `inclusion_faithful`, `inclusion_generated`, `generated_essential_image`, `image_equivalence` | cabling | Open; only used by corollary. |
| `GeneratedInputs` | `simple_square_integral`, `strand_inclusion` | cabling, fusion | Bundle-free `Ground.simple_strand_inclusion` now constructed; packaging and square-integrality remain. Only used by corollary. |

The existing `#print axioms` result establishes only kernel axiom cleanliness
for the *conditional* theorem; it says nothing about constructing these fields.

## Integrated snapshot

Latest merged snapshots: fusion 60076b7; dimensions f0dd606; calculus 158456c;
centre f031e99; modular 1d68dcc; cabling fd9b085. The full development build
passed; `ProjectAudit` scans 1,767 integrated declarations, all with only the
standard axioms. This is not a proof of the target.

The final arithmetic reduction is bundle-free: fusion bfbd006 proves target
global FP algebraic integrality, and `weaklyIntegral_of_globalFPDimension_fixed`
combines it with the constructed finite Galois field and automorphism extension.
Global FP conjugacy invariance is proved. Galois fixedness requires the
categorical real-conjugate bounds and centre/rigidity witnesses above.
