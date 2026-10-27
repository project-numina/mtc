# Ground integration ledger

Baseline: 094175c. Target definition: 45da64d. As of 2026-10-27 all old
interfaces below are unconstructed unless explicitly marked otherwise. Exact
field types are in `PropertyF/Axioms.lean` and `PropertyF/Definitions.lean`;
`FORMALIZATION.md` explains their mathematical content. All owners are the
workstreams specified in the coordination board. Statements marked provisional
must be verified before the target is frozen.

## Target and dependency graph

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

Provisional mathematical checks: simple reps exhaust all simple isoclasses;
scalar map ℂ → End(𝟙) is bijective; `invFun` computes its inverse; squared
norms are independent of isomorphism and simple presentation; FP spectral
radii form the unique positive fusion character and are presentation independent;
compare complex-automorphism conjugacy with the paper's algebraic-closure
formulation. `Ground.doubleDualIso` is already constructed from Mathlib's
braided swapped pairing and uniqueness of duals. No choice independence proof
is claimed yet.

## Fields and ownership

| Interface | Field(s) | Owner | Status |
|---|---|---|---|
| `FusionData` | `rank`, `simpleObject`, `simple_is_simple`, `simple_injective`, `unitIndex`, `unit_iso`, `hom_finite`, `decomposition` | fusion | Ground category has finite semisimple property; construction of old bundle pending. |
| `FusionData` | `fpSimple`, `fp_positive`, `fp_unit`, `fp_character` | fusion | Spectral-radius ground definition exists; PF character theorem and bridge pending. |
| `GlobalDimensionData` | `unitScalar`, `doubleDualIso` | dimensions | Ground double-dual is constructed; scalar equivalence and old bundle pending. |
| `MultiplicityData` | `simpleCount`, `dimension`, `fpDimension`, `multiplicity`, `dimension_bound` | calculus; dimensions for bound | Open: group-representation decomposition and spherical dimension bound. |
| `OverlapModel` | `stage`, `decomposition`, `fpMass_eq` | calculus, fusion | Open: endomorphism blocks, decomposition and FP mass. |
| `OverlapModel` | `left`, `right`, `partialTrace`, `trace_partial`, `partial_left`, `partial_right` | calculus, dimensions | Open: compatible finite-group averaging and spherical partial traces. |
| `ThreeStrandModel` | `overlap`, `pair`, `pair_nonzero`, `cSquared`, `a`, `b`, `braid_relation`, `a_unitary`, `b_unitary` | calculus | Open: categorical braid action, finite-image averaging, nonzero blocks. |
| `ThreeStrandModel` | `leftPair`, `rightPair`, `left_cSquared`, `right_cSquared` | calculus | Open: identity-strand algebra embeddings. |
| `ThreeStrandModel` | `pairTrace`, `simplePartial`, `pair_trace_partial`, `thirdPartial`, `trace_third`, `third_left`, `third_right`, `third_bimodule` | calculus, dimensions | Open: spherical trace realization. |
| `ThreeStrandModel` | `finite_order` | calculus | Open: transport finite order from finite actual image. |
| `ThreeStrandRealization` | `model`, `positive`, `transport`, `retained`, `trace_formula` | calculus; dimensions/modular for transported dimensions and S | Open: construct the whole bridge. |
| `ProductImageWitness` | `subgroup`, `map`, `surjective` | centre | Open: dominant product functor and restriction-to-summand diagram. |
| `ModularData` | `rank`, `unit`, `dual`, `dimension`, `globalDimension`, `S` | modular, centre | Open: modular centre and actual S-matrix. |
| `ModularData` | `dimension_ne_zero`, `global_ne_zero`, `global_eq`, `S_symmetric`, `S_unit`, `unit_dimension`, `S_square` | modular | Open: spherical and modular identities. |
| `ModularData` | `galoisLabel`, `galois_character` | modular | Open: normalized-character permutation by Galois action. |
| `CenterInputs` | `data`, `object`, `dim`, `dimension_real`, `positive`, `at_least_one`, `conjugate_real` | centre, dimensions, modular | Open: canonical spherical modular centre and dimension properties. |
| `CenterInputs` | `global_square`, `symmetric_integrality`, `generated`, `double_centralizer` | centre | Open: centre dimension, symmetric core and double centralizer. |
| `CenterInputs` | `product_witness` | centre | Open: construct `ProductImageWitness` for generated labels. |
| `CenterInputs` | `realize` | calculus | Open: construct `ThreeStrandRealization` from categorical finite braid image. |
| `DimensionField` | `field`, `finite`, `galois`, `element`, `element_eq`, `integral`, `extend` | dimensions, fusion for algebraic integrality | Open: normal closure and extension to ℂ. |
| `PseudoUnitaryInputs` | `conjugateGlobal`, `conjugate_eq`, `conjugate_positive`, `conjugate_le` | dimensions | Open: conjugate categorical dimensions, positivity and bounds. |
| `PseudoUnitaryInputs` | `center`, `arithmetic` | centre, dimensions | Open: package above constructions. |
| `StandardInputs` | `pseudo` | dimensions, centre, calculus, modular | Open: package above constructions for pseudo-unitary categories. |
| `StandardInputs` | `conjugate_labels`, `conjugate_images` | modular, fusion | Open: simple labels/FP character and actual braid-image equivalences. |
| `CablingWitness` | `blockCount`, `lengths`, `pureImage`, `finiteIndex`, `cableImage`, `restriction`, `restriction_surjective` | cabling | Open; only used by corollary. |
| `GeneratedInputs` | `cabling`, `category`, `inclusion`, `inclusion_braided`, `inclusion_full`, `inclusion_faithful`, `inclusion_generated`, `generated_essential_image`, `image_equivalence` | cabling | Open; only used by corollary. |
| `GeneratedInputs` | `simple_square_integral`, `strand_inclusion` | cabling, fusion | Open; only used by corollary. |

The existing `#print axioms` result establishes only kernel axiom cleanliness
for the *conditional* theorem; it says nothing about constructing these fields.
