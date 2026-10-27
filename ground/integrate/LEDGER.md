# Ground integration ledger

Baseline: 094175c. Frozen target definition: 45da64d. As of 2026-10-27 all old
interfaces below are unconstructed unless explicitly marked otherwise. Exact
field types are in `PropertyF/Axioms.lean` and `PropertyF/Definitions.lean`;
`FORMALIZATION.md` explains their mathematical content. All owners are the
workstreams specified in the coordination board. The target was frozen after
fusion and dimensions review; unresolved mathematical obligations are noted below.

## Target and dependency graph

`target_of_actual_center` states the remaining assumptions directly on
Mathlib’s Drinfeld centre, at object universe `max u v`; one construction
serves all Galois automorphisms. `Integrate.center_forget_fpDimension` applies
once the centre rigid and fusion instances are constructed.
`Integrate.dualCrossingIso` constructs a unit-normalized natural candidate
for dual centre objects; its tensor law and centrality of evaluation and
coevaluation remain unproved.
`target_of_center_product_retracts` explicitly transfers property F from
actual product retracts through a faithful braided functor into the centre.
The remaining categorical assumptions are listed in
`CenterProductBridge.lean`; unconditional full-centre product dominance is
false and is not assumed. `target_of_modular_center` reduces the frozen statement to an actual positive
spherical modular centre, its global FP-square formula, and finite images for
the Galois-unit-column object. `twistedOverlapTrace_proved` and
`galois_rigidity` discharge the braid-calculus premises unconditionally.
`target_of_canonical_spherical_center_and_overlap` derives that rigidity from
the named actual scalar-twisted overlap recurrence, `TwistedOverlapTrace`.
`target_of_center_and_overlap` needs no spherical assumption on the original
category: `positive_bounded_conjugates_of_fp` proves the conjugate bounds
directly from its self-dual FP fusion character. Its centre premise still
requires a positive spherical structure on the constructed modular centre. Global FP positivity
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
and the pseudo-unitary conjugate is constructed. `Example.propertyF` proves
finite braid images by a tensor-product-basis action, and
`Example.target_hypotheses_inhabited` establishes the full target hypotheses
simultaneously.

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
| `MultiplicityData` | `simpleCount`, `dimension`, `fpDimension`, `multiplicity`, `dimension_bound` | calculus; dimensions for bound | Actual unitary group-representation blocks, multiplicities, and trace weights are constructed; the sharp bound remains dependent on categorical overlap coherence. |
| `OverlapModel` | `stage`, `decomposition`, `fpMass_eq` | calculus, fusion | Actual braid-image algebras, unitary blocks, categorical multiplicities and ordinary FP mass bound constructed; the all-strand actual overlap trace recurrence is now proved. |
| `OverlapModel` | `left`, `right`, `partialTrace`, `trace_partial`, `partial_left`, `partial_right` | calculus, dimensions | Both strand star maps and iterated partial trace proved on calculus/dimensions branches; the actual overlap recurrence is now proved. |
| `ThreeStrandModel` | `overlap`, `pair`, `pair_nonzero`, `cSquared`, `a`, `b`, `braid_relation`, `a_unitary`, `b_unitary` | calculus | Actual unitary pair/three-strand blocks, braid relation, nonzero blocks and finite order proved on calculus b0fe84a; full model assembly remains. |
| `ThreeStrandModel` | `leftPair`, `rightPair`, `left_cSquared`, `right_cSquared` | calculus | Actual left/right identity-strand block maps and square-braiding identities proved on calculus b0fe84a; model assembly remains. |
| `ThreeStrandModel` | `pairTrace`, `simplePartial`, `pair_trace_partial`, `thirdPartial`, `trace_third`, `third_left`, `third_right`, `third_bimodule` | calculus, dimensions | Open: spherical trace realization. |
| `ThreeStrandModel` | `finite_order` | calculus | Finite order of the actual represented square proved on calculus b0fe84a; model assembly remains. |
| `ThreeStrandRealization` | `model`, `positive`, `transport`, `retained`, `trace_formula` | calculus; dimensions/modular for transported dimensions and S | Unitary braid blocks and trace weights are constructed; arbitrary scalar-twisted categories, pivotal structures and dimensions are now transported. The full actual overlap recurrence and resulting rigidity are proved; legacy packaging is unnecessary. |
| `ProductImageWitness` | `subgroup`, `map`, `surjective` | centre | Actual product-functor/retract quotient maps and the equality of product retracts with the generated tensor/sum/retract closure are constructed; double-centralizer membership remains. |
| `ModularData` | `rank`, `unit`, `dual`, `dimension`, `globalDimension`, `S` | modular, centre | Actual categorical S defined for a chosen pivotal structure; modular centre and remaining data open. |
| `ModularData` | `dimension_ne_zero`, `global_ne_zero`, `global_eq`, `S_symmetric`, `S_unit`, `unit_dimension`, `S_square` | modular | All legacy fields constructed from an actual spherical category with real dimensions and invertible S; centre realization and S invertibility remain. |
| `ModularData` | `galoisLabel`, `galois_character` | modular | Constructed for a spherical category with real dimensions and invertible categorical S; the centre realization remains. |
| `CenterInputs` | `data`, `object`, `dim`, `dimension_real`, `positive`, `at_least_one`, `conjugate_real` | centre, dimensions, modular | Open: canonical spherical modular centre and dimension properties. |
| `CenterInputs` | `global_square`, `symmetric_integrality`, `generated`, `double_centralizer` | centre | Open: centre dimension, symmetric core and double centralizer. |
| `CenterInputs` | `product_witness` | centre | Subgroup/quotient and retract finite-image transfer and generated closure identification are constructed; double-centralizer membership remains. |
| `CenterInputs` | `realize` | calculus | The bundle-free `galois_rigidity` is constructed from the actual finite braid image; legacy packaging is unnecessary. |
| `DimensionField` | `field`, `finite`, `galois`, `element`, `element_eq`, `integral`, `extend` | dimensions, fusion for algebraic integrality | Ground spectral global FP integrality is proved; bundle-free normal-field descent is wired by `weaklyIntegral_of_globalFPDimension_fixed`. |
| `PseudoUnitaryInputs` | `conjugateGlobal`, `conjugate_eq`, `conjugate_positive`, `conjugate_le` | dimensions | Open: conjugate categorical dimensions, positivity and bounds. |
| `PseudoUnitaryInputs` | `center`, `arithmetic` | centre, dimensions | Open: package above constructions. |
| `StandardInputs` | `pseudo` | dimensions, centre, calculus, modular | Open: package above constructions for pseudo-unitary categories. |
| `StandardInputs` | `conjugate_labels`, `conjugate_images` | modular, fusion | Braid-image equivalences, ground property-F transport, simple-label equivalence and spectral global FP preservation are proved. |
| `CablingWitness` | `blockCount`, `lengths`, `pureImage`, `finiteIndex`, `cableImage`, `restriction`, `restriction_surjective` | cabling | Finite index and abstract pure-word quotient constructed; categorical cabling map constructed by `cablingWitness_generated`. Only used by corollary. |
| `GeneratedInputs` | `cabling`, `category`, `inclusion`, `inclusion_braided`, `inclusion_full`, `inclusion_faithful`, `inclusion_generated`, `generated_essential_image`, `image_equivalence` | cabling, fusion | Ground generated fusion category, inclusion, image equivalence and essential image constructed; pure-block cabling membership and `generatedInputsOfGround` are constructed. Only used by corollary. |
| `GeneratedInputs` | `simple_square_integral`, `strand_inclusion` | cabling, fusion | Both bundle-free `Ground.simple_strand_inclusion` and `Ground.generated_simple_square_integer` are proved; legacy packaging remains. Only used by corollary. |

The existing `#print axioms` result establishes only kernel axiom cleanliness
for the *conditional* theorem; it says nothing about constructing these fields.

## Integrated snapshot

Latest merged snapshots: fusion 1bd2903; dimensions 5646fbb; calculus 80b024f;
centre 212e726; modular 0e4940c; cabling eef095b. The full development build
passed. After expanding the audit imports to include the newly merged modules,
`ProjectAudit` scans 3,569 integrated public and private declarations, all with only the
standard axioms. The strict target audit correctly fails because `Ground.target`
is absent. This is not a proof of the target.

`ScalarTwist.category` and `ScalarTwist.conjugate` construct every arbitrary
complex Galois conjugate; `ScalarTwist.pivotal`, `spherical`,
`pivotalDimension_twist`, `objectPropertyF_twist`, and `labels` establish the
corresponding pivotal dimension and finite-image transport. The intrinsic
squared norms and global dimension transform by the automorphism, while FP
global dimension is preserved. The actual all-strand overlap identity and three-strand rigidity are proved;
centre fusion, its positive spherical structure, and centralizers remain open.

The final arithmetic reduction is bundle-free: fusion bfbd006 proves target
global FP algebraic integrality, and `weaklyIntegral_of_globalFPDimension_fixed`
combines it with the constructed finite Galois field and automorphism extension.
Global FP conjugacy invariance is proved. Galois fixedness requires the
centre/rigidity witnesses above; the real-conjugate bounds are unconditional.

## Round 2 shorter-route assessment

`weaklyIntegral_of_positive_modular_propertyF` proves weak integrality directly
in a positive spherical, non-degenerate category with property F. It avoids
all centre construction and centralizer obligations in that special case.
The proof uses only the selected Galois-unit column, rigidity and the global
dimension identity, but its existence uses invertibility of the full S-matrix.
`categoricalS_det_eq_zero_of_transparent_column` shows that any non-unit simple
with the transparent column forces S to be singular; in particular a nontrivial
symmetric core blocks a direct application to the generated subcategory. No
construction of a smaller modular extension or general replacement for the
column identity has been proved.

Dimensions 5646fbb gives canonical spherical existence conditional on the
fourth-dual tensor equation on simple pairs and the Frobenius defect equation;
these equations remain unproved. Cabling 3ddf985 completes its separate
cabling and generated-category interfaces. The actual centre hCenter premise
and the frozen target remain open.

## Round 2 centre interfaces integrated

- Centre `fusionOfFiniteSemisimple` constructs the ground fusion property from
  centre rigidity and finite semisimplicity; Hom finiteness and the simple unit
  are proved. `rigidOfMateCoherence` constructs rigidity conditional on the
  normalized dual half-braiding tensor law and centrality of the two duality
  maps; those three identities are unproved.
- Fusion `globalFPDimension_square_of_adjunction` derives the FP-square from a
  right adjoint of centre forgetful with its underlying induction-sum formula,
  assuming centre rigidity/fusion. The adjoint and formula are unconstructed.
  Modular's categorical-square reduction additionally needs a positive
  spherical structure on the centre.
- Cabling `productRetract_iff_tensorClosure` identifies the actual generated
  tensor/sum/retract closure with product retracts. Integration's
  `target_of_actual_center_generated` wires that theorem into the target
  reduction. The double-centralizer S-test into this closure is still open.
- Calculus proves common-centralizer self-centrality and reduces integral
  dimensions to actual exterior-object trace identities. Construction and
  trace formulas of the alternating projectors remain open.

## Round 3 integrated snapshot

Merged fusion `ca79865`, dimensions `4af7956`, centre `6d26130`, modular
`ee9ee20`, calculus `1870108`, and cabling `63f901e`. In particular the
actual induction functor and forgetful adjunction are proved, as are centre
finite length, finitely many simple representatives, and enough injectives;
general centre semisimplicity and rigidity remain unproved. Fusion's actual
adjunction proves the FP-square once those instances exist.

`center_globalDimension_square_of_actual_induction` and
`target_of_center_image_monodromy_no_square` combine the actual adjunction,
FP-valued centre sphere and cabling's numerical double-centralizer argument.
They remove global-square as an independent centre premise. Remaining premises:
actual centre rigidity/fusion, FP-valued sphericality, invertible categorical
S, integral dimensions on the actual symmetric core, and finite-order mixed
monodromy for simple canonical-image retracts against labels satisfying their
numerical S-test. The numerical fusion-subcategory double-centralizer itself
is proved; identifying the numerical centralizer with the actual core remains
conditional on that finite-order step. The numerical support proof does not
establish core integrality. These are conditional reductions, not the target.

The rank-one actual centre is fully rigid, fusion, positive spherical and
modular, with the dimension-square identity. General pivotal existence for
fusion categories remains open; pseudo-unitary spherical existence has not
been derived here. `positive_spherical_of_pivotal_pseudoUnitary` proves it if
an actual pivotal structure is supplied, so it cannot be applied to the
centre without first proving both its pivotal structure and pseudo-unitarity.

The integrated `PropertyF` build passed on cores 0–3 with four Lean threads;
the expanded audit covers 392 project modules and 4,226 declarations. The
strict target audit fails because `PropertyF.Ground.target` is missing.

`target_of_integral_numerical_center_core` gives an alternate route avoiding
mixed monodromy and actual core identification: it assumes integral dimensions
on the numerical S-centralizer of product-retract simples and invokes the
proved Fourier double-centralizer. `numericalProductCore_integral_of_image_monodromy`
proves the earlier actual-core integrality and restricted finite-order
hypotheses imply this numerical integrality. No independent proof of the new
integrality assertion is known, and the actual core being symmetric does not by
itself establish it for the larger numerical set.

Fusion `f93cf9e` constructs centre fusion, an FP-valued spherical structure
and the categorical square assuming centre rigidity and a compatible centre
pivotal lift of an FP-valued base pivotal structure. Integration's
`target_of_compatible_center_and_integral_numerical_core` uses that result
and the numerical-core route. This avoids assuming centre pseudo-unitarity,
but does not construct the base pivotal structure, compatible lift, rigidity,
invertible S or numerical-core integrality. The integrated full build and
strict project audit pass, covering 395 modules and 4,237 declarations.

Symmetric-core integrality update: `CentreIntegrate.signed_cycle_count` proves
the full signed permutation cycle polynomial identity, and
`integral_of_cycle_traces` / `integral_of_signed_cycle_traces` connect it to
positive categorical dimensions in both parity cases. This discharges the
combinatorial signed-sum evaluation; the actual symmetric-group action and
its categorical cycle-trace/parity identity remain unproved. Full project
audit passes for the new results.

Centre `62010e5` proves the dual-crossing tensor law and coevaluation
centrality. The newer centre `f1f0122` reports actual general centre rigidity
and must be merged; its evaluation centrality is no longer an open item once
integrated. `CentreIntegrate.twist_sign_of_dual_and_tensor` proves the sign
from two explicit twist identities on the simple/dual pair; those identities
remain open and the theorem does not assume or prove a Vafa theorem.

Centre `f1f0122` is now merged: `CentreRigid.rigidCenter` constructs actual
centre rigidity unconditionally, with the dual, evaluation and coevaluation
forgetting to the chosen base data. The reductions
`target_of_fusion_center_integral_numerical_core` and
`target_of_pivotal_lift_and_integral_numerical_core` discharge this formerly
open target premise. The latest full build and strict project audit pass (413
modules, 4,311 declarations). Fusion `f811c73` reduces compatible pivotal-lift
existence to component centrality; it has not yet been merged here.
