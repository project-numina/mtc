# Integration status

## Done

- `weaklyIntegral_of_positive_modular_propertyF` proves the non-degenerate
  special case directly in the original category given a positive spherical
  structure and invertible S; no centre is used. It does not establish the
  frozen target for arbitrary degenerate braided categories.
- `categoricalS_det_eq_zero_of_transparent_column` shows a non-unit simple
  with transparent S-column makes S singular, formalizing the obstruction to
  applying the direct proof unchanged to a subcategory with nontrivial core.
- Merged dimensions 5646fbb, cabling 3ddf985, and fusion 4bd27d9; the full
  merged library built. Expanded both audit import lists to cover all newly
  merged modules; `ProjectAudit` passed for 3,569 declarations and checked the
  direct theorem's dependency cone. The target audit still fails correctly:
  `PropertyF.Ground.target` is missing.

- `PropertyF.Ground.IsFusionCategory`, `BraidedFusionCategory`, `fusionMatrix`,
  `fpSimple`, `globalFPDimension`, `doubleDualIso`, `unitScalar`, `squaredNorm`,
  `globalDimension`, `GaloisConjugate`, `HasPseudoUnitaryGaloisConjugate`,
  `TargetStatement` in `PropertyF/Ground/Target.lean`; module builds.
- Fusion and dimensions reviewed the target; it is frozen at commit 45da64d.
- `positive_ratio_of_galois_square` and `galois_unit_self_entry` isolate the
  bundle-free arithmetic and S-entry substitutions needed for the centre witness.
- `positive_bounded_conjugates_of_spherical` supplies all bounded-real
  conjugates given an actual spherical structure and dual-invariant dimensions.
- `selfDual_character_real` and `selfDual_character_galois_real` prove
  reality of self-dual fusion characters and all their Galois conjugates.
- `globalFPDimension_presentation` proves the spectral FP global dimension
  independent of the complete finite list of simple representatives.
- `target_of_legacy_standardInputs` checks the old conditional theorem applies
  to the frozen target; its explicit `StandardInputs` premise makes it unsuitable
  for the final dependency cone.
- `legacyFusionData` and `legacyGlobalDimensionData` construct every field of
  the old categorical data from ground definitions; dimension equality bridges
  are proved. These compatibility declarations are excluded from the final cone.
- `target_of_actual_center` states all remaining assumptions directly on
  Mathlib’s Drinfeld centre, at its correct object universe; one centre
  construction serves every Galois automorphism. `Integrate.bundledCenter`
  and `center_forget_fpDimension` wire the actual centre and forgetful functor
  conditional on the still-unproved rigid and fusion instances.
- `target_of_center_product_retracts` wires the centre workstream’s actual
  product-retract image theorem into the target reduction through faithful
  braided functors, with independent universe parameters.
- `twistedOverlapTrace_proved`, `galois_rigidity`, and
  `target_of_modular_center` discharge actual overlap coherence, trace bounds
  and three-strand rigidity. The final reduction needs only the modular centre
  and its finite-image transfer, as explicit unproved premises.
- `positive_bounded_conjugates_of_fp` proves real, positive bounded global FP
  conjugates for any ground braided fusion category, without spherical or
  pseudo-unitary assumptions. `target_of_center_and_overlap` therefore needs
  no spherical structure on the original category.
- `target_of_spherical_existence_center_and_overlap` only needs existence of
  an initial spherical structure for pseudo-unitary categories: dimensions
  derives the unique positive structure from it. This existence remains open.
- `target_of_canonical_spherical_center_and_overlap` wires the actual scalar
  twist and reduces the remaining rigidity premise to `TwistedOverlapTrace`.
- `target_of_canonical_spherical_and_center` reduces the target to canonical
  spherical existence and precise modular-centre, finite-image and rigidity
  facts. These are explicit unproved premises; the numerical and conjugate-bound
  steps are proved.
- `ScalarTwist.category`, `conjugate`, `pivotal`, `spherical`,
  `pivotalDimension_twist`, `objectPropertyF_twist`, and `labels` construct an
  arbitrary complex Galois twist and transport genuine pivotal dimensions and
  finite braid images; the twist is a ground braided fusion category.
  `ScalarTwist.squaredNorm_twist`, `globalDimension_twist`, and
  `globalFPDimension_twist` prove the corresponding intrinsic and FP global
  dimension transport with no spherical premise.
- `propertyF_of_galois_column` reduces the selected centre simple's finite
  braid images to symmetric-core integrality, a double-centralizer test, and
  finite images for generated labels. These remain categorical premises.
- `galois_propertyF` transports property F along the target's actual braided
  semilinear equivalence using modular’s braid-image equivalences.
- `weaklyIntegral_of_globalFPDimension_fixed` wires spectral FP integrality
  to finite-Galois descent without an old dimension-field hypothesis.
- `GaloisConjugate.refl` and `hasPseudoUnitaryGaloisConjugate_of_pseudoUnitary`
  verify that pseudo-unitary categories satisfy the frozen conjugacy condition.
- `simple_presentation_equiv` and `sum_simple_presentation` reindex any
  complete pairwise-nonisomorphic simple presentation and its invariant sums.
- `simple_strand_inclusion` combines fusion’s split-unit theorem with cabling’s
  identity-strand embedding and discharges that field for ground categories.
- `squaredNorm_eq_of_choices` connects the target norm to any conventional
  choice of scalar equivalence and simple double-dual isomorphism.
- `unit_algebraMap_bijective`, `unitScalarEquiv`, `unitScalar_algebraMap`,
  `algebraMap_unitScalar`, and `unitScalar_eq_equiv`: Schur supplies the
  canonical unit-scalar equivalence and validates the target definition.
- `Example.complexVectorSpaces` constructs finite-dimensional complex vector
  spaces as a genuine ground braided fusion category; both global dimensions
  equal one, and `Example.propertyF` proves finite braid images by their action
  on a finite tensor-product basis. `Example.target_hypotheses_inhabited`
  proves that both target hypotheses hold simultaneously for this category.
- Merged snapshots from all six workstreams and built the integrated library.
- `ProjectAudit` scans 3,242 integrated public and private declarations for forbidden axioms.
- Field-by-field ownership and dependency graph in `LEDGER.md`.
- `DependencyAudit.findIssue` checks transitive project types and private bodies;
  it fails closed on modules without private imports. Imported hidden-input and
  uninspected-module negative tests both pass. `scripts/audit-target.sh`
  rejects a missing final theorem and checks its type, dependencies, and axioms.

- `target_of_actual_center_generated` wires the proved equivalence between
  actual product retracts and the tensor/sum/retract closure of the canonical
  centre images into the final reduction. The double-centralizer membership
  assertion remains unproved.
- Merged round-2 centre, fusion, modular, calculus and cabling snapshots. The
  centre fusion bundle follows from rigidity plus finite semisimplicity; centre
  rigidity is reduced to the dual mate tensor law and centrality of evaluation
  and coevaluation. The centre FP-square follows from a right adjoint to
  forgetful with the stated underlying objects; the adjoint remains unbuilt.

## In progress

- For the general target, the elementary viable route remains a positive
  spherical modular extension with the required Galois-column finite images.
  The existing `target_of_modular_center` permits an abstract extension of the
  specified global dimension, while `target_of_actual_center` asks for the
  actual Mathlib centre. The direct modular proof avoids centre theory only
  when C itself has invertible S; restricting to the generated subcategory
  does not generally preserve non-degeneracy because its symmetric core can
  contain non-unit simples. No general smaller extension is constructed.

- `Integrate.dualCrossingIso` gives a unit-normalized natural candidate
  on a centre object’s chosen dual. Its tensor half-braiding law and the
  centre evaluation/coevaluation equations remain open; expanding the
  adjunction mates produces a large coherence identity involving both dual
  pairings and the original half-braiding. No rigid-centre instance is claimed.
- Centre pseudo-unitarity needs an independent route: FP-square plus the
  current categorical-square result cannot establish it without assuming the
  very positive spherical structure that ENO would then construct.
- Wire genuine centre fusion, positive spherical, dimension, S invertibility,
  centralizer and finite-image constructions as they arrive.
- Continue validating mathematical interfaces and exercising the final
  dependency gate as integration progresses.
- Refactor the conditional argument into bundle-free results as constructions
  arrive; a direct use of its old theorem would fail the strict dependency audit.

## Blocked / remaining

No final theorem: centre fusion, its positive spherical structure,
modularity, global dimension formula and finite-image transfer remain open as detailed
in the ledger. The FP spectral-radius/character identification and both global dimensions’
representative independence are proved. The work
is a substantial multi-workstream formalization, not a short integration patch;
no reliable completion-time estimate is available.

## Round 3 integration (2026-10-27)

- Merged committed tips fusion `ca79865`, dimensions `4af7956`, centre
  `6d26130` (already contained), modular `ee9ee20`, calculus `1870108`,
  and cabling `63f901e`. The actual centre induction and forgetful adjunction
  are now constructed without extra assumptions; finite simple representatives
  and enough injectives are also proved. Centre semisimplicity remains open.
- `center_globalDimension_square_of_actual_induction` applies the actual
  adjunction to prove the categorical centre square whenever centre rigidity,
  fusion and an FP-valued spherical structure exist.
  `target_of_center_image_monodromy_no_square` eliminates the square premise
  from cabling's most refined target reduction. Its remaining centre premises
  are rigidity, fusion, FP-valued spherical structure, invertible S, integral
  core dimensions, and finite mixed monodromy on the specified image labels.
- Cabling's fusion-ring Fourier argument establishes the numerical double
  centralizer; its identification with the actual symmetric core still needs
  finite-order mixed monodromy (or a different proof of the numerical-to-actual
  inclusion). This is not implied by property F on C by the existing proof:
  centre half-braidings are not generally the base braiding.
- Expanded both audits to 392 project modules. Full `lake build PropertyF`
  on cores 0–3 with four Lean threads passes; `ProjectAudit` checks 4,226
  declarations and the new reduction's dependency cone. Target audit fails
  as intended because `PropertyF.Ground.target` is absent.
- Shorter-route assessment: the new categorical square is automatic once the
  centre sphere exists, but it does not resolve the circularity in constructing
  that sphere. Fourier double-centralizer replaces a categorical theorem by
  an S-test, but identifying that S-test with the integral symmetric core is
  still open. No centre-free route for the general target is established.

- `target_of_integral_numerical_center_core` replaces both the actual-core
  integrality and mixed-monodromy premises by the single assertion that the
  numerical S-centralizer of product-retract simples has integer dimensions.
  Fourier double-centralization is proved. The comparison theorem
  `numericalProductCore_integral_of_image_monodromy` shows the earlier
  actual-core integrality plus finite-monodromy hypotheses imply the new
  numerical-integrality premise. The latter is not proved independently.

- Merged fusion `f93cf9e`. `target_of_compatible_center_and_integral_numerical_core`
  wires its `center_structure_of_compatible_pivotal` into the numerical-core
  reduction, constructing centre fusion and the FP-valued centre sphere from
  centre rigidity, an FP-valued base pivotal structure, and a compatible
  pivotal lift. This is an alternative to proving centre pseudo-unitarity
  first; existence of both base pivotal structure and compatible lift remains
  open. Invertible centre S and numerical-core integrality remain assumptions.
- The dual-evaluation coherence attempt expanded the mate counit but did not
  derive the required equation: the mate component is at `Z ⊗ U`, so original
  half-braiding tensor coherence and unit normalization still need to be
  related. Scratch experiments are not imported or committed.
- Full build and strict project audit pass after these changes, covering 395
  modules and 4,237 declarations. The final target remains unproved.

- `CentreIntegrate.signed_cycle_count` proves the signed cycle-count
  polynomial identity over ℂ, with fixed points included as cycles. The proof
  counts fixed colourings using same-cycle quotients, uses a determinant to
  cancel non-injective colourings, and extends from natural values by
  polynomial interpolation. `integral_of_cycle_traces` and
  `integral_of_signed_cycle_traces` wire the identity to calculus's
  integrality criterion for the two parity cases. Construction of the
  permutation action and either appropriate categorical cycle trace formula
  remains open. The focused build and full project audit pass (399 modules,
  4,254 declarations).

- Merged centre `62010e5`: the normalized dual crossing tensor law and
  coevaluation centrality are proved. Centre `f1f0122` has since also proved
  general evaluation centrality and actual centre rigidity; that newer commit
  is awaiting integration. `CentreIntegrate.twist_sign_of_dual_and_tensor`
  reduces the simple twist parity sign to dual compatibility and
  multiplicativity on the dual pair; both remain explicit hypotheses. The
  coevaluation nonzero argument is proved from nonzero simple dimension.

- Merged actual centre rigidity `f1f0122` and its forgetful comparisons.
  `target_of_fusion_center_integral_numerical_core` removes centre rigidity
  from the numerical-core reduction, while
  `target_of_pivotal_lift_and_integral_numerical_core` removes it from the
  compatible-pivotal route. The other stated premises remain unproved.
  Expanded project audit and full build pass for 413 modules and 4,311
  declarations. Fusion's newer pivotal-centrality reduction is not yet merged.

- Merged fusion `f811c73`. `target_of_pivotal_centrality_and_integral_numerical_core`
  now constructs the compatible centre pivotal lift from the explicit
  `PivotalComponentsCentral` equation, using the constructed centre rigid
  structure. It still assumes an FP-valued base pivotal structure, that
  centrality equation, centre S invertibility and numerical-core integrality.
  The full build and strict project audit pass (416 modules, 4,328 declarations).

- Merged dimensions `4117b5b`. `spherical_rightTrace_rightDual` and
  `pivotalTwistScalar_rightDual` establish equality of twist scalars for a
  spherical simple and its right dual. `self_doubleBraiding_eq_one_rightDual`
  establishes centrality of X with X* from centrality with itself, using the
  generated-subcategory dual theorem. The parity sign now follows from the
  still-unproved pivotal twist balancing equation on this one dual pair, as
  `twist_sign_of_spherical_self_transparency_and_balancing` records. Full build
  and strict project audit pass (426 modules, 4,363 declarations).

- `doubleDualTensor_evaluation`, `drinfeld_tensor_of_pairing_cap`, and
  `balance_of_drinfeld_tensor` reduce pivotal twist balancing to one explicit
  tensor-pairing cap/hexagon identity. The identity is the `hcap` premise in
  `TwistBalancing.lean` and is still unproved; it would discharge the parity
  sign and support Vafa's mixed-monodromy route. Full build and project audit
  pass (427 modules, 4,366 declarations).

- Merged fusion `36bf5d8`. `pivotalComponentsCentral_proved` constructs the
  compatible centre pivotal lift from any base pivotal structure; together
  with constructed centre rigidity and pseudo-unitarity it constructs centre
  fusion and the positive spherical structure. The new
  `target_of_pivotal_base_and_integral_numerical_core` retains only base
  pivotal existence, centre S invertibility, and numerical-core integrality.
  No general pivotal existence is claimed. Full build and project audit pass
  (432 modules, 4,394 declarations).

- Merged calculus, including the type-A presentation, actual permutation
  actions, parity-deletion reduction, and spherical iterated trace theorem.
  `simple_integral_of_self_transparency_and_dual_balancing` and
  `symmetricCore_integral_of_dual_balancing` prove actual symmetric-core
  integrality from twist balancing on its simple/dual pairs. The resulting
  `target_of_pivotal_base_balancing_and_image_monodromy` assumes base pivotal
  existence, centre S invertibility, that balancing equation and the restricted
  mixed-monodromy finite-order condition. Balancing is still unproved. Full
  build and project audit pass (446 modules, 4,565 declarations).

- Merged calculus actual-core integrality and modular `3b920a6` (finite mixed
  monodromy from pivotal balancing). `target_of_pivotal_base_modular_balanced_center`
  now constructs centre rigidity, fusion, positive sphericality, its dimension
  square, actual core integrality, and restricted mixed-monodromy finiteness.
  Its explicit premises are existence of any base pivotal structure,
  invertibility of centre S, and centre pivotal twist balancing. None of those
  three is asserted proved. Full build and strict audit pass (475 modules,
  4,731 declarations).

- Modular's transparency criterion is merged and wired as
  `target_of_pivotal_balanced_center_trivial_transparency`: centre S
  invertibility can be replaced by triviality of actual transparent simples
  once twist balancing holds. Base pivotal existence, balancing, and that
  transparency statement are explicit and unproved. Full build and strict
  project audit pass (477 modules, 4,736 declarations).
