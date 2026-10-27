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
