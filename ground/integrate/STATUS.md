# Integration status

## Done

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
- `target_of_spherical_and_witness` reduces the target to existence of a
  self-dual spherical structure and the centre/rigidity witness. Both are
  explicit unproved premises; the numerical and conjugate-bound steps are proved.
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
  spaces as a genuine ground braided fusion category, proving non-vacuity of
  the category interface (property F and pseudo-unitarity are not yet shown).
- Merged snapshots from all six workstreams and built the integrated library.
- `ProjectAudit` scans all 1,734 integrated declarations for forbidden axioms.
- Field-by-field ownership and dependency graph in `LEDGER.md`.
- `DependencyAudit.findIssue` checks transitive project types and private bodies;
  it fails closed on modules without private imports. Imported hidden-input and
  uninspected-module negative tests both pass. `scripts/audit-target.sh`
  rejects a missing final theorem and checks its type, dependencies, and axioms.

## In progress

- Continue validating mathematical interfaces and exercising the final
  dependency gate as integration progresses.
- Refactor the conditional argument into bundle-free results as constructions
  arrive; a direct use of its old theorem would fail the strict dependency audit.

## Blocked / remaining

No final theorem: pseudo-unitary spherical structures, centre fusion and
modularity, and the categorical braid/trace witness remain open as detailed
in the ledger. The FP spectral-radius/character identification and both global dimensions’
representative independence are proved. The work
is a substantial multi-workstream formalization, not a short integration patch;
no reliable completion-time estimate is available.
