# Integration status

## Done

- `PropertyF.Ground.IsFusionCategory`, `BraidedFusionCategory`, `fusionMatrix`,
  `fpSimple`, `globalFPDimension`, `doubleDualIso`, `unitScalar`, `squaredNorm`,
  `globalDimension`, `GaloisConjugate`, `HasPseudoUnitaryGaloisConjugate`,
  `TargetStatement` in `PropertyF/Ground/Target.lean`; module builds.
- Posted provisional statement and explicit review requests to fusion/dimensions.
- `unit_algebraMap_bijective`, `unitScalarEquiv`, `unitScalar_algebraMap`,
  `algebraMap_unitScalar`, and `unitScalar_eq_equiv`: Schur supplies the
  canonical unit-scalar equivalence and validates the target definition.
- Merged snapshots from all six workstreams and built the integrated library.
- `ProjectAudit` scans all 822 integrated declarations for forbidden axioms.
- Field-by-field ownership and dependency graph in `LEDGER.md`.
- `DependencyAudit.findForbidden` checks transitive declaration types and bodies;
  its negative fixture catches a hidden old input. `scripts/audit-target.sh`
  rejects a missing final theorem and checks its type, dependencies, and axioms.

## In progress

- Prove faithful interpretation of the target and choice independence; freeze
  only after review. Extend audit tests and verify the final gate.
- Build bridge from the ground category to existing conditional theorem as
  constructions arrive. Coordinate with all owners.

## Blocked / remaining

No final theorem: the target needs FP/semisimple, intrinsic/spherical dimension,
centre, modular, and categorical braid/trace constructions enumerated in the
ledger. The FP spectral-radius/character identification and choice independence,
and scalar-map bijectivity and norm independence, are not yet proved. The work
is a substantial multi-workstream formalization, not a short integration patch;
no reliable completion-time estimate is available.
