# Integration status

## Done

- `PropertyF.Ground.IsFusionCategory`, `BraidedFusionCategory`, `fusionMatrix`,
  `fpSimple`, `globalFPDimension`, `doubleDualIso`, `unitScalar`, `squaredNorm`,
  `globalDimension`, `GaloisConjugate`, `HasPseudoUnitaryGaloisConjugate`,
  `TargetStatement` in `PropertyF/Ground/Target.lean`; module builds.
- Posted provisional statement and explicit review requests to fusion/dimensions.
- Field-by-field ownership and dependency graph in `LEDGER.md`.

## In progress

- Prove faithful interpretation of the target and choice independence; freeze
  only after review. Implement dependency-cone audit with negative tests.
- Build bridge from the ground category to existing conditional theorem as
  constructions arrive. Coordinate with all owners.

## Blocked / remaining

No final theorem: the target needs FP/semisimple, intrinsic/spherical dimension,
centre, modular, and categorical braid/trace constructions enumerated in the
ledger. The FP spectral-radius/character identification and choice independence,
and scalar-map bijectivity and norm independence, are not yet proved. The work
is a substantial multi-workstream formalization, not a short integration patch;
no reliable completion-time estimate is available.
