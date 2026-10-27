# Calculus workstream

Branch: `ground/calculus`. Started from `094175c`.

## Done

- Inspected the paper's §3, the existing conditional interfaces, and Mathlib's matrix positivity APIs.
- `PropertyF.Ground.Calculus.averagedGram`, `averagedGram_posDef`, `averagedGram_invariant`: a positive-definite invariant form for any finite group representation by complex invertible matrices. Built `PropertyF.Ground.Calculus.Averaging`.

## In progress

- Convert the invariant form to an explicit unitary change of basis and connect it to compatible star maps.

## Blocked / dependencies

- End-algebra and trace constructions require shared fusion and spherical category interfaces; precise requests are in `DEPENDS.md`.
- Trace transport and the S-matrix formula require modular and Galois-conjugation constructions.

## Remaining fields and estimate

All fields of `OverlapModel`, `ThreeStrandModel`, `ThreeStrandRealization`, and `CenterInputs.realize` remain to be built from genuine categories. The missing categorical semisimplicity, spherical calculus, compatible Wedderburn blocks, and Galois transport represent substantial work; no credible completion-time estimate is currently available.
