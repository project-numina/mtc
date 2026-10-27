# Modular workstream status

## Done

- `PropertyF.Ground.Modular.Character.map`, `galoisPerm`, `galoisLabel`, and `galoisLabel_character`: construct the genuine action of every automorphism of ℂ on characters of integral fusion rules, then transport it to labels via a classification of those characters.
- `PropertyF.Ground.Modular.modularDataOfCharacters`: constructs the existing `ModularData` package from its numerical identities plus a bijective classification of normalized S-columns as fusion characters. The Galois permutation and its character equation are constructed, not supplied.
- Verified: `LEAN_NUM_THREADS=4 taskset -c 20-23 lake build PropertyF.Ground.Modular.Characters`.

## In progress

- Derive the classification of fusion characters from the S identities and the Verlinde character equations, rather than accepting bijectivity.

## Blocked / dependencies

- The category-level S-matrix and its properties require spherical traces from dimensions, fusion rules from fusion, and the modular/non-degenerate centre from centre. No such construction has yet been merged. See `ground/modular/DEPENDS.md`.
- The final target statement and category interface are owned by integrate and have not yet been published on the board.

## Remaining

- Construct categorical S, symmetry, unit column, S-square, Verlinde, and normalized-column character classification from a genuine modular category; combine with the completed Galois action construction.
- Derive conjugate label equivalence and positive-character invariance from the semilinear braided equivalence and fusion workstream's FP uniqueness.
- Construct braid-image equivalences from braided monoidal equivalence and tensor-power coherence.

This is substantial foundational work; the present result discharges only the abstract Galois-action construction once character classification and modular identities are established, not the category-level obligations.
