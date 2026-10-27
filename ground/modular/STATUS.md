# Modular workstream status

## Done

- `PropertyF.Ground.Modular.Character.map`, `galoisPerm`, `galoisLabel`, and `galoisLabel_character`: construct the genuine action of every automorphism of ℂ on characters of integral fusion rules, then transport it to labels via a classification of those characters.
- `PropertyF.Ground.Modular.characters_exhausted`, `characters_bijective`, `dual_involutive`, and `normalized_columns_linearIndependent`: normalized columns classify all characters from S symmetry, S-square, nonzero dimensions and the Verlinde character equations.
- `PropertyF.Ground.Modular.modularDataOfVerlinde` constructs `ModularData` from the S identities and Verlinde character equations, deriving both classification and Galois fields.
- `PropertyF.Ground.Modular.modularDataOfCharacters`: constructs the existing `ModularData` package from its numerical identities plus a bijective classification of normalized S-columns as fusion characters. The Galois permutation and its character equation are constructed, not supplied.
- `PropertyF.Ground.Modular.braidGenerator_natural`, `conjugate_braidGenerator`, and `braidImageIso`: isomorphic objects have isomorphic braid-image groups via the actual tensor-power isomorphisms; this requires only a braided monoidal category.
- `PropertyF.Ground.Modular.braidGenerator_functor`, `braidImageFunctorIso`, `braidImages_of_essentiallySurjective`, and `conjugate_images`: the old `StandardInputs.conjugate_images` field is proved from the braided equivalence; the general result works for any faithful, essentially surjective braided monoidal functor without old hypothesis structures.
- `PropertyF.Ground.Modular.simpleLabels_equiv` constructs the bijection of simple representatives under any category equivalence for the frozen ground category, together with the actual object isomorphisms.
- Verified: `LEAN_NUM_THREADS=4 taskset -c 20-23 lake build PropertyF.Ground.Modular.Characters`.

## In progress

- Derive fusion-coefficient invariance from the semilinear functor and the label bijection; then prove FP invariance using the spectral-radius definition or positive-character uniqueness. Investigate categorical S-matrix ingredients.
- Make the S/Verlinde and Galois results usable directly in the ground development without old hypothesis structures in their dependency cone.

## Blocked / dependencies

- The category-level S-matrix and its properties require spherical traces from dimensions, fusion rules from fusion, and the modular/non-degenerate centre from centre. No such construction has yet been merged. See `ground/modular/DEPENDS.md`.
- Integrate published a provisional genuine-category target in `ground/integrate` commit 45da64d. Its strict audit prohibits old hypothesis structures in the final dependency cone; the category-free character and classification theorems are independent of those structures, while the two old-`ModularData` constructors are compatibility bridges only.

## Remaining

- Construct categorical S, symmetry, unit column, S-square, Verlinde, and normalized-column character classification from a genuine modular category; combine with the completed Galois action construction.
- Derive conjugate label equivalence and positive-character invariance from the semilinear braided equivalence and fusion workstream's FP uniqueness.
- `conjugate_images` is complete; integrate its general braided-functor version into the ground proof without old hypothesis structures.

This is substantial foundational work; the present result discharges only the abstract Galois-action construction once character classification and modular identities are established, not the category-level obligations.
