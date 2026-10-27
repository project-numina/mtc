# Modular workstream status

## Done

- `PropertyF.Ground.Modular.Character.map`, `galoisPerm`, `galoisLabel`, and `galoisLabel_character`: construct the genuine action of every automorphism of ℂ on characters of integral fusion rules, then transport it to labels via a classification of those characters.
- `PropertyF.Ground.Modular.characters_exhausted`, `characters_bijective`, `dual_involutive`, and `normalized_columns_linearIndependent`: normalized columns classify all characters from S symmetry, S-square, nonzero dimensions and the Verlinde character equations.
- `PropertyF.Ground.Modular.modularDataOfVerlinde` constructs `ModularData` from the S identities and Verlinde character equations, deriving both classification and Galois fields.
- `PropertyF.Ground.Modular.modularDataOfCharacters`: constructs the existing `ModularData` package from its numerical identities plus a bijective classification of normalized S-columns as fusion characters. The Galois permutation and its character equation are constructed, not supplied.
- `PropertyF.Ground.Modular.braidGenerator_natural`, `conjugate_braidGenerator`, and `braidImageIso`: isomorphic objects have isomorphic braid-image groups via the actual tensor-power isomorphisms; this requires only a braided monoidal category.
- `PropertyF.Ground.Modular.braidGenerator_functor`, `braidImageFunctorIso`, `braidImages_of_essentiallySurjective`, and `conjugate_images`: the old `StandardInputs.conjugate_images` field is proved from the braided equivalence; the general result works for any faithful, essentially surjective braided monoidal functor without old hypothesis structures.
- `PropertyF.Ground.Modular.simpleLabels_equiv` constructs the bijection of simple representatives under any category equivalence for the frozen ground category, together with the actual object isomorphisms.
- `PropertyF.Ground.Modular.conjugate_hom_finrank`, `conjugate_fusionCoeff`, `conjugate_fusionMatrix`, `conjugate_fpSimple`, `conjugate_labels`, and `conjugate_globalFPDimension`: Galois conjugacy preserves Hom dimensions, fusion rules, target spectral-radius FP dimensions, and global FP dimension. These statements use the frozen ground category and no old hypothesis bundles.
- `PropertyF.Ground.Modular.ground_conjugate_images` and `conjugate_propertyF`: braid images and property F transport to the conjugate in the frozen ground interface.
- `PropertyF.Ground.Modular.categoricalS`, `categoricalS_symmetric`, `categoricalS_unit`, and `categorical_global_eq_sum_squares`: the actual double-braiding trace defines S for a ground braided fusion category with a pivotal structure; symmetry and unit column follow without nondegeneracy, and global sum-of-squares follows from sphericality.
- `PropertyF.Ground.Modular.categoricalS_galois_action` constructs the Galois action on the actual S columns from explicitly stated S-square, nonzero-dimension, and Verlinde equations, with no old modular-data bundle; `galois_unit_properties` proves the paper's Proposition 2.1 from the exact numerical identities.
- The integrator's transitive type-and-body dependency scanner reports no old hypothesis structures in the ground Galois reduction, S symmetry/unit, or new Galois action and proposition.
- Verified: `LEAN_NUM_THREADS=4 taskset -c 20-23 lake build PropertyF.Ground.Modular.Characters`.

## In progress

- Prove S² and the Verlinde equations from a genuine non-degenerate spherical braided fusion category; integrate the category-level S with the algebraic Galois action.
- Make the S/Verlinde and Galois results usable directly in the ground development without old hypothesis structures in their dependency cone.

## Blocked / dependencies

- The category-level S-matrix and its properties require spherical traces from dimensions, fusion rules from fusion, and the modular/non-degenerate centre from centre. No such construction has yet been merged. See `ground/modular/DEPENDS.md`.
- Integrate published a provisional genuine-category target in `ground/integrate` commit 45da64d. Its strict audit prohibits old hypothesis structures in the final dependency cone; the category-free character and classification theorems are independent of those structures, while the two old-`ModularData` constructors are compatibility bridges only.

## Remaining

- Construct categorical S, symmetry, unit column, S-square, Verlinde, and normalized-column character classification from a genuine modular category; combine with the completed Galois action construction.
- Ground conjugate label and spectral FP invariance are complete. The legacy `StandardInputs.conjugate_labels` statement uses the old positive-character specification; it would additionally require the fusion workstream's uniqueness/comparison theorem. The ground result does not need that dependency.
- `conjugate_images` is complete; integrate its general braided-functor version into the ground proof without old hypothesis structures.

This is substantial foundational work; the present result discharges only the abstract Galois-action construction once character classification and modular identities are established, not the category-level obligations.
