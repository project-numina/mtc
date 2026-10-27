# Calculus workstream

Branch: `ground/calculus`. Started from `094175c`.

## Done

- Inspected the paper's §3, the existing conditional interfaces, and Mathlib's matrix positivity APIs.
- `PropertyF.Ground.Calculus.averagedGram`, `averagedGram_posDef`, `averagedGram_invariant`: a positive-definite invariant form for any finite group representation by complex invertible matrices. Built `PropertyF.Ground.Calculus.Averaging`.
- `PropertyF.Ground.Calculus.groupInImage_span`, `presented_group_span`, `unitary_block_star_inv`, and `presented_intertwiner_map_star`: any algebra map intertwining group elements between two unitary block presentations preserves adjoints on all blocks. The categorical strand maps still need to be constructed and shown to intertwine.
- `PropertyF.Ground.Calculus.groupImageAlgebra_unitary_blocks` and `braidAlgebra_unitary_blocks`: Wedderburn matrix blocks can be chosen so every (categorical) finite-group image element acts unitarily in every block. The compatible star-map property is proved once an intertwining algebra map has been supplied.
- `PropertyF.Ground.Calculus.braidEndRepresentation`, `braidAlgebra`, `braidAlgebra_toSubmodule`, `braidAlgebra_semisimple`, and `braidAlgebra_blocks`: the genuine categorical braid-image span is a finite-dimensional semisimple algebra with complex matrix blocks when the image is finite.
- `PropertyF.Ground.Calculus.groupImageAlgebra_toSubmodule`, `groupImageAlgebra_semisimple`, `groupImageAlgebra_finite`, and `groupImageAlgebra_blocks`: the span of any finite group image is a finite-dimensional semisimple algebra, with a complex matrix-block decomposition by Maschke and Wedderburn–Artin. The block equivalence is made unitary in `UnitaryBlocks`; its categorical multiplicities and compatibility across embeddings remain to be identified.
- `PropertyF.Ground.Calculus.imageGenerator`, `represented_braid_finite_order`, `represented_square_finite_order`, and `braid_square_finite_order`: finite order for actual categorical braid generators and their represented squares.
- `PropertyF.Ground.Calculus.map_star_of_mem_span`, `star_eq_coe_inv_of_unitary`, and `map_star_on_unitary_group_span`: an intertwining algebra map preserves adjoints on the span of unitary group images.
- `PropertyF.Ground.Calculus.exists_unitarizing_basis`: constructs a common change of basis making every group element unitary, using the square root of the averaged Gram matrix.

## In progress

- Connect the finite-group unitary realization and span lemma to the actual categorical braid-image embeddings.

## Blocked / dependencies

- End-algebra and trace constructions require shared fusion and spherical category interfaces; precise requests are in `DEPENDS.md`.
- Trace transport and the S-matrix formula require modular and Galois-conjugation constructions.

## Remaining fields and estimate

All fields of `OverlapModel`, `ThreeStrandModel`, `ThreeStrandRealization`, and `CenterInputs.realize` remain to be assembled from genuine categories. The finite-order field now has a direct theorem once its categorical representation is constructed. The missing categorical semisimplicity, spherical calculus, compatible Wedderburn blocks, and Galois transport represent substantial work; no credible completion-time estimate is currently available.
