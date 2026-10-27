# Dependencies

- **Fusion:** supplied the genuine semisimple category, simple decompositions, multiplicities and FP dimensions used in all categorical braid-block and trace theorems.
- **Dimensions:** supplied pivotal structures, traces, iterated trace compatibility and dimension bounds. The actual centre still needs a positive spherical structure. Integrate's current reduction does not require a spherical structure on the original category.
- **Modular:** supplied the actual categorical S matrix and Galois/character arithmetic. `positive_galois_rigidity` needs the actual S self-entry identity; `target_of_spherical_existence_and_center` takes invertibility of the centre S matrix as part of its explicit centre premise.
- **Centre / cabling:** construct the Drinfeld centre as a genuine braided fusion category, its nondegenerate S matrix and global dimension, and finite braid-image transfer to the selected centre simple.

The intrinsic overlap recurrence and both calculus lemmas are proved, as is arbitrary semilinear Galois transport of finite braid-algebra blocks. The integrator's scalar-twisted overlap interface is discharged. The old hypothesis structures have not been assembled literally; their braid-span closure requirements are stronger than what the proof needs, and the final dependency cone must not mention them.

## Round 2 centre interfaces

- **Centre / fusion:** actual Mathlib `Center C.Obj` rigidity and `IsFusionCategory` instances remain under construction. Our self-centrality theorem needs only the existing canonical centre and embeddings, and applies independently of those instances.
- **Dimensions:** an actual positive spherical structure on that centre must supply equality of its simple categorical dimensions and FP dimensions; `pivotalDimension_eq_fpDimension` then extends this to all objects.
- **Cabling / centre:** identify the core chosen for `target_of_actual_center` as objects centralizing both canonical images. `commonCentralizer_self` then supplies self-centrality; the integrality proof itself remains calculus work, with permutation action and trace evaluation still open.
