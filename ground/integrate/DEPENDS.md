# Integration dependencies

All remaining items below are explicit, temporary arguments to
`Ground.target_of_canonical_spherical_and_witness`; none is an assumption in the frozen
`TargetStatement`. Their exact Lean types are in
`PropertyF/Ground/Integrate/Reduction.lean`.

- `hCanonical`: for pseudo-unitary C, construct an actual spherical pivotal
  structure whose simple dimensions equal the corresponding positive FP
  dimensions. Owner: dimensions. `spherical_dimension_dual_of_positive` and
  `positive_bounded_conjugates_of_spherical` then supply dual invariance and
  all real-conjugate bounds without extra assumptions. The alternative
  `target_of_spherical_and_witness` needs only self-dual simple dimensions.
- `hWitness`: for σ producing a strictly smaller real conjugate a, and its
  inverse producing b, produce reals f,d with `σ f = d`, `f*b = FPdim(C)`,
  `1 ≤ f`, and `f = |d|`. Owners: centre (canonical centre, centralizers,
  property F, positive centre dimension and global-square identities), modular
  (S-matrix/Verlinde/Galois unit column), and calculus (three-strand rigidity
  from actual finite images and spherical traces). Dimensions supplies the
  positive spherical structure and trace/dimension transport. This is the
  paper's specific centre/rigidity intermediate conclusion, not target fixedness.
  `center_witness_of_modular_and_rigidity` now derives this conclusion from
  the modular global identity, the Galois-unit self-column and rigidity.

Fusion has proved `one_le_globalFPDimension` directly from the unit fusion
matrix, so global FP positivity is discharged. The last sum/integrality step, Galois transport of property F and global FP
invariance, and the numerical contradiction are proved without old input
structures. `ground/integrate/LEDGER.md` details all underlying old fields.
