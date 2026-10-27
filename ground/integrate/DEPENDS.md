# Integration dependencies

All remaining items below are explicit, temporary arguments to
`Ground.target_of_bounded_conjugates_and_witness`; none is an assumption in the frozen
`TargetStatement`. Their exact Lean types are in
`PropertyF/Ground/Integrate/Reduction.lean`.

- `hConjugates`: for each automorphism σ, `σ (globalFPDimension C)` is a
  positive real number at most the original global FP dimension. Owner:
  dimensions (pseudo-unitary canonical spherical structure, transport, real
  norms and the global FP bound), with fusion supplying FP character results.
- `hWitness`: for σ producing a strictly smaller real conjugate a, and its
  inverse producing b, produce reals f,d with `σ f = d`, `f*b = FPdim(C)`,
  `1 ≤ f`, and `f = |d|`. Owners: centre (canonical centre, centralizers,
  property F, positive centre dimension and global-square identities), modular
  (S-matrix/Verlinde/Galois unit column), and calculus (three-strand rigidity
  from actual finite images and spherical traces). Dimensions supplies the
  positive spherical structure and trace/dimension transport. This is the
  paper's specific centre/rigidity intermediate conclusion, not target fixedness.

Fusion has proved `one_le_globalFPDimension` directly from the unit fusion
matrix, so global FP positivity is discharged. The last sum/integrality step, Galois transport of property F and global FP
invariance, and the numerical contradiction are proved without old input
structures. `ground/integrate/LEDGER.md` details all underlying old fields.
