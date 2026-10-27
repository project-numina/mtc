# Integration dependencies

All items below are explicit, temporary arguments to
`Ground.target_of_numerical_witnesses`; none is an assumption in the frozen
`TargetStatement`. Their exact Lean types are in
`PropertyF/Ground/Integrate/Reduction.lean`.

- `hPositive`: `0 < globalFPDimension C` for pseudo-unitary property-F C.
  Owner: fusion (positivity of spectral FP dimensions; this is expected for all
  ground fusion categories).
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

The last sum/integrality step, Galois transport of property F and global FP
invariance, and the numerical contradiction are proved without old input
structures. `ground/integrate/LEDGER.md` details all underlying old fields.
