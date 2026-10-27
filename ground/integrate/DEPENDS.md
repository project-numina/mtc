# Integration dependencies

All remaining items below are explicit, temporary arguments to
`Ground.target_of_spherical_existence_center_and_overlap`; none is an assumption in the frozen
`TargetStatement`. Their exact Lean types are in
`PropertyF/Ground/Integrate/OverlapReduction.lean`. The former rigidity premise
is discharged from the precise categorical `TwistedOverlapTrace` recurrence.

- `hSpherical`: for pseudo-unitary C, construct any actual spherical pivotal
  structure. Owner: dimensions. Given that structure,
  `positive_spherical_of_spherical_pseudoUnitary` constructs the canonical
  positive FP-dimensional structure without extra assumptions. `spherical_dimension_dual_of_positive` and
  `positive_bounded_conjugates_of_spherical` then supply dual invariance and
  all real-conjugate bounds without extra assumptions. The alternative
  `target_of_spherical_and_witness` needs only self-dual simple dimensions.
- `hCenter`: for pseudo-unitary property-F C and each σ, construct the centre
  as a genuine braided fusion category Z with positive spherical structure,
  invertible categorical S, and global dimension FPdim(C)²; prove that any
  simple with the Galois-unit S column has property F and obeys the concrete
  three-strand rigidity implication. Owners: centre (Z, dimension formula,
  centralizers, finite-image transfer and S invertibility), dimensions
  (positive spherical structures and trace transport), and calculus (actual
  three-strand rigidity); modular supplies S identities and Galois action.
  Arbitrary scalar-twisted ground categories and their pivotal dimensions,
  FP labels and braid-image finiteness are constructed by integrate; the
  all-strand categorical overlap identity remains owned by calculus.
  `propertyF_of_galois_column` derives the finite-image implication from
  integral dimensions on the common centralizer, a double-centralizer test,
  and property F on the generated subcategory. These three assertions remain
  explicit centre obligations. The exact final reduction is in
  `CenterReduction.lean`.

Fusion has proved `one_le_globalFPDimension` directly from the unit fusion
matrix, so global FP positivity is discharged. The last sum/integrality step, Galois transport of property F and global FP
invariance, and the numerical contradiction are proved without old input
structures. `ground/integrate/LEDGER.md` details all underlying old fields.
