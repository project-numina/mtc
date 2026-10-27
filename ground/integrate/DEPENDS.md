# Integration dependencies

All remaining items are explicit, temporary arguments to
`Ground.target_of_center_and_overlap`; none is an assumption in the frozen
`TargetStatement`. The exact Lean type is in
`PropertyF/Ground/Integrate/CenterOnlyReduction.lean`. No spherical structure
is needed on the original category: `positive_bounded_conjugates_of_fp`
constructs the bounds directly from its FP fusion character.

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

The centre must still be equipped with a positive spherical structure;
its construction remains owned by centre and dimensions.

Fusion has proved `one_le_globalFPDimension` directly from the unit fusion
matrix, so global FP positivity is discharged. The last sum/integrality step, Galois transport of property F and global FP
invariance, and the numerical contradiction are proved without old input
structures. `ground/integrate/LEDGER.md` details all underlying old fields.
