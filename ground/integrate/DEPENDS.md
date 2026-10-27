# Integration dependencies

All remaining items are explicit, temporary arguments to
`Ground.target_of_modular_center`; none is an assumption in the frozen
`TargetStatement`. The exact Lean type is in
`PropertyF/Ground/Integrate/CenterReductionComplete.lean`. No spherical structure
is needed on the original category: `positive_bounded_conjugates_of_fp`
constructs the bounds directly from its FP fusion character.

- `hCenter`: for pseudo-unitary property-F C and each σ, construct the centre
  as a genuine braided fusion category Z with positive spherical structure,
  invertible categorical S, and global dimension FPdim(C)²; prove that any
  simple with the Galois-unit S column has property F. Owners: centre (Z,
  dimension formula, centralizers, finite-image transfer and S invertibility)
  and dimensions (positive spherical structures); modular supplies S
  identities and Galois action. Calculus proved the actual overlap recurrence
  and integrate wired it to `Ground.galois_rigidity`, so no braid-calculus
  premise remains.
  `propertyF_of_galois_column` derives the finite-image implication from
  integral dimensions on the common centralizer, a double-centralizer test,
  and property F on the generated subcategory. These three assertions remain
  explicit centre obligations. The exact final reduction is in
  `CenterReductionComplete.lean`.

The centre must still be equipped with a positive spherical structure;
its construction remains owned by centre and dimensions.

Fusion has proved `one_le_globalFPDimension` directly from the unit fusion
matrix, so global FP positivity is discharged. The last sum/integrality step, Galois transport of property F and global FP
invariance, and the numerical contradiction are proved without old input
structures. `ground/integrate/LEDGER.md` details all underlying old fields.
