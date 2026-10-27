# Integration dependencies

All remaining items are explicit, temporary arguments to
`Ground.target_of_actual_center`; none is an assumption in the frozen
`TargetStatement`. The exact Lean type is in
`PropertyF/Ground/Integrate/ActualCenterReduction.lean`. No spherical structure
is needed on the original category: `positive_bounded_conjugates_of_fp`
constructs the bounds directly from its FP fusion character.

- `hCenter`: for pseudo-unitary property-F C, construct one actual Drinfeld
  centre with rigid and fusion instances and a positive spherical structure,
  invertible categorical S, global dimension FPdim(C)², and the stated
  centralizer conditions. Owners: centre (Z,
  dimension formula, centralizers, finite-image transfer and S invertibility)
  and dimensions (positive spherical structures); modular supplies S
  identities and Galois action. Calculus proved the actual overlap recurrence
  and integrate wired it to `Ground.galois_rigidity`, so no braid-calculus
  premise remains.
  `propertyF_of_galois_column` derives the selected finite image from integral
  dimensions on the common centralizer, a double-centralizer test and generated
  labels being actual product retracts. The product-retract finite-image
  transfer is constructed through a faithful braided functor to Mathlib Center;
  full-centre dominance is neither assumed nor true in general. The integral
  core, double centralizer and product-retract identification remain explicit
  centre obligations.

The centre must still be equipped with a positive spherical structure;
its construction remains owned by centre and dimensions.

Fusion has proved `one_le_globalFPDimension` directly from the unit fusion
matrix, so global FP positivity is discharged. The last sum/integrality step, Galois transport of property F and global FP
invariance, and the numerical contradiction are proved without old input
structures. `ground/integrate/LEDGER.md` details all underlying old fields.
