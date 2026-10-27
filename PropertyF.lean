module
public import PropertyF.Audit
public import PropertyF.Ground.Target
public import PropertyF.Consequences
public import PropertyF.Descent
public import PropertyF.Transfer
public import PropertyF.Ground.Dimensions.DimensionField
public import PropertyF.Ground.Dimensions.FusionDimensionField
public import PropertyF.Ground.Dimensions.TargetDimensionField
public import PropertyF.Ground.Dimensions.Norm
public import PropertyF.Ground.Dimensions.Pivotal
public import PropertyF.Ground.Dimensions.Trace
public import PropertyF.Ground.Dimensions.GroundNorm
public import PropertyF.Ground.Dimensions.GlobalInequality

/-! Formalization of `paper/property-f-simplified.pdf`.
The main theorem is `PropertyF.propertyF_implies_weaklyIntegral`.
Its explicit standard-input and realization assumptions are in `PropertyF.Axioms`.
See `FORMALIZATION.md` for the complete assumption ledger.
-/
