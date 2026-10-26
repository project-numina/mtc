module
public import PropertyF.Consequences
public import PropertyF.Descent
public import PropertyF.Transfer

/-! Reproducible dependency audit. The standard-input structure is an explicit
parameter and therefore does not appear in `#print axioms`. Consult the ledger. -/

#print axioms PropertyF.propertyF_implies_weaklyIntegral
#print axioms PropertyF.global_dimension_fixed
#print axioms PropertyF.OverlapModel.trace_bound
#print axioms PropertyF.ThreeStrandModel.rigidity
#print axioms PropertyF.ModularData.galois_global_dimension
#print axioms PropertyF.propertyF_closure
#print axioms PropertyF.eventually_infinite_braidImage
#print axioms PropertyF.integer_of_galois_fixed
#print axioms PropertyF.pivotal_scalar_algebraic
#check @PropertyF.propertyF_implies_weaklyIntegral
#check @PropertyF.eventually_infinite_braidImage
