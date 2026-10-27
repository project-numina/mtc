module
public import PropertyF.Consequences
public import PropertyF.Descent
public import PropertyF.Transfer
public import PropertyF.Ground.Integrate.DependencyAudit

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

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut checked : Nat := 0
  for (name, _) in env.constants.toList do
    if name.toString.startsWith "PropertyF." then
      for ax in ← collectAxioms name do
        unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
          throwError "Unexpected axiom {ax} in project declaration {name}"
      checked := checked + 1
  logInfo m!"Audited {checked} project declarations: no sorryAx or custom axioms."
