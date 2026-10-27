module
public import PropertyF.Audit
public meta import PropertyF.Ground.Integrate.DependencyAudit
public import PropertyF.Ground.Integrate.UnitScalar
public import PropertyF.Ground.Integrate.Example
public import PropertyF.Ground.Fusion.Integrality
public import PropertyF.Ground.Fusion.Splitting
public import PropertyF.Ground.Dimensions.DimensionField
public import PropertyF.Ground.Dimensions.Norm
public import PropertyF.Ground.Calculus.StarSpan
public import PropertyF.Ground.Centre.Embeddings
public import PropertyF.Ground.Modular.Classification
public import PropertyF.Ground.Cabling.Strands
public import PropertyF.Ground.Cabling.Pure
public import PropertyF.Ground.Cabling.Witness

/-! Scan all currently integrated project declarations, including the ground
modules. `PropertyF.Audit` alone sees only its own imports. -/

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
  logInfo m!"Audited {checked} integrated project declarations: no sorryAx or custom axioms."

open Lean Elab Command PropertyF.Ground.DependencyAudit in
run_cmd do
  let env ← getEnv
  unless (findForbidden env ``PropertyF.propertyF_implies_weaklyIntegral).isSome do
    throwError "dependency audit did not reject the imported conditional theorem"
  for n in #[``PropertyF.Ground.unit_algebraMap_bijective,
      ``PropertyF.Ground.Example.complexVectorSpaces,
      ``PropertyF.Ground.Dimensions.squaredNorm_independent] do
    if let some bad := findForbidden env n then
      throwError "unexpected old hypothesis {bad} in ground result {n}"
  logInfo "Dependency audit passed imported positive and negative fixtures."
