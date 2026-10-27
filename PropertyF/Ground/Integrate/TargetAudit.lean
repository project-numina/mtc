module
public meta import PropertyF.Ground.Integrate.DependencyAudit

/-! Explicit final-theorem gate. This module intentionally fails to build until
`PropertyF.Ground.target : PropertyF.Ground.TargetStatement` exists. It is not
part of the ordinary library build while the proof remains under development. -/

open Lean Elab Command PropertyF.Ground.DependencyAudit in
run_cmd do
  let env ← getEnv
  let targetName := `PropertyF.Ground.target
  let some ci := env.find? targetName
    | throwError "Final theorem PropertyF.Ground.target is missing"
  match ci with
  | .thmInfo _ => pure ()
  | _ => throwError "PropertyF.Ground.target must be a theorem"
  match ci.type with
  | .const n _ =>
      unless n == ``PropertyF.Ground.TargetStatement do
        throwError "Final theorem must have exactly the frozen TargetStatement type"
  | _ => throwError "Final theorem must have exactly the frozen TargetStatement type"
  if let some bad := findForbidden env targetName then
    throwError "Final theorem depends on forbidden declaration {bad}"
  let axioms ← collectAxioms targetName
  for ax in axioms do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
      throwError "Final theorem depends on forbidden axiom {ax}"
  logInfo m!"Final theorem axiom dependencies: {axioms}"
