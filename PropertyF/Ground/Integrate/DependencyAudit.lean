module
public import PropertyF.Axioms
public import PropertyF.Ground.Target
public import Lean.Util.FoldConsts
public import Lean.Util.CollectAxioms

/-! Dependency-cone audit. Unlike `#print axioms`, this traverses declaration
bodies AND types, so it detects unconstructed hypothesis structures even if
those structures are passed through intermediate helper declarations. -/

public section
open Lean
namespace PropertyF.Ground.DependencyAudit

def forbidden : Array String := #[
  "PropertyF.FusionData", "PropertyF.GlobalDimensionData",
  "PropertyF.BraidedFusionCategory", "PropertyF.MultiplicityData",
  "PropertyF.StandardInputs", "PropertyF.PseudoUnitaryInputs",
  "PropertyF.CenterInputs", "PropertyF.DimensionField", "PropertyF.OverlapModel",
  "PropertyF.ThreeStrandModel", "PropertyF.ThreeStrandRealization",
  "PropertyF.ProductImageWitness", "PropertyF.CablingWitness",
  "PropertyF.GeneratedInputs", "PropertyF.ModularData"]

def isForbidden (n : Name) : Bool :=
  forbidden.any fun s => n.toString == s || n.toString.startsWith (s ++ ".")

/-- Traverse all direct and transitive constants in both types and values.
Opaque values are inspected too; a visited set handles recursive declarations. -/
partial def findForbidden (env : Environment) (root : Name) : Option Name := Id.run do
  let mut pending := #[root]
  let mut visited : Std.HashSet Name := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    if !visited.contains n then
      visited := visited.insert n
      if isForbidden n then return some n
      if let some ci := env.checked.get.find? n then
        pending := pending ++ ci.type.getUsedConstants
        if let some value := ci.value? (allowOpaque := true) then
          pending := pending ++ value.getUsedConstants
  return none

/-- A scan must reject a forbidden name or an uninspected project module. -/
inductive Issue where
  | forbidden (name : Name)
  | uninspectedModule (moduleName : Name)
  deriving Repr

/-- Fail closed when a project declaration comes from a module whose private
bodies were not imported. External modules cannot depend on project modules,
so their bodies cannot hide a project hypothesis and need not be traversed. -/
partial def findIssue (env : Environment) (root : Name) : Option Issue := Id.run do
  let mut pending := #[root]
  let mut visited : Std.HashSet Name := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    if !visited.contains n then
      visited := visited.insert n
      if isForbidden n then return some (.forbidden n)
      if let some idx := env.getModuleIdxFor? n then
        if let some m := env.header.modules[idx.toNat]? then
          if !m.module.toString.startsWith "PropertyF" then continue
          if !m.importAll then return some (.uninspectedModule m.module)
      if let some ci := env.checked.get.find? n then
        pending := pending ++ ci.type.getUsedConstants
        if let some value := ci.value? (allowOpaque := true) then
          pending := pending ++ value.getUsedConstants
  return none

/-- Test fixture: a forbidden input hidden behind an ordinary definition. -/
def hiddenInput : Prop := ∃ _H : PropertyF.StandardInputs.{0, 0}, True

def hiddenInputWrapper : Prop := hiddenInput

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  unless (findForbidden env ``hiddenInputWrapper).isSome do
    throwError "dependency audit failed to detect a hidden old input"
  if let some bad := findForbidden env ``PropertyF.Ground.TargetStatement then
    throwError "target statement depends on forbidden declaration {bad}"
  logInfo "Dependency audit self-test passed; target statement has no old hypothesis structures."

end PropertyF.Ground.DependencyAudit
