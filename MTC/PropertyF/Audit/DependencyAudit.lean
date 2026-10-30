module
public import MTC.PropertyF.Statement
public import Lean.Util.FoldConsts
public import Lean.Util.CollectAxioms
public import Lean.Compiler.ImplementedByAttr
public import Lean.Compiler.ExternAttr

/-! Dependency-cone audit. Unlike `#print axioms`, this traverses declaration
bodies AND types, so it detects unconstructed hypothesis structures even if
those structures are passed through intermediate helper declarations. -/

public section
open Lean
namespace MTC.DependencyAudit

/-- A fixture used to test forbidden-dependency detection. -/
def forbidden : Array String := #["MTC.DependencyAudit.ForbiddenFixture"]

/-- Detect a forbidden structure or one of its generated declarations. -/
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
  | foreignImplementation (name : Name)
  | missingDeclaration (name : Name)
  deriving Repr

/-- Pinned upstream modules cannot import this project. Any other module must be
inspected even if it uses a namespace other than `MTC`. -/
def isTrustedUpstream (n : Name) : Bool :=
  #["Init", "Lean", "Std", "Lake", "Mathlib", "Batteries", "Aesop", "Qq",
    "Plausible", "ImportGraph", "ProofWidgets", "LeanSearchClient", "Cli"].any fun s =>
      n.toString == s || n.toString.startsWith (s ++ ".")

/-- Fail closed when a non-upstream declaration comes from a module whose
private bodies were not imported. Pinned upstream modules cannot depend on
project modules, so their bodies cannot hide a project hypothesis. -/
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
          if isTrustedUpstream m.module then continue
          if !m.importAll then return some (.uninspectedModule m.module)
      if Lean.isExtern env n || (Lean.Compiler.getImplementedBy? env n).isSome then
        return some (.foreignImplementation n)
      if let some ci := env.checked.get.find? n then
        pending := pending ++ ci.type.getUsedConstants
        if let some value := ci.value? (allowOpaque := true) then
          pending := pending ++ value.getUsedConstants
      else
        return some (.missingDeclaration n)
  return none

/-- A synthetic forbidden type for testing dependency traversal. -/
structure ForbiddenFixture where
  /-- A field ensuring that the synthetic type has an ordinary constructor. -/
  value : Nat

/-- Test fixture: a forbidden input hidden behind an ordinary definition. -/
def hiddenInput : Prop := ∃ _H : ForbiddenFixture, True

/-- Indirect fixture for testing transitive dependency inspection. -/
def hiddenInputWrapper : Prop := hiddenInput

/-- A proof with a clean statement but a forbidden type inside its body. -/
theorem hiddenProof : True :=
  (Classical.em (Nonempty ForbiddenFixture)).elim
    (fun _ => True.intro) (fun _ => True.intro)

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  unless (findForbidden env ``hiddenInputWrapper).isSome do
    throwError "dependency audit failed to detect a hidden old input"
  if let some bad := findForbidden env ``MTC.PropertyF.TargetStatement then
    throwError "target statement depends on forbidden declaration {bad}"
  logInfo "Dependency audit self-test passed; target statement passes the forbidden-dependency check."

end MTC.DependencyAudit
