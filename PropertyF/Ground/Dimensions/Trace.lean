module
public import PropertyF.Ground.Dimensions.Pivotal
public import Mathlib.CategoryTheory.Monoidal.Linear

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.Dimensions.PivotalStructure

universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
  [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  (p : PivotalStructure (C := C)) {X : C}

omit [Linear ℂ C] [MonoidalLinear ℂ C] in
/-- The right trace is linear in its endomorphism argument. -/
theorem rightTrace_add (f g : X ⟶ X) : p.rightTrace (f + g) = p.rightTrace f + p.rightTrace g := by
  apply End.homEquiv.injective
  simp [rightTrace, tensorHom_def]

theorem rightTrace_smul (c : ℂ) (f : X ⟶ X) : p.rightTrace (c • f) = c • p.rightTrace f := by
  apply End.homEquiv.injective
  simp [rightTrace, tensorHom_def]

omit [Linear ℂ C] [MonoidalLinear ℂ C] in
/-- The left trace is linear in its endomorphism argument. -/
theorem leftTrace_add (f g : X ⟶ X) : p.leftTrace (f + g) = p.leftTrace f + p.leftTrace g := by
  apply End.homEquiv.injective
  simp [leftTrace, tensorHom_def]

theorem leftTrace_smul (c : ℂ) (f : X ⟶ X) : p.leftTrace (c • f) = c • p.leftTrace f := by
  apply End.homEquiv.injective
  simp [leftTrace, tensorHom_def]

end PropertyF.Ground.Dimensions.PivotalStructure
