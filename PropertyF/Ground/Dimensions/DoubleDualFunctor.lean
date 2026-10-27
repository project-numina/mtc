module
public import PropertyF.Ground.Dimensions.FourthDualRoots

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.Dimensions
universe v u
variable (C : Type u) [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]

/-- The double-right-dual assignment is a covariant endofunctor. -/
def doubleDualFunctor : C ⥤ C where
  obj X := (Xᘁ)ᘁ
  map f := (fᘁ)ᘁ
  map_id X := by simp
  map_comp f g := by simp [comp_rightAdjointMate]

variable [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]

omit [Linear ℂ C] [MonoidalLinear ℂ C] in
/-- Right adjoint mates preserve addition. -/
theorem rightAdjointMate_add {X Y : C} (f g : X ⟶ Y) :
    (f + g)ᘁ = fᘁ + gᘁ := by
  simp [rightAdjointMate]

instance : (doubleDualFunctor C).Linear ℂ where
  map_smul := by
    intro X Y f c
    change ((c • f)ᘁ)ᘁ = c • (fᘁ)ᘁ
    rw [rightAdjointMate_smul, rightAdjointMate_smul]

instance : (doubleDualFunctor C).Additive where
  map_add := by
    intro X Y f g
    change ((f + g)ᘁ)ᘁ = (fᘁ)ᘁ + (gᘁ)ᘁ
    rw [rightAdjointMate_add, rightAdjointMate_add]

end PropertyF.Ground.Dimensions

namespace PropertyF.Ground.Dimensions
universe v u

/-- The canonical braided double-dual components form a natural isomorphism. -/
def drinfeldNaturalIso (C : Ground.BraidedFusionCategory.{v,u}) :
    𝟭 C.Obj ≅ doubleDualFunctor C.Obj :=
  NatIso.ofComponents (Ground.doubleDualIso C) (fun f => doubleDualIso_natural C f)

/-- The canonical braided fourth-dual components form a natural
isomorphism. Tensor compatibility is not asserted here. -/
def fourthDualNaturalIso (C : Ground.BraidedFusionCategory.{v,u}) :
    𝟭 C.Obj ≅ doubleDualFunctor C.Obj ⋙ doubleDualFunctor C.Obj :=
  NatIso.ofComponents (fourthDualIso C) (fun f => fourthDualIso_natural C f)

end PropertyF.Ground.Dimensions
