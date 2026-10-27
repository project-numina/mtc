module
public import PropertyF.Ground.CentreInduction.Underlying
public import PropertyF.Ground.Dimensions.Pivotal

/-! The unit summand of the underlying induction object. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
namespace PropertyF.Ground.CentreInduction
universe v u
attribute [local instance] Abelian.hasFiniteBiproducts

/-- The unit-labelled summand is isomorphic to the middle object. -/
def unitSummandIso (C : BraidedFusionCategory.{v,u}) (X : C.Obj) :
    (simples C (unitIndex C) ⊗ X) ⊗ (simples C (unitIndex C))ᘁ ≅ X := by
  let e : simples C (unitIndex C) ≅ 𝟙_ C.Obj := Classical.choice (unitIndex_iso C)
  let d : (simples C (unitIndex C))ᘁ ≅ 𝟙_ C.Obj :=
    Dimensions.rightDualIsoMap e.symm ≪≫ Dimensions.rightDualUnitIso
  exact ((e ⊗ᵢ Iso.refl X) ⊗ᵢ d) ≪≫ ((λ_ X) ⊗ᵢ Iso.refl (𝟙_ C.Obj)) ≪≫ ρ_ X

set_option backward.isDefEq.respectTransparency false in
/-- Every object is a retract of its underlying induction sum through the
unit-labelled component. -/
def unitSummandRetract (C : BraidedFusionCategory.{v,u}) (X : C.Obj) :
    Retract X (underlying C X) where
  i := (unitSummandIso C X).inv ≫ biproduct.ι (fun i : Fin (rank C) => (simples C i ⊗ X) ⊗ (simples C i)ᘁ) (unitIndex C)
  r := biproduct.π (fun i : Fin (rank C) => (simples C i ⊗ X) ⊗ (simples C i)ᘁ) (unitIndex C) ≫ (unitSummandIso C X).hom
  retract := by simp [underlying, Category.assoc]

end PropertyF.Ground.CentreInduction
