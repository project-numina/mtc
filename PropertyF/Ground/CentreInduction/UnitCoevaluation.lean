module
public import PropertyF.Ground.CentreInduction.UnitSummand
public import PropertyF.Ground.Dimensions.DualCoherence

/-! Coevaluation transported along an isomorphism with the unit. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.CentreInduction
universe v u

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- An object isomorphic to the tensor unit has its coevaluation normalized
by the induced identification of its right dual with the unit. -/
theorem coevaluation_iso_unit (C : BraidedFusionCategory.{v,u})
    (A : C.Obj) (e : A ≅ 𝟙_ C.Obj) :
    η_ A Aᘁ ≫ (e.hom ⊗ₘ (Dimensions.rightDualIsoMap e.symm ≪≫
      Dimensions.rightDualUnitIso).hom) = (ρ_ (𝟙_ C.Obj)).inv := by
  letI : HasRightDual (𝟙_ C.Obj) := RightRigidCategory.rightDual (𝟙_ C.Obj)
  let p : ExactPairing (𝟙_ C.Obj) ((𝟙_ C.Obj)ᘁ) := HasRightDual.exact
  let q : ExactPairing (𝟙_ C.Obj) (𝟙_ C.Obj) := exactPairingUnit
  have hu := Dimensions.coevaluation_rightDualIso p q
  have he := coevaluation_comp_rightAdjointMate e.inv
  change η_ A Aᘁ ≫ A ◁ (e.invᘁ) = η_ (𝟙_ C.Obj) ((𝟙_ C.Obj)ᘁ) ≫ e.inv ▷ _ at he
  change η_ (𝟙_ C.Obj) ((𝟙_ C.Obj)ᘁ) ≫
    (𝟙_ C.Obj) ◁ Dimensions.rightDualUnitIso.hom = (ρ_ (𝟙_ C.Obj)).inv at hu
  simp only [Iso.trans_hom, Dimensions.rightDualIsoMap, Iso.symm_inv, Iso.symm_hom, Category.assoc,
    tensorHom_def', whiskerLeft_comp]
  rw [← Category.assoc, he]
  simp only [Category.assoc]
  rw [← whisker_exchange_assoc]
  have hh : (e.inv ▷ (𝟙_ C.Obj)) ≫ (e.hom ▷ (𝟙_ C.Obj)) = 𝟙 _ := by
    rw [← comp_whiskerRight, Iso.inv_hom_id, id_whiskerRight]
  calc
    _ = (η_ (𝟙_ C.Obj) ((𝟙_ C.Obj)ᘁ) ≫
      (𝟙_ C.Obj) ◁ Dimensions.rightDualUnitIso.hom) ≫
      ((e.inv ▷ (𝟙_ C.Obj)) ≫ (e.hom ▷ (𝟙_ C.Obj))) := by simp only [Category.assoc]
    _ = _ := by rw [hh, Category.comp_id]; exact hu

end PropertyF.Ground.CentreInduction
