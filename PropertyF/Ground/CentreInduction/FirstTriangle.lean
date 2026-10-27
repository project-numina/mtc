module
public import PropertyF.Ground.CentreInduction.UnitCandidate
public import PropertyF.Ground.CentreInduction.UnitCoevaluation
public import PropertyF.Ground.CentreInduction.UnitTest

/-! The first underlying triangle for the proposed centre adjunction. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.BraidedCategory
namespace PropertyF.Ground.CentreInduction
universe v u

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The underlying maps proposed for the induction unit and counit satisfy
the first triangle identity. -/
theorem unitCandidate_counit (C : BraidedFusionCategory.{v,u})
    (Z : CategoryTheory.Center C.Obj) :
    unitCandidate C Z ≫ (underlyingCounit C).app Z.1 = 𝟙 Z.1 := by
  rw [unitCandidate_counit_component]
  let A := simples C (unitIndex C)
  let e : A ≅ 𝟙_ C.Obj := Classical.choice (unitIndex_iso C)
  let d : Aᘁ ≅ 𝟙_ C.Obj := Dimensions.rightDualIsoMap e.symm ≪≫ Dimensions.rightDualUnitIso
  have hn := Z.2.naturality e.hom
  have hc := coevaluation_iso_unit C A e
  change (η_ A Aᘁ ≫ (e.hom ⊗ₘ d.hom)) = (ρ_ (𝟙_ C.Obj)).inv at hc
  change ((ρ_ Z.1).inv ≫ (Z.1 ◁ η_ A Aᘁ) ≫ (α_ Z.1 A Aᘁ).inv ≫
    ((Z.2.β A).hom ▷ Aᘁ)) ≫
      (((e ⊗ᵢ Iso.refl Z.1) ⊗ᵢ d) ≪≫
        ((λ_ Z.1) ⊗ᵢ Iso.refl (𝟙_ C.Obj)) ≪≫ ρ_ Z.1).hom = 𝟙 Z.1
  simp only [Iso.trans_hom, tensorIso_hom, Iso.refl_hom, tensorHom_def,
    whiskerLeft_id, Category.comp_id, Category.assoc]
  rw [← comp_whiskerRight_assoc, ← hn]
  rw [comp_whiskerRight_assoc, ← associator_inv_naturality_middle_assoc]
  rw [← whiskerLeft_comp_assoc]
  rw [halfBraiding_unit C Z]
  simp only [comp_whiskerRight, Category.assoc]
  rw [triangle_assoc_comp_right_assoc, ← whisker_exchange_assoc]
  simp only [← comp_whiskerRight_assoc, Iso.inv_hom_id, id_whiskerRight, Category.id_comp]
  have hunit : η_ A Aᘁ ≫ (e.hom ▷ Aᘁ) ≫ (λ_ Aᘁ).hom ≫ d.hom = 𝟙 (𝟙_ C.Obj) := by
    rw [← leftUnitor_naturality, ← tensorHom_def_assoc, ← Category.assoc, hc]
    monoidal_coherence
  simp only [← whiskerLeft_comp_assoc]
  simp only [Category.assoc] at hunit ⊢
  rw [hunit, whiskerLeft_id]
  simp

end PropertyF.Ground.CentreInduction
