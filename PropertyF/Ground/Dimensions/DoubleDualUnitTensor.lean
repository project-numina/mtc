module
public import PropertyF.Ground.Dimensions.RightDualUnitTensor

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.Dimensions
universe v u
set_option backward.isDefEq.respectTransparency false in
/-- The canonical double-dual tensor comparison is left-unital. -/
theorem doubleDualTensorIso_unit_left {C : Type u} [Category.{v} C]
    [MonoidalCategory C] [RightRigidCategory C] (X : C) :
    letI : HasRightDual (𝟙_ C) := RightRigidCategory.rightDual (𝟙_ C)
    letI : HasRightDual ((𝟙_ C)ᘁ) := RightRigidCategory.rightDual ((𝟙_ C)ᘁ)
    (doubleDualUnitIso (C := C)).hom ▷ ((Xᘁ)ᘁ) ≫
      (doubleDualTensorIso (𝟙_ C) X).hom ≫ (((λ_ X).homᘁ)ᘁ) = (λ_ ((Xᘁ)ᘁ)).hom := by
  let I := 𝟙_ C
  let : HasRightDual I := RightRigidCategory.rightDual I
  let : HasRightDual (Iᘁ) := RightRigidCategory.rightDual (Iᘁ)
  let r : Iᘁ ≅ I := by
    change rightDualObject (𝟙_ C) ≅ 𝟙_ C
    exact rightDualUnitIso
  let R := rightDualTensorIso I X
  let S := rightDualTensorIso (Xᘁ) (Iᘁ)
  let S₀ := rightDualTensorIso (Xᘁ) I
  have hR : ((λ_ X).homᘁ) ≫ R.hom = (ρ_ (Xᘁ)).inv ≫ (Xᘁ) ◁ r.inv := by
    exact rightDualTensorIso_unit_left X
  have hR' := congrArg (fun f => rightAdjointMate f) hR
  simp only [comp_rightAdjointMate] at hR'
  have hn := rightDualTensorIso_natural (𝟙 (Xᘁ)) r.inv
  simp only [rightAdjointMate_id, id_tensorHom] at hn
  have hs : S.inv ≫ ((Xᘁ) ◁ r.inv)ᘁ = ((r.invᘁ) ▷ ((Xᘁ)ᘁ)) ≫ S₀.inv := by
    apply (cancel_mono S₀.hom).1
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [hn]
    simp [← Category.assoc]
  have hS : ((ρ_ (Xᘁ)).homᘁ) ≫ S₀.hom = (λ_ ((Xᘁ)ᘁ)).inv ≫ r.inv ▷ ((Xᘁ)ᘁ) := by
    exact rightDualTensorIso_unit_right (Xᘁ)
  have hS' : r.inv ▷ ((Xᘁ)ᘁ) ≫ S₀.inv ≫ ((ρ_ (Xᘁ)).invᘁ) = (λ_ ((Xᘁ)ᘁ)).hom := by
    apply (cancel_epi (λ_ ((Xᘁ)ᘁ)).inv).1
    simp only [Iso.inv_hom_id]
    slice_lhs 1 2 => rw [← hS]
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id,
      ← comp_rightAdjointMate, Iso.inv_hom_id, rightAdjointMate_id]
  change (r.inv ≫ (r.homᘁ)) ▷ ((Xᘁ)ᘁ) ≫
    (S.inv ≫ (R.homᘁ)) ≫ (((λ_ X).homᘁ)ᘁ) = (λ_ ((Xᘁ)ᘁ)).hom
  simp only [comp_whiskerRight, Category.assoc]
  rw [hR']
  slice_lhs 3 4 => rw [hs]
  have hc : (r.homᘁ) ≫ (r.invᘁ) = 𝟙 (Iᘁ) := by
    have h := (rightDualIsoMap r).hom_inv_id
    exact h
  simp only [Category.assoc]
  slice_lhs 2 3 => rw [← comp_whiskerRight, hc, id_whiskerRight]
  simpa only [Category.id_comp, Category.comp_id, Category.assoc] using hS' 

set_option backward.isDefEq.respectTransparency false in
/-- The canonical double-dual tensor comparison is right-unital. -/
theorem doubleDualTensorIso_unit_right {C : Type u} [Category.{v} C]
    [MonoidalCategory C] [RightRigidCategory C] (X : C) :
    letI : HasRightDual (𝟙_ C) := RightRigidCategory.rightDual (𝟙_ C)
    letI : HasRightDual ((𝟙_ C)ᘁ) := RightRigidCategory.rightDual ((𝟙_ C)ᘁ)
    ((Xᘁ)ᘁ) ◁ (doubleDualUnitIso (C := C)).hom ≫
      (doubleDualTensorIso X (𝟙_ C)).hom ≫ (((ρ_ X).homᘁ)ᘁ) = (ρ_ ((Xᘁ)ᘁ)).hom := by
  let I := 𝟙_ C
  let : HasRightDual I := RightRigidCategory.rightDual I
  let : HasRightDual (Iᘁ) := RightRigidCategory.rightDual (Iᘁ)
  let r : Iᘁ ≅ I := by
    change rightDualObject (𝟙_ C) ≅ 𝟙_ C
    exact rightDualUnitIso
  let R := rightDualTensorIso X I
  let S := rightDualTensorIso (Iᘁ) (Xᘁ)
  let S₀ := rightDualTensorIso I (Xᘁ)
  have hR : ((ρ_ X).homᘁ) ≫ R.hom = (λ_ (Xᘁ)).inv ≫ r.inv ▷ (Xᘁ) := by
    exact rightDualTensorIso_unit_right X
  have hR' := congrArg (fun f => rightAdjointMate f) hR
  simp only [comp_rightAdjointMate] at hR'
  have hn := rightDualTensorIso_natural r.inv (𝟙 (Xᘁ))
  simp only [rightAdjointMate_id, tensorHom_id] at hn
  have hs : S.inv ≫ (r.inv ▷ (Xᘁ))ᘁ = (((Xᘁ)ᘁ) ◁ (r.invᘁ)) ≫ S₀.inv := by
    apply (cancel_mono S₀.hom).1
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [hn]
    simp [← Category.assoc]
  have hS : ((λ_ (Xᘁ)).homᘁ) ≫ S₀.hom = (ρ_ ((Xᘁ)ᘁ)).inv ≫ ((Xᘁ)ᘁ) ◁ r.inv := by
    exact rightDualTensorIso_unit_left (Xᘁ)
  have hS' : ((Xᘁ)ᘁ) ◁ r.inv ≫ S₀.inv ≫ ((λ_ (Xᘁ)).invᘁ) = (ρ_ ((Xᘁ)ᘁ)).hom := by
    apply (cancel_epi (ρ_ ((Xᘁ)ᘁ)).inv).1
    simp only [Iso.inv_hom_id]
    slice_lhs 1 2 => rw [← hS]
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id,
      ← comp_rightAdjointMate, Iso.inv_hom_id, rightAdjointMate_id]
  change ((Xᘁ)ᘁ) ◁ (r.inv ≫ (r.homᘁ)) ≫
    (S.inv ≫ (R.homᘁ)) ≫ (((ρ_ X).homᘁ)ᘁ) = (ρ_ ((Xᘁ)ᘁ)).hom
  simp only [whiskerLeft_comp, Category.assoc]
  rw [hR']
  slice_lhs 3 4 => rw [hs]
  have hc : (r.homᘁ) ≫ (r.invᘁ) = 𝟙 (Iᘁ) := by
    have h := (rightDualIsoMap r).hom_inv_id
    exact h
  simp only [Category.assoc]
  slice_lhs 2 3 => rw [← whiskerLeft_comp, hc, whiskerLeft_id]
  simpa only [Category.id_comp, Category.comp_id, Category.assoc] using hS'

end PropertyF.Ground.Dimensions
