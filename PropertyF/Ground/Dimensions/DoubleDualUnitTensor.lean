module
public import PropertyF.Ground.Dimensions.FourthDualUnit
public import PropertyF.Ground.Dimensions.DimensionCharacter
public import PropertyF.Ground.Integrate.CharacterReality
public import PropertyF.Ground.Modular.SMatrix
public import PropertyF.Ground.Dimensions.SimpleScalars
public import PropertyF.Ground.Fusion.Agreement

/-! # Unit laws for dual tensor comparisons

Right-dual and double-dual tensor comparisons are compatible with the unitors.

## Main results

* `rightDualTensorIso_unit_left`: relates the right-dual comparison to the left unitor.
* `doubleDualTensorIso_unit_right`: establishes the corresponding right unit law for double duals.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.Dimensions
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [RightRigidCategory C]
set_option backward.isDefEq.respectTransparency false in
/-- Right dual tensor comparison is compatible with the left unitor. -/
theorem rightDualTensorIso_unit_left (X : C) :
    letI : HasRightDual (𝟙_ C) := RightRigidCategory.rightDual (𝟙_ C)
    ((λ_ X).homᘁ) ≫ (rightDualTensorIso (𝟙_ C) X).hom =
      (ρ_ (Xᘁ)).inv ≫ ((Xᘁ) ◁ (rightDualUnitIso (C := C)).inv) := by
  let I := 𝟙_ C
  let : HasRightDual I := RightRigidCategory.rightDual I
  let r : Iᘁ ≅ I := rightDualUnitIso
  have he := rightDualIso_inv_evaluation
    (@HasRightDual.exact C _ _ I (RightRigidCategory.rightDual I))
    (inferInstance : ExactPairing I I)
  change r.inv ▷ I ≫ ε_ I (Iᘁ) = ε_ I I at he
  apply evaluation_ext (X := I ⊗ X)
  simp only [comp_whiskerRight_assoc]
  rw [rightDualTensorIso_evaluation I X, rightAdjointMate_comp_evaluation,
    ← comp_whiskerRight_assoc]
  change _ = ((ρ_ (Xᘁ)).inv ≫ (Xᘁ) ◁ r.inv) ▷ (I ⊗ X) ≫
    (𝟙 _ ⊗≫ (Xᘁ) ◁ (ε_ I (Iᘁ) ▷ X) ⊗≫ ε_ X (Xᘁ))
  calc
    _ = 𝟙 _ ⊗≫ (Xᘁ : C) ◁ ((r.inv ▷ I ≫ ε_ I (Iᘁ)) ▷ X) ⊗≫ ε_ X (Xᘁ) := by
      rw [he]
      change (Xᘁ) ◁ (λ_ X).hom ≫ ε_ X (Xᘁ) =
        𝟙 _ ⊗≫ (Xᘁ : C) ◁ ((ρ_ I).hom ▷ X) ⊗≫ ε_ X (Xᘁ)
      monoidal
    _ = _ := by
      simp only [comp_whiskerRight, whiskerLeft_comp]
      monoidal
/-- Right dual tensor comparison is compatible with the right unitor. -/
theorem rightDualTensorIso_unit_right (X : C) :
    letI : HasRightDual (𝟙_ C) := RightRigidCategory.rightDual (𝟙_ C)
    ((ρ_ X).homᘁ) ≫ (rightDualTensorIso X (𝟙_ C)).hom =
      (λ_ (Xᘁ)).inv ≫ ((rightDualUnitIso (C := C)).inv ▷ (Xᘁ)) := by
  let I := 𝟙_ C
  let : HasRightDual I := RightRigidCategory.rightDual I
  let r : Iᘁ ≅ I := rightDualUnitIso
  have he := rightDualIso_inv_evaluation
    (@HasRightDual.exact C _ _ I (RightRigidCategory.rightDual I))
    (inferInstance : ExactPairing I I)
  change r.inv ▷ I ≫ ε_ I (Iᘁ) = ε_ I I at he
  apply evaluation_ext (X := X ⊗ I)
  simp only [comp_whiskerRight_assoc]
  rw [rightDualTensorIso_evaluation X I, rightAdjointMate_comp_evaluation]
  change _ = ((λ_ (Xᘁ)).inv ≫ r.inv ▷ (Xᘁ)) ▷ (X ⊗ I) ≫
    (𝟙 _ ⊗≫ (Iᘁ) ◁ (ε_ X (Xᘁ) ▷ I) ⊗≫ ε_ I (Iᘁ))
  symm
  calc
    _ = 𝟙 _ ⊗≫ ((r.inv ▷ ((Xᘁ ⊗ X) ⊗ I)) ≫
      (Iᘁ : C) ◁ (ε_ X (Xᘁ) ▷ I)) ⊗≫ ε_ I (Iᘁ) := by
        simp only [comp_whiskerRight]
        monoidal
    _ = 𝟙 _ ⊗≫ ((I : C) ◁ (ε_ X (Xᘁ) ▷ I) ≫
      r.inv ▷ ((𝟙_ C) ⊗ I)) ⊗≫ ε_ I (Iᘁ) := by rw [← whisker_exchange]
    _ = 𝟙 _ ⊗≫ (ε_ X (Xᘁ) ▷ I) ⊗≫ (r.inv ▷ I ≫ ε_ I (Iᘁ)) := by monoidal
    _ = _ := by
      rw [he]
      change 𝟙 _ ⊗≫ (ε_ X (Xᘁ) ▷ I) ⊗≫ (ρ_ I).hom = _
      monoidal

end PropertyF.Ground.Dimensions

end

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.Dimensions
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [RightRigidCategory C]
set_option backward.isDefEq.respectTransparency false in
/-- The canonical double-dual tensor comparison is left-unital. -/
theorem doubleDualTensorIso_unit_left (X : C) :
    letI : HasRightDual (𝟙_ C) := RightRigidCategory.rightDual (𝟙_ C)
    letI : HasRightDual ((𝟙_ C)ᘁ) := RightRigidCategory.rightDual ((𝟙_ C)ᘁ)
    (doubleDualUnitIso (C := C)).hom ▷ ((Xᘁ)ᘁ) ≫
      (doubleDualTensorIso (𝟙_ C) X).hom ≫ (((λ_ X).homᘁ)ᘁ) = (λ_ ((Xᘁ)ᘁ)).hom := by
  let I := 𝟙_ C
  let : HasRightDual I := RightRigidCategory.rightDual I
  let : HasRightDual (Iᘁ) := RightRigidCategory.rightDual (Iᘁ)
  let r : Iᘁ ≅ I := rightDualUnitIso
  let R := rightDualTensorIso I X
  let S := rightDualTensorIso (Xᘁ) (Iᘁ)
  let S₀ := rightDualTensorIso (Xᘁ) I
  have hR' := congrArg (fun f => rightAdjointMate f) (rightDualTensorIso_unit_left X)
  simp only [comp_rightAdjointMate] at hR'
  have hs : S.inv ≫ ((Xᘁ) ◁ r.inv)ᘁ = ((r.invᘁ) ▷ ((Xᘁ)ᘁ)) ≫ S₀.inv := by
    simpa only [rightAdjointMate_id, id_tensorHom, tensorHom_id] using
      (rightDualTensorIso_inv_natural (𝟙 (Xᘁ)) r.inv).symm
  have hS : ((ρ_ (Xᘁ)).homᘁ) ≫ S₀.hom = (λ_ ((Xᘁ)ᘁ)).inv ≫ r.inv ▷ ((Xᘁ)ᘁ) :=
    rightDualTensorIso_unit_right (Xᘁ)
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
  have hc : (r.homᘁ) ≫ (r.invᘁ) = 𝟙 (Iᘁ) := (rightDualIsoMap r).hom_inv_id
  simp only [Category.assoc]
  slice_lhs 2 3 => rw [← comp_whiskerRight, hc, id_whiskerRight]
  simpa only [Category.id_comp, Category.comp_id, Category.assoc] using hS'

set_option backward.isDefEq.respectTransparency false in
/-- The canonical double-dual tensor comparison is right-unital. -/
theorem doubleDualTensorIso_unit_right (X : C) :
    letI : HasRightDual (𝟙_ C) := RightRigidCategory.rightDual (𝟙_ C)
    letI : HasRightDual ((𝟙_ C)ᘁ) := RightRigidCategory.rightDual ((𝟙_ C)ᘁ)
    ((Xᘁ)ᘁ) ◁ (doubleDualUnitIso (C := C)).hom ≫
      (doubleDualTensorIso X (𝟙_ C)).hom ≫ (((ρ_ X).homᘁ)ᘁ) = (ρ_ ((Xᘁ)ᘁ)).hom := by
  let I := 𝟙_ C
  let : HasRightDual I := RightRigidCategory.rightDual I
  let : HasRightDual (Iᘁ) := RightRigidCategory.rightDual (Iᘁ)
  let r : Iᘁ ≅ I := rightDualUnitIso
  let R := rightDualTensorIso X I
  let S := rightDualTensorIso (Iᘁ) (Xᘁ)
  let S₀ := rightDualTensorIso I (Xᘁ)
  have hR' := congrArg (fun f => rightAdjointMate f) (rightDualTensorIso_unit_right X)
  simp only [comp_rightAdjointMate] at hR'
  have hs : S.inv ≫ (r.inv ▷ (Xᘁ))ᘁ = (((Xᘁ)ᘁ) ◁ (r.invᘁ)) ≫ S₀.inv := by
    simpa only [rightAdjointMate_id, id_tensorHom, tensorHom_id] using
      (rightDualTensorIso_inv_natural r.inv (𝟙 (Xᘁ))).symm
  have hS : ((λ_ (Xᘁ)).homᘁ) ≫ S₀.hom = (ρ_ ((Xᘁ)ᘁ)).inv ≫ ((Xᘁ)ᘁ) ◁ r.inv :=
    rightDualTensorIso_unit_left (Xᘁ)
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
  have hc : (r.homᘁ) ≫ (r.invᘁ) = 𝟙 (Iᘁ) := (rightDualIsoMap r).hom_inv_id
  simp only [Category.assoc]
  slice_lhs 2 3 => rw [← whiskerLeft_comp, hc, whiskerLeft_id]
  simpa only [Category.id_comp, Category.comp_id, Category.assoc] using hS'

end PropertyF.Ground.Dimensions

end
