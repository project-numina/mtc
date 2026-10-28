module
public import PropertyF.Ground.Dimensions.RootDualPairing
public import PropertyF.Ground.Dimensions.IntrinsicNonzero
public import PropertyF.Ground.Dimensions.PivotalTwist
public import PropertyF.Ground.Fusion.Agreement
public import PropertyF.Ground.Dimensions.PositiveCanonical

/-! # Unit laws for dual tensor comparisons

Right-dual and double-dual tensor comparisons are compatible with the unitors.
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
  let : HasRightDual (𝟙_ C) := RightRigidCategory.rightDual (𝟙_ C)
  let I := 𝟙_ C
  let : HasRightDual I := RightRigidCategory.rightDual I
  let r : Iᘁ ≅ I := by
    change rightDualObject (𝟙_ C) ≅ 𝟙_ C
    exact rightDualUnitIso
  let J := (Xᘁ) ⊗ (Iᘁ)
  let l : (Xᘁ) ⟶ J := ((λ_ X).homᘁ) ≫ (rightDualTensorIso I X).hom
  let s : (Xᘁ) ⟶ J := (ρ_ (Xᘁ)).inv ≫ (Xᘁ) ◁ r.inv
  have hl : l ▷ (I ⊗ X) ≫ ε_ (I ⊗ X) J = (Xᘁ) ◁ (λ_ X).hom ≫ ε_ X (Xᘁ) := by
    have he := rightDualIso_evaluation
      (@HasRightDual.exact C _ _ (I ⊗ X) (RightRigidCategory.rightDual _))
      (ExactPairing.tensor (X₁ := I) (X₂ := X) (Y₁ := Iᘁ) (Y₂ := Xᘁ))
    change (rightDualTensorIso I X).hom ▷ (I ⊗ X) ≫ ε_ (I ⊗ X) J =
      ε_ (I ⊗ X) ((I ⊗ X)ᘁ) at he
    dsimp only [l]
    rw [comp_whiskerRight_assoc, he, rightAdjointMate_comp_evaluation]
  have hs : s ▷ (I ⊗ X) ≫ ε_ (I ⊗ X) J = (Xᘁ) ◁ (λ_ X).hom ≫ ε_ X (Xᘁ) := by
    have he := rightDualIso_inv_evaluation
      (@HasRightDual.exact C _ _ I (RightRigidCategory.rightDual I))
      (inferInstance : ExactPairing I I)
    change r.inv ▷ I ≫ ε_ I (Iᘁ) = ε_ I I at he
    change ((ρ_ (Xᘁ)).inv ≫ (Xᘁ) ◁ r.inv) ▷ (I ⊗ X) ≫
      (𝟙 _ ⊗≫ (Xᘁ) ◁ (ε_ I (Iᘁ) ▷ X) ⊗≫ ε_ X (Xᘁ)) = _
    calc
      _ = 𝟙 _ ⊗≫ (Xᘁ : C) ◁ ((r.inv ▷ I ≫ ε_ I (Iᘁ)) ▷ X) ⊗≫ ε_ X (Xᘁ) := by
        simp only [comp_whiskerRight, whiskerLeft_comp]
        monoidal
      _ = 𝟙 _ ⊗≫ (Xᘁ : C) ◁ (ε_ I I ▷ X) ⊗≫ ε_ X (Xᘁ) := by rw [he]
      _ = _ := by
        change 𝟙 _ ⊗≫ (Xᘁ : C) ◁ ((ρ_ I).hom ▷ X) ⊗≫ ε_ X (Xᘁ) = _
        monoidal
  have h : l ▷ (I ⊗ X) ≫ ε_ (I ⊗ X) J = s ▷ (I ⊗ X) ≫ ε_ (I ⊗ X) J := hl.trans hs.symm
  let : HasRightDual (I ⊗ X) := { rightDual := J, exact := ExactPairing.tensor }
  exact evaluation_ext h
/-- Right dual tensor comparison is compatible with the right unitor. -/
theorem rightDualTensorIso_unit_right (X : C) :
    letI : HasRightDual (𝟙_ C) := RightRigidCategory.rightDual (𝟙_ C)
    ((ρ_ X).homᘁ) ≫ (rightDualTensorIso X (𝟙_ C)).hom =
      (λ_ (Xᘁ)).inv ≫ ((rightDualUnitIso (C := C)).inv ▷ (Xᘁ)) := by
  let : HasRightDual (𝟙_ C) := RightRigidCategory.rightDual (𝟙_ C)
  let I := 𝟙_ C
  let : HasRightDual I := RightRigidCategory.rightDual I
  let r : Iᘁ ≅ I := by
    change rightDualObject (𝟙_ C) ≅ 𝟙_ C
    exact rightDualUnitIso
  let J := (Iᘁ) ⊗ (Xᘁ)
  let l : (Xᘁ) ⟶ J := ((ρ_ X).homᘁ) ≫ (rightDualTensorIso X I).hom
  let s : (Xᘁ) ⟶ J := (λ_ (Xᘁ)).inv ≫ r.inv ▷ (Xᘁ)
  have hl : l ▷ (X ⊗ I) ≫ ε_ (X ⊗ I) J = (Xᘁ) ◁ (ρ_ X).hom ≫ ε_ X (Xᘁ) := by
    have he := rightDualIso_evaluation
      (@HasRightDual.exact C _ _ (X ⊗ I) (RightRigidCategory.rightDual _))
      (ExactPairing.tensor (X₁ := X) (X₂ := I) (Y₁ := Xᘁ) (Y₂ := Iᘁ))
    change (rightDualTensorIso X I).hom ▷ (X ⊗ I) ≫ ε_ (X ⊗ I) J =
      ε_ (X ⊗ I) ((X ⊗ I)ᘁ) at he
    dsimp only [l]
    rw [comp_whiskerRight_assoc, he, rightAdjointMate_comp_evaluation]
  have hs : s ▷ (X ⊗ I) ≫ ε_ (X ⊗ I) J = (Xᘁ) ◁ (ρ_ X).hom ≫ ε_ X (Xᘁ) := by
    have he := rightDualIso_inv_evaluation
      (@HasRightDual.exact C _ _ I (RightRigidCategory.rightDual I))
      (inferInstance : ExactPairing I I)
    change r.inv ▷ I ≫ ε_ I (Iᘁ) = ε_ I I at he
    change ((λ_ (Xᘁ)).inv ≫ r.inv ▷ (Xᘁ)) ▷ (X ⊗ I) ≫
      (𝟙 _ ⊗≫ (Iᘁ) ◁ (ε_ X (Xᘁ) ▷ I) ⊗≫ ε_ I (Iᘁ)) = _
    calc
      _ = 𝟙 _ ⊗≫ ((r.inv ▷ ((Xᘁ ⊗ X) ⊗ I)) ≫
        (Iᘁ : C) ◁ (ε_ X (Xᘁ) ▷ I)) ⊗≫ ε_ I (Iᘁ) := by
          simp only [comp_whiskerRight]
          monoidal
      _ = 𝟙 _ ⊗≫ ((I : C) ◁ (ε_ X (Xᘁ) ▷ I) ≫
        r.inv ▷ ((𝟙_ C) ⊗ I)) ⊗≫ ε_ I (Iᘁ) := by
          rw [← whisker_exchange]
      _ = 𝟙 _ ⊗≫ (ε_ X (Xᘁ) ▷ I) ⊗≫ (r.inv ▷ I ≫ ε_ I (Iᘁ)) := by monoidal
      _ = 𝟙 _ ⊗≫ (ε_ X (Xᘁ) ▷ I) ⊗≫ ε_ I I := by rw [he]
      _ = _ := by
        change 𝟙 _ ⊗≫ (ε_ X (Xᘁ) ▷ I) ⊗≫ (ρ_ I).hom = _
        monoidal
  have h : l ▷ (X ⊗ I) ≫ ε_ (X ⊗ I) J = s ▷ (X ⊗ I) ≫ ε_ (X ⊗ I) J := hl.trans hs.symm
  let : HasRightDual (X ⊗ I) := { rightDual := J, exact := ExactPairing.tensor }
  exact evaluation_ext h

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
  have hs : S.inv ≫ ((Xᘁ) ◁ r.inv)ᘁ = ((r.invᘁ) ▷ ((Xᘁ)ᘁ)) ≫ S₀.inv := by
    simpa only [rightAdjointMate_id, id_tensorHom, tensorHom_id] using
      (rightDualTensorIso_inv_natural (𝟙 (Xᘁ)) r.inv).symm
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
    exact ((rightDualIsoMap r).hom_inv_id)
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
  have hs : S.inv ≫ (r.inv ▷ (Xᘁ))ᘁ = (((Xᘁ)ᘁ) ◁ (r.invᘁ)) ≫ S₀.inv := by
    simpa only [rightAdjointMate_id, id_tensorHom, tensorHom_id] using
      (rightDualTensorIso_inv_natural r.inv (𝟙 (Xᘁ))).symm
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
    exact ((rightDualIsoMap r).hom_inv_id)
  simp only [Category.assoc]
  slice_lhs 2 3 => rw [← whiskerLeft_comp, hc, whiskerLeft_id]
  simpa only [Category.id_comp, Category.comp_id, Category.assoc] using hS'

end PropertyF.Ground.Dimensions

end
