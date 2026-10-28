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
variable (X : C)
local instance : HasRightDual (𝟙_ C) := RightRigidCategory.rightDual _
set_option backward.isDefEq.respectTransparency false in
/-- Right dual tensor comparison is compatible with the left unitor. -/
theorem rightDualTensorIso_unit_left :
    ((λ_ X).homᘁ) ≫ (rightDualTensorIso (𝟙_ C) X).hom =
      (ρ_ (Xᘁ)).inv ≫ ((Xᘁ) ◁ (rightDualUnitIso (C := C)).inv) := by
  let I := 𝟙_ C
  let r : Iᘁ ≅ I := rightDualUnitIso
  apply evaluation_ext (X := I ⊗ X)
  simp only [comp_whiskerRight_assoc]
  rw [rightDualTensorIso_evaluation I X, rightAdjointMate_comp_evaluation,
    tensorPairing_evaluation_whiskerLeft (p := (inferInstance : ExactPairing I I))
      (q := @HasRightDual.exact C _ _ I (RightRigidCategory.rightDual I))
      (r := HasRightDual.exact) r.inv (rightDualIso_inv_evaluation
        (@HasRightDual.exact C _ _ I (RightRigidCategory.rightDual I))
        (inferInstance : ExactPairing I I)),
    ExactPairing.tensor_evaluation,
    show @ExactPairing.evaluation C _ _ I I (inferInstance : ExactPairing I I) =
      (ρ_ I).hom from rfl]
  monoidal
/-- Right dual tensor comparison is compatible with the right unitor. -/
theorem rightDualTensorIso_unit_right :
    ((ρ_ X).homᘁ) ≫ (rightDualTensorIso X (𝟙_ C)).hom =
      (λ_ (Xᘁ)).inv ≫ ((rightDualUnitIso (C := C)).inv ▷ (Xᘁ)) := by
  let I := 𝟙_ C
  let r : Iᘁ ≅ I := rightDualUnitIso
  apply evaluation_ext (X := X ⊗ I)
  simp only [comp_whiskerRight_assoc]
  rw [rightDualTensorIso_evaluation X I, rightAdjointMate_comp_evaluation]
  change _ = ((λ_ (Xᘁ)).inv ≫ r.inv ▷ (Xᘁ)) ▷ (X ⊗ I) ≫ ε_ (X ⊗ I) ((Iᘁ) ⊗ (Xᘁ))
  rw [comp_whiskerRight_assoc,
    tensorPairing_evaluation_whiskerRight (p := HasRightDual.exact) (q := (inferInstance : ExactPairing I I))
      (r := @HasRightDual.exact C _ _ I (RightRigidCategory.rightDual I)) r.inv
      (rightDualIso_inv_evaluation (@HasRightDual.exact C _ _ I (RightRigidCategory.rightDual I))
        (inferInstance : ExactPairing I I)),
    ExactPairing.tensor_evaluation,
    show @ExactPairing.evaluation C _ _ I I (inferInstance : ExactPairing I I) =
      (ρ_ I).hom from rfl]
  monoidal

end PropertyF.Ground.Dimensions

end

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.Dimensions
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [RightRigidCategory C]
variable (X : C)
local instance : HasRightDual (𝟙_ C) := RightRigidCategory.rightDual _
local instance : HasRightDual ((𝟙_ C)ᘁ) := RightRigidCategory.rightDual _
set_option backward.isDefEq.respectTransparency false in
/-- The canonical double-dual tensor comparison is left-unital. -/
theorem doubleDualTensorIso_unit_left :
    (doubleDualUnitIso (C := C)).hom ▷ ((Xᘁ)ᘁ) ≫
      (doubleDualTensorIso (𝟙_ C) X).hom ≫ (((λ_ X).homᘁ)ᘁ) = (λ_ ((Xᘁ)ᘁ)).hom := by
  let I := 𝟙_ C
  let r : Iᘁ ≅ I := rightDualUnitIso
  let R := rightDualTensorIso I X
  let S := rightDualTensorIso (Xᘁ) (Iᘁ)
  let S₀ := rightDualTensorIso (Xᘁ) I
  have hR' := congrArg (fun f => rightAdjointMate f) (rightDualTensorIso_unit_left X)
  simp only [comp_rightAdjointMate] at hR'
  have hs : S.inv ≫ ((Xᘁ) ◁ r.inv)ᘁ = ((r.invᘁ) ▷ ((Xᘁ)ᘁ)) ≫ S₀.inv := by
    simpa only [rightAdjointMate_id, id_tensorHom, tensorHom_id] using
      (rightDualTensorIso_inv_natural (𝟙 (Xᘁ)) r.inv).symm
  have hS' : r.inv ▷ ((Xᘁ)ᘁ) ≫ S₀.inv ≫ ((ρ_ (Xᘁ)).invᘁ) = (λ_ ((Xᘁ)ᘁ)).hom := by
    rw [← Category.assoc]
    refine (Iso.comp_inv_eq (rightDualIsoMap (ρ_ (Xᘁ)))).2 ((Iso.comp_inv_eq S₀).2 ?_)
    simpa only [rightDualIsoMap, Category.assoc] using
      (Iso.inv_comp_eq (λ_ ((Xᘁ)ᘁ))).1 (rightDualTensorIso_unit_right (Xᘁ)).symm
  change (r.inv ≫ (r.homᘁ)) ▷ ((Xᘁ)ᘁ) ≫
    (S.inv ≫ (R.homᘁ)) ≫ (((λ_ X).homᘁ)ᘁ) = (λ_ ((Xᘁ)ᘁ)).hom
  simp only [comp_whiskerRight, Category.assoc]
  rw [hR', reassoc_of% hs,
    ← comp_whiskerRight_assoc (r.homᘁ) (r.invᘁ), ← comp_rightAdjointMate,
    Iso.inv_hom_id, rightAdjointMate_id, id_whiskerRight, Category.id_comp]
  exact hS'

set_option backward.isDefEq.respectTransparency false in
/-- The canonical double-dual tensor comparison is right-unital. -/
theorem doubleDualTensorIso_unit_right :
    ((Xᘁ)ᘁ) ◁ (doubleDualUnitIso (C := C)).hom ≫
      (doubleDualTensorIso X (𝟙_ C)).hom ≫ (((ρ_ X).homᘁ)ᘁ) = (ρ_ ((Xᘁ)ᘁ)).hom := by
  let I := 𝟙_ C
  let r : Iᘁ ≅ I := rightDualUnitIso
  let R := rightDualTensorIso X I
  let S := rightDualTensorIso (Iᘁ) (Xᘁ)
  let S₀ := rightDualTensorIso I (Xᘁ)
  have hR' := congrArg (fun f => rightAdjointMate f) (rightDualTensorIso_unit_right X)
  simp only [comp_rightAdjointMate] at hR'
  have hs : S.inv ≫ (r.inv ▷ (Xᘁ))ᘁ = (((Xᘁ)ᘁ) ◁ (r.invᘁ)) ≫ S₀.inv := by
    simpa only [rightAdjointMate_id, id_tensorHom, tensorHom_id] using
      (rightDualTensorIso_inv_natural r.inv (𝟙 (Xᘁ))).symm
  have hS' : ((Xᘁ)ᘁ) ◁ r.inv ≫ S₀.inv ≫ ((λ_ (Xᘁ)).invᘁ) = (ρ_ ((Xᘁ)ᘁ)).hom := by
    rw [← Category.assoc]
    refine (Iso.comp_inv_eq (rightDualIsoMap (λ_ (Xᘁ)))).2 ((Iso.comp_inv_eq S₀).2 ?_)
    simpa only [rightDualIsoMap, Category.assoc] using
      (Iso.inv_comp_eq (ρ_ ((Xᘁ)ᘁ))).1 (rightDualTensorIso_unit_left (Xᘁ)).symm
  change ((Xᘁ)ᘁ) ◁ (r.inv ≫ (r.homᘁ)) ≫
    (S.inv ≫ (R.homᘁ)) ≫ (((ρ_ X).homᘁ)ᘁ) = (ρ_ ((Xᘁ)ᘁ)).hom
  simp only [whiskerLeft_comp, Category.assoc]
  rw [hR', reassoc_of% hs,
    ← whiskerLeft_comp_assoc ((Xᘁ)ᘁ) (r.homᘁ) (r.invᘁ), ← comp_rightAdjointMate,
    Iso.inv_hom_id, rightAdjointMate_id, whiskerLeft_id, Category.id_comp]
  exact hS'

end PropertyF.Ground.Dimensions

end
