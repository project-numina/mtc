module
public import PropertyF.Ground.Dimensions.RightDualAssociativity

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.Dimensions
universe v u
set_option backward.isDefEq.respectTransparency false in
/-- The canonical double-dual tensor comparison respects associativity. -/
theorem doubleDualTensorIso_associativity {C : Type u} [Category.{v} C]
    [MonoidalCategory C] [RightRigidCategory C] (X Y Z : C) :
    (doubleDualTensorIso X Y).hom ▷ ((Zᘁ)ᘁ) ≫ (doubleDualTensorIso (X ⊗ Y) Z).hom ≫
      (((α_ X Y Z).homᘁ)ᘁ) =
    (α_ ((Xᘁ)ᘁ) ((Yᘁ)ᘁ) ((Zᘁ)ᘁ)).hom ≫
      ((Xᘁ)ᘁ) ◁ (doubleDualTensorIso Y Z).hom ≫ (doubleDualTensorIso X (Y ⊗ Z)).hom := by
  simp only [doubleDualTensorIso, Iso.trans_hom, Iso.symm_hom, rightDualIsoMap,
    comp_whiskerRight, whiskerLeft_comp, Category.assoc]
  have hmove1 : (rightDualTensorIso X Y).homᘁ ▷ ((Zᘁ)ᘁ) ≫
      (rightDualTensorIso (Zᘁ) ((X ⊗ Y)ᘁ)).inv =
    (rightDualTensorIso (Zᘁ) ((Yᘁ) ⊗ (Xᘁ))).inv ≫
      (((Zᘁ) ◁ (rightDualTensorIso X Y).hom)ᘁ) := by
    have h := rightDualTensorIso_natural (𝟙 (Zᘁ)) (rightDualTensorIso X Y).hom
    simp only [rightAdjointMate_id, id_tensorHom, tensorHom_id] at h
    apply (cancel_mono (rightDualTensorIso (Zᘁ) ((X ⊗ Y)ᘁ)).hom).1
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [h]
    simp [← Category.assoc]
  have hmove2 : (rightDualTensorIso ((Zᘁ) ⊗ (Yᘁ)) (Xᘁ)).inv ≫
      (((rightDualTensorIso Y Z).hom ▷ (Xᘁ))ᘁ) =
    ((Xᘁ)ᘁ) ◁ ((rightDualTensorIso Y Z).homᘁ) ≫
      (rightDualTensorIso ((Y ⊗ Z)ᘁ) (Xᘁ)).inv := by
    have h := rightDualTensorIso_natural (rightDualTensorIso Y Z).hom (𝟙 (Xᘁ))
    simp only [rightAdjointMate_id, id_tensorHom, tensorHom_id] at h
    apply (cancel_mono (rightDualTensorIso ((Y ⊗ Z)ᘁ) (Xᘁ)).hom).1
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [h]
    simp [← Category.assoc]
  have hdual := congrArg (fun f => rightAdjointMate f) (rightDualTensorIso_associativity X Y Z)
  simp only [comp_rightAdjointMate] at hdual
  let A := (rightDualTensorIso (Yᘁ) (Xᘁ)).symm ▷ᵢ ((Zᘁ)ᘁ)
  let B := (rightDualTensorIso (Zᘁ) ((Yᘁ) ⊗ (Xᘁ))).symm
  let C₀ := rightDualIsoMap (α_ (Zᘁ) (Yᘁ) (Xᘁ)).symm
  let D := rightDualTensorIso ((Zᘁ) ⊗ (Yᘁ)) (Xᘁ)
  let E := ((Xᘁ)ᘁ) ◁ᵢ rightDualTensorIso (Zᘁ) (Yᘁ)
  let F := α_ ((Xᘁ)ᘁ) ((Yᘁ)ᘁ) ((Zᘁ)ᘁ)
  have heq : D ≪≫ E = C₀ ≪≫ B.symm ≪≫ A.symm ≪≫ F := by
    apply Iso.ext
    simpa only [A, B, C₀, D, E, F, Iso.trans_hom, Iso.symm_hom, Iso.symm_inv, rightDualIsoMap,
      whiskerRightIso_inv, whiskerLeftIso_hom] using
      rightDualTensorIso_associativity (Zᘁ) (Yᘁ) (Xᘁ)
  have hinv := congrArg Iso.inv heq
  simp only [Iso.trans_inv, Iso.symm_inv, Category.assoc] at hinv
  have hrev : A.hom ≫ B.hom = F.hom ≫ E.inv ≫ D.inv ≫ C₀.hom := by
    apply (cancel_epi F.inv).1
    apply (cancel_mono C₀.inv).1
    simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id, Category.comp_id]
    simpa only [Category.assoc] using hinv.symm
  have hrev' : (rightDualTensorIso (Yᘁ) (Xᘁ)).inv ▷ ((Zᘁ)ᘁ) ≫
      (rightDualTensorIso (Zᘁ) ((Yᘁ) ⊗ (Xᘁ))).inv =
    (α_ ((Xᘁ)ᘁ) ((Yᘁ)ᘁ) ((Zᘁ)ᘁ)).hom ≫
      ((Xᘁ)ᘁ) ◁ (rightDualTensorIso (Zᘁ) (Yᘁ)).inv ≫
        (rightDualTensorIso ((Zᘁ) ⊗ (Yᘁ)) (Xᘁ)).inv ≫ ((α_ (Zᘁ) (Yᘁ) (Xᘁ)).invᘁ) := by
    simpa only [A, B, C₀, D, E, F, rightDualIsoMap, Iso.symm_hom,
      whiskerRightIso_hom, whiskerLeftIso_inv] using hrev
  slice_lhs 2 3 => rw [hmove1]
  simp only [Category.assoc]
  slice_lhs 1 2 => rw [hrev']
  simp only [Category.assoc]
  slice_lhs 5 6 => rw [hdual]
  simp only [Category.assoc]
  have hα : ((α_ (Zᘁ) (Yᘁ) (Xᘁ)).invᘁ) ≫ ((α_ (Zᘁ) (Yᘁ) (Xᘁ)).homᘁ) = 𝟙 _ := by
    rw [← comp_rightAdjointMate, Iso.hom_inv_id, rightAdjointMate_id]
  have hβ : (((α_ X Y Z).invᘁ)ᘁ) ≫ (((α_ X Y Z).homᘁ)ᘁ) = 𝟙 _ := by
    have h := (rightDualIsoMap (rightDualIsoMap (α_ X Y Z))).inv_hom_id
    exact h
  slice_lhs 4 5 => rw [hα]
  simp only [Category.id_comp, Category.assoc]
  slice_lhs 6 7 => rw [hβ]
  simp only [Category.comp_id]
  slice_lhs 3 4 => rw [hmove2]
  simp only [Category.assoc]
end PropertyF.Ground.Dimensions
