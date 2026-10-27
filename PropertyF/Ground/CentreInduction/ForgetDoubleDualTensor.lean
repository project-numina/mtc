module
public import PropertyF.Ground.CentreInduction.ForgetDualTensor

/-! Tensor coherence for the forgotten double-dual and pivotal components. -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.CentreInduction
universe v u
set_option backward.isDefEq.respectTransparency false
variable (C : BraidedFusionCategory.{v,u}) [RigidCategory (CategoryTheory.Center C.Obj)]

theorem forgetDoubleDualIso_tensor (X Y : CategoryTheory.Center C.Obj) :
    (Dimensions.doubleDualTensorIso X Y).hom.f ≫ (forgetDoubleDualIso C (X ⊗ Y)).hom =
      ((forgetDoubleDualIso C X).hom ⊗ₘ (forgetDoubleDualIso C Y).hom) ≫
        (Dimensions.doubleDualTensorIso X.1 Y.1).hom := by
  simp only [Dimensions.doubleDualTensorIso, Iso.trans_hom, Iso.symm_hom,
    Dimensions.rightDualIsoMap, CategoryTheory.Center.comp_f, Category.assoc,
    forgetDoubleDualIso]
  have hn := forgetDualIso_natural C (rightDualTensorIso X Y).hom
  rw [← Category.assoc ((rightDualTensorIso X Y).homᘁ).f, hn]
  have ht := forgetDualIso_tensor C (Yᘁ) (Xᘁ)
  have ht' : (rightDualTensorIso (Yᘁ) (Xᘁ)).inv.f ≫
      (forgetDualIso C ((Yᘁ) ⊗ (Xᘁ))).hom =
      ((forgetDualIso C (Xᘁ)).hom ⊗ₘ (forgetDualIso C (Yᘁ)).hom) ≫
        (rightDualTensorIso (Yᘁ).1 (Xᘁ).1).inv := by
    apply (cancel_mono (rightDualTensorIso (Yᘁ).1 (Xᘁ).1).hom).1
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [ht]
    simp [← CategoryTheory.Center.comp_f, ← Category.assoc]
  simp only [← Category.assoc]
  rw [ht']
  have ht2 := congrArg (fun m => rightAdjointMate m) (forgetDualIso_tensor C X Y)
  simp only [comp_rightAdjointMate] at ht2
  have hk : (rightDualTensorIso X Y).hom.fᘁ ≫ (forgetDualIso C (X ⊗ Y)).invᘁ =
      (((forgetDualIso C Y).inv ⊗ₘ (forgetDualIso C X).inv)ᘁ) ≫
        (rightDualTensorIso X.1 Y.1).homᘁ := by
    let e := (forgetDualIso C Y) ⊗ᵢ (forgetDualIso C X)
    change (rightDualTensorIso X.1 Y.1).homᘁ ≫ (forgetDualIso C (X ⊗ Y)).homᘁ =
      e.homᘁ ≫ (rightDualTensorIso X Y).hom.fᘁ at ht2
    letI : IsIso (e.homᘁ) := by
      change IsIso (Dimensions.rightDualIsoMap e).hom
      infer_instance
    change (rightDualTensorIso X Y).hom.fᘁ ≫ (forgetDualIso C (X ⊗ Y)).invᘁ =
      e.invᘁ ≫ (rightDualTensorIso X.1 Y.1).homᘁ
    apply (cancel_epi (e.homᘁ)).1
    rw [← Category.assoc, ← ht2]
    have he : e.homᘁ ≫ e.invᘁ = 𝟙 _ := by
      rw [← comp_rightAdjointMate, Iso.inv_hom_id, rightAdjointMate_id]
    have hf : (forgetDualIso C (X ⊗ Y)).homᘁ ≫
        (forgetDualIso C (X ⊗ Y)).invᘁ = 𝟙 _ := by
      rw [← comp_rightAdjointMate, Iso.inv_hom_id, rightAdjointMate_id]
    simp only [Category.assoc, hf, Category.comp_id]
    rw [← Category.assoc, he, Category.id_comp]
    simp
  simp only [Category.assoc]
  rw [hk]
  have hnat := Dimensions.rightDualTensorIso_natural
    (forgetDualIso C Y).inv (forgetDualIso C X).inv
  have hnat' : (rightDualTensorIso (Yᘁ).1 (Xᘁ).1).inv ≫
      (((forgetDualIso C Y).inv ⊗ₘ (forgetDualIso C X).inv)ᘁ) =
      ((forgetDualIso C X).invᘁ ⊗ₘ (forgetDualIso C Y).invᘁ) ≫
        (rightDualTensorIso Y.1ᘁ X.1ᘁ).inv := by
    apply (cancel_mono (rightDualTensorIso Y.1ᘁ X.1ᘁ).hom).1
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [hnat]
    simp [Category.assoc]
  rw [← Category.assoc ((rightDualTensorIso (Yᘁ).1 (Xᘁ).1).inv), hnat']
  simp only [tensorHom_comp_tensorHom_assoc, Category.assoc]

/-- The transported pivotal components satisfy the tensor law after forgetting. -/
theorem transported_pivotal_tensor
    (p : Dimensions.PivotalStructure (C := C.Obj)) (X Y : CategoryTheory.Center C.Obj) :
    (((p.iso X.1).hom ≫ (forgetDoubleDualIso C X).inv) ⊗ₘ
      ((p.iso Y.1).hom ≫ (forgetDoubleDualIso C Y).inv)) ≫
      (Dimensions.doubleDualTensorIso X Y).hom.f =
    (p.iso (X.1 ⊗ Y.1)).hom ≫ (forgetDoubleDualIso C (X ⊗ Y)).inv := by
  apply (cancel_mono (forgetDoubleDualIso C (X ⊗ Y)).hom).1
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [forgetDoubleDualIso_tensor]
  simp only [tensorHom_comp_tensorHom_assoc, Category.assoc, Iso.inv_hom_id,
    Category.comp_id, id_tensorHom_id, Category.id_comp]
  exact (p.tensor X.1 Y.1).symm

end PropertyF.Ground.CentreInduction
