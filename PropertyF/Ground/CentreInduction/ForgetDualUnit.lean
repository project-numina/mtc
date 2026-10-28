module
public import PropertyF.Ground.CentreInduction.ForgetDualTensor

/-! Tensor coherence for the forgotten double-dual and pivotal components. -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.CentreInduction
universe v u
set_option backward.isDefEq.respectTransparency false
variable {D : Type u} [Category.{v} D] [MonoidalCategory D] [RightRigidCategory D]
  [RigidCategory (CategoryTheory.Center D)]
local notation "𝒵" => CategoryTheory.Center D

/-- The inverse tensor comparison commutes with the forgotten dual isomorphisms. -/
private theorem forgetDualIso_tensor_inv (X Y : 𝒵) :
    (rightDualTensorIso X Y).inv.f ≫ (forgetDualIso (X ⊗ Y)).hom =
      ((forgetDualIso Y).hom ⊗ₘ (forgetDualIso X).hom) ≫
        (rightDualTensorIso X.1 Y.1).inv := by
  apply (cancel_mono (rightDualTensorIso X.1 Y.1).hom).1
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [forgetDualIso_tensor X Y]
  simp [← CategoryTheory.Center.comp_f, ← Category.assoc]

/-- Taking mates of the tensor comparison also preserves its inverse. -/
private theorem forgetDualIso_tensor_mate_inv (X Y : 𝒵) :
    (rightDualTensorIso X Y).hom.fᘁ ≫ (forgetDualIso (X ⊗ Y)).invᘁ =
      (((forgetDualIso Y).inv ⊗ₘ (forgetDualIso X).inv)ᘁ) ≫
        (rightDualTensorIso X.1 Y.1).homᘁ := by
  have ht := congrArg (fun m => rightAdjointMate m) (forgetDualIso_tensor X Y)
  simp only [comp_rightAdjointMate] at ht
  let e := (forgetDualIso Y) ⊗ᵢ (forgetDualIso X)
  change (rightDualTensorIso X.1 Y.1).homᘁ ≫ (forgetDualIso (X ⊗ Y)).homᘁ =
    e.homᘁ ≫ (rightDualTensorIso X Y).hom.fᘁ at ht
  let : IsIso (e.homᘁ) := by
    change IsIso (Dimensions.rightDualIsoMap e).hom
    infer_instance
  change (rightDualTensorIso X Y).hom.fᘁ ≫ (forgetDualIso (X ⊗ Y)).invᘁ =
    e.invᘁ ≫ (rightDualTensorIso X.1 Y.1).homᘁ
  apply (cancel_epi (e.homᘁ)).1
  rw [← Category.assoc, ← ht]
  have he : e.homᘁ ≫ e.invᘁ = 𝟙 _ := by
    rw [← comp_rightAdjointMate, Iso.inv_hom_id, rightAdjointMate_id]
  have hf : (forgetDualIso (X ⊗ Y)).homᘁ ≫
      (forgetDualIso (X ⊗ Y)).invᘁ = 𝟙 _ := by
    rw [← comp_rightAdjointMate, Iso.inv_hom_id, rightAdjointMate_id]
  simp only [Category.assoc, hf]
  rw [← Category.assoc, he, Category.id_comp]
  simp

omit [RigidCategory (𝒵)] in
/-- The inverse right-dual tensor comparison is natural in both arguments. -/
theorem rightDualTensorIso_inv_natural {A A' B B' : D}
    (f : A ⟶ A') (g : B ⟶ B') :
    (rightDualTensorIso A' B').inv ≫ ((f ⊗ₘ g)ᘁ) =
      (gᘁ ⊗ₘ fᘁ) ≫ (rightDualTensorIso A B).inv := by
  rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv]
  exact Dimensions.rightDualTensorIso_natural f g

/-- Forgetting the centre preserves the tensor comparison for double duals. -/
theorem forgetDoubleDualIso_tensor (X Y : 𝒵) :
    (Dimensions.doubleDualTensorIso X Y).hom.f ≫ (forgetDoubleDualIso (X ⊗ Y)).hom =
      ((forgetDoubleDualIso X).hom ⊗ₘ (forgetDoubleDualIso Y).hom) ≫
        (Dimensions.doubleDualTensorIso X.1 Y.1).hom := by
  simp only [Dimensions.doubleDualTensorIso, Iso.trans_hom, Iso.symm_hom,
    Dimensions.rightDualIsoMap, CategoryTheory.Center.comp_f, Category.assoc,
    forgetDoubleDualIso]
  rw [← Category.assoc ((rightDualTensorIso X Y).homᘁ).f, forgetDualIso_natural]
  simp only [← Category.assoc]
  rw [forgetDualIso_tensor_inv (Yᘁ) (Xᘁ)]
  simp only [Category.assoc]
  rw [forgetDualIso_tensor_mate_inv X Y]
  rw [← Category.assoc ((rightDualTensorIso (Yᘁ).1 (Xᘁ).1).inv),
    rightDualTensorIso_inv_natural (forgetDualIso Y).inv (forgetDualIso X).inv]
  simp only [tensorHom_comp_tensorHom_assoc, Category.assoc]

/-- The transported pivotal components satisfy the tensor law after forgetting. -/
theorem transported_pivotal_tensor
    (p : Dimensions.PivotalStructure (C := D)) (X Y : 𝒵) :
    (((p.iso X.1).hom ≫ (forgetDoubleDualIso X).inv) ⊗ₘ
      ((p.iso Y.1).hom ≫ (forgetDoubleDualIso Y).inv)) ≫
      (Dimensions.doubleDualTensorIso X Y).hom.f =
    (p.iso (X.1 ⊗ Y.1)).hom ≫ (forgetDoubleDualIso (X ⊗ Y)).inv := by
  apply (cancel_mono (forgetDoubleDualIso (X ⊗ Y)).hom).1
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [forgetDoubleDualIso_tensor]
  simp only [tensorHom_comp_tensorHom_assoc, Category.assoc, Iso.inv_hom_id,
    Category.comp_id]
  exact (p.tensor X.1 Y.1).symm

end PropertyF.Ground.CentreInduction

end

/-! Unit coherence of centre dual and pivotal comparisons. -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.CentreInduction
universe v u
set_option backward.isDefEq.respectTransparency false
variable {D : Type u} [Category.{v} D] [MonoidalCategory D] [RightRigidCategory D]
  [RigidCategory (CategoryTheory.Center D)]
local notation "𝒵" => CategoryTheory.Center D

omit [RightRigidCategory D] in
/-- The right-dual unit comparison is preserved by centre forget. -/
theorem forget_rightDualUnitIso :
    (Dimensions.rightDualUnitIso (C := 𝒵)).hom.f =
      (rightDualIso (forgetPairing (𝟙_ (𝒵)))
        (inferInstance : ExactPairing (𝟙_ D) (𝟙_ D))).hom := by
  have hc : (η_ (𝟙_ (𝒵)) (𝟙_ (𝒵))).f =
      (ρ_ (𝟙_ (𝒵)).1).inv := by
    change (ρ_ (𝟙_ (𝒵))).inv.f = _
    exact CategoryTheory.Center.rightUnitor_inv_f _
  unfold Dimensions.rightDualUnitIso rightDualIso rightAdjointMate
  simp only [CategoryTheory.Center.comp_f, CategoryTheory.Center.rightUnitor_inv_f,
    CategoryTheory.Center.leftUnitor_hom_f, CategoryTheory.Center.whiskerLeft_f,
    CategoryTheory.Center.whiskerRight_f, CategoryTheory.Center.associator_inv_f,
    CategoryTheory.Center.id_f, hc]
  rfl

theorem forgetDualIso_unit :
    (forgetDualIso (𝟙_ (𝒵))).hom ≫
      (Dimensions.rightDualUnitIso (C := D)).hom =
    (Dimensions.rightDualUnitIso (C := 𝒵)).hom.f := by
  rw [forget_rightDualUnitIso]
  exact rightDualIso_trans (forgetPairing (𝟙_ (𝒵)))
    HasRightDual.exact (inferInstance : ExactPairing (𝟙_ D) (𝟙_ D))

theorem forgetDoubleDualIso_unit :
    (Dimensions.doubleDualUnitIso (C := 𝒵)).hom.f ≫
      (forgetDoubleDualIso (𝟙_ (𝒵))).hom =
    (Dimensions.doubleDualUnitIso (C := D)).hom := by
  let U := 𝟙_ (𝒵)
  let : HasRightDual U := RightRigidCategory.rightDual U
  let : HasRightDual (𝟙_ D) := RightRigidCategory.rightDual _
  let e := Dimensions.rightDualUnitIso (C := 𝒵)
  let b := Dimensions.rightDualUnitIso (C := D)
  have hu : (forgetDualIso U).hom ≫ b.hom = e.hom.f := forgetDualIso_unit (D := D)
  have hv : e.inv.f ≫ (forgetDualIso U).hom = b.inv := by
    apply (cancel_mono b.hom).1
    rw [Category.assoc, hu, ← CategoryTheory.Center.comp_f, Iso.inv_hom_id]
    simp
  have hn := forgetDualIso_natural e.hom
  change (e.homᘁ).f ≫ (forgetDualIso (Uᘁ)).hom =
    (forgetDualIso U).hom ≫ (e.hom.fᘁ) at hn
  simp only [Dimensions.doubleDualUnitIso, Iso.trans_hom, Iso.symm_hom,
    Dimensions.rightDualIsoMap, CategoryTheory.Center.comp_f, forgetDoubleDualIso,
    Category.assoc]
  change e.inv.f ≫ (e.homᘁ).f ≫ (forgetDualIso (Uᘁ)).hom ≫
      (forgetDualIso U).invᘁ = b.inv ≫ b.homᘁ
  rw [← Category.assoc (e.homᘁ).f, hn]
  rw [← hu, comp_rightAdjointMate]
  simp only [Category.assoc]
  rw [← Category.assoc e.inv.f, hv]
  simp only [← comp_rightAdjointMate,
    Iso.inv_hom_id, rightAdjointMate_id, Category.comp_id]

/-- Transported pivotal components preserve the tensor unit after forgetting. -/
theorem transported_pivotal_unit (p : Dimensions.PivotalStructure (C := D)) :
    (p.iso (𝟙_ D)).hom ≫
      (forgetDoubleDualIso (𝟙_ (𝒵))).inv =
    (Dimensions.doubleDualUnitIso (C := 𝒵)).hom.f := by
  apply (cancel_mono (forgetDoubleDualIso (𝟙_ (𝒵))).hom).1
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [forgetDoubleDualIso_unit, p.unit]

end PropertyF.Ground.CentreInduction
