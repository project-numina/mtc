module
public import PropertyF.Ground.CentreInduction.ForgetDoubleDualTensor

/-! Unit coherence of centre dual and pivotal comparisons. -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.CentreInduction
universe v u
set_option backward.isDefEq.respectTransparency false
variable (C : BraidedFusionCategory.{v,u}) [RigidCategory (CategoryTheory.Center C.Obj)]

theorem forget_rightDualUnitIso :
    (Dimensions.rightDualUnitIso (C := CategoryTheory.Center C.Obj)).hom.f =
      (rightDualIso (forgetPairing C (𝟙_ (CategoryTheory.Center C.Obj)))
        (inferInstance : ExactPairing (𝟙_ C.Obj) (𝟙_ C.Obj))).hom := by
  have hc : (η_ (𝟙_ (CategoryTheory.Center C.Obj)) (𝟙_ (CategoryTheory.Center C.Obj))).f =
      (ρ_ (𝟙_ (CategoryTheory.Center C.Obj)).1).inv := by
    change (ρ_ (𝟙_ (CategoryTheory.Center C.Obj))).inv.f = _
    exact CategoryTheory.Center.rightUnitor_inv_f _
  unfold Dimensions.rightDualUnitIso rightDualIso rightAdjointMate
  simp only [CategoryTheory.Center.comp_f, CategoryTheory.Center.rightUnitor_inv_f,
    CategoryTheory.Center.leftUnitor_hom_f, CategoryTheory.Center.whiskerLeft_f,
    CategoryTheory.Center.whiskerRight_f, CategoryTheory.Center.associator_inv_f,
    CategoryTheory.Center.id_f, hc]
  rfl

theorem forgetDualIso_unit :
    (forgetDualIso C (𝟙_ (CategoryTheory.Center C.Obj))).hom ≫
      (Dimensions.rightDualUnitIso (C := C.Obj)).hom =
    (Dimensions.rightDualUnitIso (C := CategoryTheory.Center C.Obj)).hom.f := by
  rw [forget_rightDualUnitIso]
  exact rightDualIso_trans (forgetPairing C (𝟙_ (CategoryTheory.Center C.Obj)))
    HasRightDual.exact (inferInstance : ExactPairing (𝟙_ C.Obj) (𝟙_ C.Obj))

theorem forgetDoubleDualIso_unit :
    (Dimensions.doubleDualUnitIso (C := CategoryTheory.Center C.Obj)).hom.f ≫
      (forgetDoubleDualIso C (𝟙_ (CategoryTheory.Center C.Obj))).hom =
    (Dimensions.doubleDualUnitIso (C := C.Obj)).hom := by
  let U := 𝟙_ (CategoryTheory.Center C.Obj)
  letI : HasRightDual U := RightRigidCategory.rightDual U
  letI : HasRightDual (𝟙_ C.Obj) := RightRigidCategory.rightDual _
  let e := Dimensions.rightDualUnitIso (C := CategoryTheory.Center C.Obj)
  let b := Dimensions.rightDualUnitIso (C := C.Obj)
  have hu : (forgetDualIso C U).hom ≫ b.hom = e.hom.f := forgetDualIso_unit C
  have hv : e.inv.f ≫ (forgetDualIso C U).hom = b.inv := by
    apply (cancel_mono b.hom).1
    rw [Category.assoc, hu, ← CategoryTheory.Center.comp_f, Iso.inv_hom_id]
    simp
  have hn := forgetDualIso_natural C e.hom
  change (e.homᘁ).f ≫ (forgetDualIso C (Uᘁ)).hom =
    (forgetDualIso C U).hom ≫ (e.hom.fᘁ) at hn
  simp only [Dimensions.doubleDualUnitIso, Iso.trans_hom, Iso.symm_hom,
    Dimensions.rightDualIsoMap, CategoryTheory.Center.comp_f, forgetDoubleDualIso,
    Category.assoc]
  change e.inv.f ≫ (e.homᘁ).f ≫ (forgetDualIso C (Uᘁ)).hom ≫
      (forgetDualIso C U).invᘁ = b.inv ≫ b.homᘁ
  rw [← Category.assoc (e.homᘁ).f, hn]
  rw [← hu, comp_rightAdjointMate]
  simp only [Category.assoc]
  rw [← Category.assoc e.inv.f, hv]
  simp only [← Category.assoc ((forgetDualIso C U).homᘁ), ← comp_rightAdjointMate,
    Iso.inv_hom_id, rightAdjointMate_id, Category.comp_id]

/-- Transported pivotal components preserve the tensor unit after forgetting. -/
theorem transported_pivotal_unit (p : Dimensions.PivotalStructure (C := C.Obj)) :
    (p.iso (𝟙_ C.Obj)).hom ≫
      (forgetDoubleDualIso C (𝟙_ (CategoryTheory.Center C.Obj))).inv =
    (Dimensions.doubleDualUnitIso (C := CategoryTheory.Center C.Obj)).hom.f := by
  apply (cancel_mono (forgetDoubleDualIso C (𝟙_ (CategoryTheory.Center C.Obj))).hom).1
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [forgetDoubleDualIso_unit, p.unit]

end PropertyF.Ground.CentreInduction
