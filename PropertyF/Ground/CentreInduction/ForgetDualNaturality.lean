module
public import PropertyF.Ground.CentreInduction.ForgetDual

/-! Naturality of the comparison between centre duals and base duals. -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.CentreInduction
universe v u
set_option backward.isDefEq.respectTransparency false
variable (C : BraidedFusionCategory.{v,u}) [RigidCategory (CategoryTheory.Center C.Obj)]

/-- Forgetting a centre mate computes the mate for the forgotten dual pairings. -/
theorem forget_rightAdjointMate {X Y : CategoryTheory.Center C.Obj} (f : X ⟶ Y) :
    (fᘁ).f = @rightAdjointMate C.Obj _ _ X.1 Y.1
      (show HasRightDual X.1 from { rightDual := (Xᘁ).1, exact := forgetPairing C X })
      (show HasRightDual Y.1 from { rightDual := (Yᘁ).1, exact := forgetPairing C Y }) f.f := by
  simp only [rightAdjointMate, CategoryTheory.Center.comp_f,
    CategoryTheory.Center.rightUnitor_inv_f, CategoryTheory.Center.leftUnitor_hom_f,
    CategoryTheory.Center.whiskerLeft_f, CategoryTheory.Center.whiskerRight_f,
    CategoryTheory.Center.associator_inv_f]
  rfl

/-- The canonical comparison of centre and base duals is natural in centre morphisms. -/
theorem forgetDualIso_natural {X Y : CategoryTheory.Center C.Obj} (f : X ⟶ Y) :
    (fᘁ).f ≫ (forgetDualIso C X).hom = (forgetDualIso C Y).hom ≫ (f.fᘁ) := by
  rw [forget_rightAdjointMate]
  unfold forgetDualIso rightDualIso
  simp only
  rw [← @comp_rightAdjointMate, ← @comp_rightAdjointMate]
  simp

/-- The double-dual comparison is natural in centre morphisms. -/
theorem forgetDoubleDualIso_natural {X Y : CategoryTheory.Center C.Obj} (f : X ⟶ Y) :
    ((fᘁ)ᘁ).f ≫ (forgetDoubleDualIso C Y).hom =
      (forgetDoubleDualIso C X).hom ≫ ((f.fᘁ)ᘁ) := by
  have h := forgetDualIso_natural C f
  have hmate := congrArg (fun m => rightAdjointMate m) h
  simp only [comp_rightAdjointMate] at hmate
  have hdual := forgetDualIso_natural C (fᘁ)
  simp only [forgetDoubleDualIso, Iso.trans_hom, Dimensions.rightDualIsoMap,
    Iso.symm_hom, Category.assoc]
  rw [← Category.assoc, hdual]
  simp only [Category.assoc]
  have hk : (fᘁ).fᘁ ≫ (forgetDualIso C Y).invᘁ =
      (forgetDualIso C X).invᘁ ≫ ((f.fᘁ)ᘁ) := by
    letI : IsIso ((forgetDualIso C X).homᘁ) := by
      change IsIso (Dimensions.rightDualIsoMap (forgetDualIso C X)).hom
      infer_instance
    apply (cancel_epi ((forgetDualIso C X).homᘁ)).1
    rw [← Category.assoc, hmate]
    have hx : (forgetDualIso C X).homᘁ ≫ (forgetDualIso C X).invᘁ = 𝟙 _ := by
      rw [← comp_rightAdjointMate, Iso.inv_hom_id, rightAdjointMate_id]
    have hy : (forgetDualIso C Y).homᘁ ≫ (forgetDualIso C Y).invᘁ = 𝟙 _ := by
      rw [← comp_rightAdjointMate, Iso.inv_hom_id, rightAdjointMate_id]
    simp only [Category.assoc, hy, Category.comp_id]
    rw [← Category.assoc, hx, Category.id_comp]
  rw [hk]

/-- The transported pivotal components are natural on centre morphisms. -/
theorem transported_pivotal_natural
    (p : Dimensions.PivotalStructure (C := C.Obj))
    {X Y : CategoryTheory.Center C.Obj} (f : X ⟶ Y) :
    f.f ≫ (p.iso Y.1).hom ≫ (forgetDoubleDualIso C Y).inv =
      (p.iso X.1).hom ≫ (forgetDoubleDualIso C X).inv ≫ ((fᘁ)ᘁ).f := by
  have h := forgetDoubleDualIso_natural C f
  apply (cancel_mono (forgetDoubleDualIso C Y).hom).1
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [h]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  exact p.naturality f.f

end PropertyF.Ground.CentreInduction
