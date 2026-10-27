module
public import PropertyF.Ground.CentreInduction.DualTensorComparison

/-! Tensor coherence of centre and base dual comparisons. -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.CentreInduction
universe v u
set_option backward.isDefEq.respectTransparency false
variable (C : BraidedFusionCategory.{v,u}) [RigidCategory (CategoryTheory.Center C.Obj)]

theorem rightDualIso_trans {D : Type u} [Category.{v} D] [MonoidalCategory D]
    {X A B E : D} (p : ExactPairing X A) (q : ExactPairing X B) (r : ExactPairing X E) :
    (rightDualIso p q).hom ≫ (rightDualIso q r).hom = (rightDualIso p r).hom := by
  unfold rightDualIso
  simp only
  rw [← @comp_rightAdjointMate]
  simp

theorem forget_rightDualTensorIso (X Y : CategoryTheory.Center C.Obj) :
    (rightDualTensorIso X Y).hom.f =
      (rightDualIso (forgetPairing C (X ⊗ Y))
        (show ExactPairing (X.1 ⊗ Y.1) ((Yᘁ).1 ⊗ (Xᘁ).1) from
          @ExactPairing.tensor C.Obj _ _ X.1 Y.1 (Xᘁ).1 (Yᘁ).1
            (forgetPairing C X) (forgetPairing C Y))).hom := by
  have hc : (η_ (X ⊗ Y) (Yᘁ ⊗ Xᘁ)).f =
      @ExactPairing.coevaluation C.Obj _ _ (X.1 ⊗ Y.1) ((Yᘁ).1 ⊗ (Xᘁ).1)
        (@ExactPairing.tensor C.Obj _ _ X.1 Y.1 (Xᘁ).1 (Yᘁ).1
          (forgetPairing C X) (forgetPairing C Y)) := by
    let cx : 𝟙_ C.Obj ⟶ X.1 ⊗ (Xᘁ).1 := (η_ X (Xᘁ)).f
    let cy : 𝟙_ C.Obj ⟶ Y.1 ⊗ (Yᘁ).1 := (η_ Y (Yᘁ)).f
    have hh : (η_ X (Xᘁ) ⊗≫ (X ◁ η_ Y (Yᘁ)) ▷ (Xᘁ) ⊗≫
        𝟙 ((X ⊗ Y) ⊗ ((Yᘁ) ⊗ (Xᘁ)))).f =
      (cx ⊗≫ (X.1 ◁ cy) ▷ (Xᘁ).1 ⊗≫ 𝟙 ((X.1 ⊗ Y.1) ⊗ ((Yᘁ).1 ⊗ (Xᘁ).1))) := by
      simp [monoidalComp, cx, cy]
    exact hh
  unfold rightDualTensorIso rightDualIso rightAdjointMate
  simp only [CategoryTheory.Center.comp_f, CategoryTheory.Center.rightUnitor_inv_f,
    CategoryTheory.Center.leftUnitor_hom_f, CategoryTheory.Center.whiskerLeft_f,
    CategoryTheory.Center.whiskerRight_f, CategoryTheory.Center.associator_inv_f,
    CategoryTheory.Center.id_f, hc]
  rfl

/-- Forgetting centre duals preserves their tensor comparison. -/
theorem forgetDualIso_tensor (X Y : CategoryTheory.Center C.Obj) :
    (forgetDualIso C (X ⊗ Y)).hom ≫ (rightDualTensorIso X.1 Y.1).hom =
      (rightDualTensorIso X Y).hom.f ≫
        ((forgetDualIso C Y).hom ⊗ₘ (forgetDualIso C X).hom) := by
  let p := forgetPairing C (X ⊗ Y)
  let q := (HasRightDual.exact : ExactPairing (X.1 ⊗ Y.1) ((X.1 ⊗ Y.1)ᘁ))
  let s := @ExactPairing.tensor C.Obj _ _ X.1 Y.1 (Xᘁ).1 (Yᘁ).1
      (forgetPairing C X) (forgetPairing C Y)
  let r := @ExactPairing.tensor C.Obj _ _ X.1 Y.1 (X.1ᘁ) (Y.1ᘁ)
      HasRightDual.exact HasRightDual.exact
  have h1 := rightDualIso_trans p q r
  have h2 := rightDualIso_trans p s r
  have h3 := rightDualIso_tensor (forgetPairing C X) HasRightDual.exact
    (forgetPairing C Y) HasRightDual.exact
  change (rightDualIso s r).hom = (forgetDualIso C Y).hom ⊗ₘ (forgetDualIso C X).hom at h3
  rw [forget_rightDualTensorIso]
  change (rightDualIso p q).hom ≫ (rightDualIso q r).hom =
    (rightDualIso p s).hom ≫ _
  rw [← h3, h1, h2]

end PropertyF.Ground.CentreInduction
