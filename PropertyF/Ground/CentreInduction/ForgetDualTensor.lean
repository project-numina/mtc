module
public import PropertyF.Ground.CentreInduction.ForgetDual
public import PropertyF.Ground.Dimensions.DualTensorNaturality

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

end

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.CentreInduction
universe v u
set_option backward.isDefEq.respectTransparency false
variable {D : Type u} [Category.{v} D] [MonoidalCategory D]

/-- The canonical comparison of duals preserves tensor products of pairings. -/
theorem rightDualIso_tensor {X Y A B A' B' : D}
    (pX : ExactPairing X A) (qX : ExactPairing X A')
    (pY : ExactPairing Y B) (qY : ExactPairing Y B') :
    letI := pX
    letI := pY
    let p := (inferInstance : ExactPairing (X ⊗ Y) (B ⊗ A))
    letI := qX
    letI := qY
    let q := (inferInstance : ExactPairing (X ⊗ Y) (B' ⊗ A'))
    (rightDualIso p q).hom = (rightDualIso pY qY).hom ⊗ₘ (rightDualIso pX qX).hom := by
  dsimp only
  letI : ExactPairing X A := pX
  letI : ExactPairing Y B := pY
  letI : ExactPairing X A' := qX
  letI : ExactPairing Y B' := qY
  have hX := Dimensions.rightDualIso_evaluation pX qX
  have hY := Dimensions.rightDualIso_evaluation pY qY
  have h := Dimensions.rightDualIso_evaluation
    (inferInstance : ExactPairing (X ⊗ Y) (B ⊗ A))
    (inferInstance : ExactPairing (X ⊗ Y) (B' ⊗ A'))
  let a := (rightDualIso pX qX).hom
  let b := (rightDualIso pY qY).hom
  have ht : (b ⊗ₘ a) ▷ (X ⊗ Y) ≫ ε_ (X ⊗ Y) (B' ⊗ A') =
      ε_ (X ⊗ Y) (B ⊗ A) := by
    change (b ⊗ₘ a) ▷ (X ⊗ Y) ≫
      (𝟙 _ ⊗≫ B' ◁ (ε_ X A' ▷ Y) ⊗≫ ε_ Y B') =
      (𝟙 _ ⊗≫ B ◁ (ε_ X A ▷ Y) ⊗≫ ε_ Y B)
    calc
      _ = 𝟙 _ ⊗≫ (b ▷ ((A ⊗ X) ⊗ Y)) ⊗≫
          B' ◁ ((a ▷ X ≫ ε_ X A') ▷ Y) ⊗≫ ε_ Y B' := by
        simp only [tensorHom_def, comp_whiskerRight, whiskerLeft_comp]
        monoidal
      _ = 𝟙 _ ⊗≫ ((b ▷ ((A ⊗ X) ⊗ Y)) ≫
          B' ◁ ((a ▷ X ≫ ε_ X A') ▷ Y)) ⊗≫ ε_ Y B' := by monoidal
      _ = 𝟙 _ ⊗≫ (B ◁ ((a ▷ X ≫ ε_ X A') ▷ Y) ≫
          b ▷ ((𝟙_ D) ⊗ Y)) ⊗≫ ε_ Y B' := by rw [whisker_exchange]
      _ = 𝟙 _ ⊗≫ B ◁ ((a ▷ X ≫ ε_ X A') ▷ Y) ⊗≫
          (b ▷ ((𝟙_ D) ⊗ Y)) ⊗≫ ε_ Y B' := by monoidal
      _ = 𝟙 _ ⊗≫ B ◁ ((a ▷ X ≫ ε_ X A') ▷ Y) ⊗≫
          (b ▷ Y ≫ ε_ Y B') := by monoidal
      _ = _ := by rw [hX, hY]
  have hh := h.trans ht.symm
  let l := (rightDualIso (inferInstance : ExactPairing (X ⊗ Y) (B ⊗ A))
    (inferInstance : ExactPairing (X ⊗ Y) (B' ⊗ A'))).hom
  let r := b ⊗ₘ a
  change l ▷ (X ⊗ Y) ≫ ε_ (X ⊗ Y) (B' ⊗ A') =
    r ▷ (X ⊗ Y) ≫ ε_ (X ⊗ Y) (B' ⊗ A') at hh
  letI : HasRightDual (X ⊗ Y) := { rightDual := B' ⊗ A', exact := inferInstance }
  have he := congrArg (tensorRightHomEquiv (B ⊗ A) (X ⊗ Y) (B' ⊗ A') (𝟙_ D)) hh
  have hL := @tensorRightHomEquiv_whiskerRight_comp_evaluation D _ _ (X ⊗ Y) (B ⊗ A) this l
  have hR := @tensorRightHomEquiv_whiskerRight_comp_evaluation D _ _ (X ⊗ Y) (B ⊗ A) this r
  change (tensorRightHomEquiv (B ⊗ A) (X ⊗ Y) (B' ⊗ A') (𝟙_ D))
    (l ▷ (X ⊗ Y) ≫ ε_ (X ⊗ Y) (B' ⊗ A')) = l ≫ (λ_ (B' ⊗ A')).inv at hL
  change (tensorRightHomEquiv (B ⊗ A) (X ⊗ Y) (B' ⊗ A') (𝟙_ D))
    (r ▷ (X ⊗ Y) ≫ ε_ (X ⊗ Y) (B' ⊗ A')) = r ≫ (λ_ (B' ⊗ A')).inv at hR
  rw [hL, hR] at he
  exact (cancel_mono (λ_ (B' ⊗ A')).inv).1 he
end PropertyF.Ground.CentreInduction

end

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
