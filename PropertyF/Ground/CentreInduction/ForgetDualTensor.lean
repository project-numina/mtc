module
public import PropertyF.Ground.CentreInduction.ForgetDual
public import PropertyF.Ground.Dimensions.DualTensorNaturality

open PropertyF.Ground.Dimensions

/-! Naturality of the comparison between centre duals and base duals. -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.CentreInduction
universe v u
set_option backward.isDefEq.respectTransparency false
variable {D : Type u} [Category.{v} D] [MonoidalCategory D] [RightRigidCategory D]
  [RigidCategory (Center D)]
local notation "𝒵" => Center D
variable {X Y : Center D}

omit [RightRigidCategory D] in
/-- Forgetting a centre mate computes the mate for the forgotten dual pairings. -/
theorem forget_rightAdjointMate (f : X ⟶ Y) :
    (fᘁ).f = @rightAdjointMate D _ _ X.1 Y.1
      (show HasRightDual X.1 from { rightDual := (Xᘁ).1, exact := forgetPairing X })
      (show HasRightDual Y.1 from { rightDual := (Yᘁ).1, exact := forgetPairing Y }) f.f := by
  simp only [rightAdjointMate, Center.comp_f,
    Center.rightUnitor_inv_f, Center.leftUnitor_hom_f,
    Center.whiskerLeft_f, Center.whiskerRight_f,
    Center.associator_inv_f]
  rfl

/-- The canonical comparison of centre and base duals is natural in centre morphisms. -/
theorem forgetDualIso_natural (f : X ⟶ Y) :
    (fᘁ).f ≫ (forgetDualIso X).hom = (forgetDualIso Y).hom ≫ (f.fᘁ) := by
  simp [forget_rightAdjointMate, forgetDualIso, rightDualIso, ← comp_rightAdjointMate]

/-- The double-dual comparison is natural in centre morphisms. -/
theorem forgetDoubleDualIso_natural (f : X ⟶ Y) :
    ((fᘁ)ᘁ).f ≫ (forgetDoubleDualIso Y).hom =
      (forgetDoubleDualIso X).hom ≫ ((f.fᘁ)ᘁ) := by
  simp only [forgetDoubleDualIso, Iso.trans_hom, rightDualIsoMap,
    Iso.symm_hom, Category.assoc]
  rw [← Category.assoc, forgetDualIso_natural (fᘁ)]
  simp only [Category.assoc]
  congr 1
  change (fᘁ).fᘁ ≫ (rightDualIsoMap (forgetDualIso Y)).inv =
    (rightDualIsoMap (forgetDualIso X)).inv ≫ ((f.fᘁ)ᘁ)
  rw [Iso.eq_inv_comp, ← Category.assoc, Iso.comp_inv_eq]
  simpa only [comp_rightAdjointMate, rightDualIsoMap] using
    congrArg (fun m => rightAdjointMate m) (forgetDualIso_natural f)

/-- Transport a pivotal component along the forgotten double-dual comparison. -/
def transportedPivotalHom (p : PivotalStructure (C := D)) (Z : 𝒵) :
    Z.1 ⟶ ((Zᘁ)ᘁ).1 := (p.iso Z.1).hom ≫ (forgetDoubleDualIso Z).inv

/-- The transported pivotal components are natural on centre morphisms. -/
theorem transported_pivotal_natural (p : PivotalStructure (C := D)) (f : X ⟶ Y) :
    f.f ≫ transportedPivotalHom p Y = transportedPivotalHom p X ≫ ((fᘁ)ᘁ).f := by
  dsimp only [transportedPivotalHom]
  rw [← Category.assoc, Iso.comp_inv_eq]
  simpa only [Category.assoc, forgetDoubleDualIso_natural, Iso.inv_hom_id_assoc] using p.naturality f.f

end PropertyF.Ground.CentreInduction

end

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.CentreInduction
universe v u
set_option backward.isDefEq.respectTransparency false
variable {D : Type u} [Category.{v} D] [MonoidalCategory D]

/-- Tensoring dual-comparison maps preserves the tensor evaluation pairing. -/
private theorem rightDualIso_tensor_evaluation {X Y A B A' B' : D}
    (pX : ExactPairing X A) (qX : ExactPairing X A')
    (pY : ExactPairing Y B) (qY : ExactPairing Y B') :
    letI := pX
    letI := pY
    letI := qX
    letI := qY
    ((rightDualIso pY qY).hom ⊗ₘ (rightDualIso pX qX).hom) ▷ (X ⊗ Y) ≫
      ε_ (X ⊗ Y) (B' ⊗ A') = ε_ (X ⊗ Y) (B ⊗ A) := by
  let : ExactPairing X A := pX
  let : ExactPairing Y B := pY
  let : ExactPairing X A' := qX
  let : ExactPairing Y B' := qY
  let a := (rightDualIso pX qX).hom
  let b := (rightDualIso pY qY).hom
  change (b ⊗ₘ a) ▷ (X ⊗ Y) ≫
    (𝟙 _ ⊗≫ B' ◁ (ε_ X A' ▷ Y) ⊗≫ ε_ Y B') =
    (𝟙 _ ⊗≫ B ◁ (ε_ X A ▷ Y) ⊗≫ ε_ Y B)
  calc
    _ = 𝟙 _ ⊗≫ ((b ▷ ((A ⊗ X) ⊗ Y)) ≫
        B' ◁ ((a ▷ X ≫ ε_ X A') ▷ Y)) ⊗≫ ε_ Y B' := by
      simp only [tensorHom_def, comp_whiskerRight, whiskerLeft_comp]
      monoidal
    _ = 𝟙 _ ⊗≫ (B ◁ ((a ▷ X ≫ ε_ X A') ▷ Y) ≫
        b ▷ ((𝟙_ D) ⊗ Y)) ⊗≫ ε_ Y B' := by rw [whisker_exchange]
    _ = _ := by
      rw [← rightDualIso_evaluation pX qX, ← rightDualIso_evaluation pY qY]
      monoidal

/-- The canonical comparison of duals preserves tensor products of pairings. -/
theorem rightDualIso_tensor {X Y A B A' B' : D} (pX : ExactPairing X A) (qX : ExactPairing X A')
    (pY : ExactPairing Y B) (qY : ExactPairing Y B') :
    (rightDualIso (@ExactPairing.tensor D _ _ X Y A B pX pY)
      (@ExactPairing.tensor D _ _ X Y A' B' qX qY)).hom =
        (rightDualIso pY qY).hom ⊗ₘ (rightDualIso pX qX).hom := by
  let : ExactPairing X A := pX
  let : ExactPairing Y B := pY
  let : ExactPairing X A' := qX
  let : ExactPairing Y B' := qY
  exact evaluation_ext
    ((rightDualIso_evaluation
      (inferInstance : ExactPairing (X ⊗ Y) (B ⊗ A))
      (inferInstance : ExactPairing (X ⊗ Y) (B' ⊗ A'))).trans
      (rightDualIso_tensor_evaluation pX qX pY qY).symm)
end PropertyF.Ground.CentreInduction

end

/-! Tensor coherence of centre and base dual comparisons. -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.CentreInduction
universe v u
set_option backward.isDefEq.respectTransparency false
variable {D : Type u} [Category.{v} D] [MonoidalCategory D] [RightRigidCategory D]
  [RigidCategory (Center D)]
local notation "𝒵" => Center D

omit [RightRigidCategory D] in
/-- Tensor the forgotten dual pairings of two centre objects. -/
abbrev tensorForgetPairing (X Y : 𝒵) :
    ExactPairing (X.1 ⊗ Y.1) ((Yᘁ).1 ⊗ (Xᘁ).1) :=
  @ExactPairing.tensor D _ _ X.1 Y.1 (Xᘁ).1 (Yᘁ).1 (forgetPairing X) (forgetPairing Y)

theorem rightDualIso_trans {E : Type u} [Category.{v} E] [MonoidalCategory E]
    {X A B E : E} (p : ExactPairing X A) (q : ExactPairing X B) (r : ExactPairing X E) :
    (rightDualIso p q).hom ≫ (rightDualIso q r).hom = (rightDualIso p r).hom := by
  simp [rightDualIso, ← comp_rightAdjointMate]

omit [RightRigidCategory D] in
/-- The forgotten tensor dual agrees with the tensor pairing of forgotten duals. -/
theorem forget_rightDualTensorIso (X Y : 𝒵) :
    (rightDualTensorIso X Y).hom.f =
      (rightDualIso (forgetPairing (X ⊗ Y)) (tensorForgetPairing X Y)).hom := by
  have hc : (η_ (X ⊗ Y) (Yᘁ ⊗ Xᘁ)).f =
      @ExactPairing.coevaluation D _ _ (X.1 ⊗ Y.1) ((Yᘁ).1 ⊗ (Xᘁ).1)
        (tensorForgetPairing X Y) := by
    let cx : 𝟙_ D ⟶ X.1 ⊗ (Xᘁ).1 := (η_ X (Xᘁ)).f
    let cy : 𝟙_ D ⟶ Y.1 ⊗ (Yᘁ).1 := (η_ Y (Yᘁ)).f
    change (η_ X (Xᘁ) ⊗≫ (X ◁ η_ Y (Yᘁ)) ▷ (Xᘁ) ⊗≫
        𝟙 ((X ⊗ Y) ⊗ ((Yᘁ) ⊗ (Xᘁ)))).f =
      (cx ⊗≫ (X.1 ◁ cy) ▷ (Xᘁ).1 ⊗≫ 𝟙 ((X.1 ⊗ Y.1) ⊗ ((Yᘁ).1 ⊗ (Xᘁ).1)))
    simp [monoidalComp, cx, cy]
  unfold rightDualTensorIso rightDualIso rightAdjointMate
  simp only [Center.comp_f, Center.rightUnitor_inv_f,
    Center.leftUnitor_hom_f, Center.whiskerLeft_f,
    Center.whiskerRight_f, Center.associator_inv_f,
    Center.id_f, hc]
  rfl

/-- Forgetting centre duals preserves their tensor comparison. -/
theorem forgetDualIso_tensor (X Y : 𝒵) :
    (forgetDualIso (X ⊗ Y)).hom ≫ (rightDualTensorIso X.1 Y.1).hom =
      (rightDualTensorIso X Y).hom.f ≫
        ((forgetDualIso Y).hom ⊗ₘ (forgetDualIso X).hom) := by
  let p := forgetPairing (X ⊗ Y)
  let q := (HasRightDual.exact : ExactPairing (X.1 ⊗ Y.1) ((X.1 ⊗ Y.1)ᘁ))
  let s := tensorForgetPairing X Y
  let r := @ExactPairing.tensor D _ _ X.1 Y.1 (X.1ᘁ) (Y.1ᘁ)
      HasRightDual.exact HasRightDual.exact
  have h3 := rightDualIso_tensor (forgetPairing X) HasRightDual.exact
    (forgetPairing Y) HasRightDual.exact
  change (rightDualIso s r).hom = (forgetDualIso Y).hom ⊗ₘ (forgetDualIso X).hom at h3
  rw [forget_rightDualTensorIso]
  change (rightDualIso p q).hom ≫ (rightDualIso q r).hom =
    (rightDualIso p s).hom ≫ _
  rw [← h3, rightDualIso_trans p q r, rightDualIso_trans p s r]

end PropertyF.Ground.CentreInduction
