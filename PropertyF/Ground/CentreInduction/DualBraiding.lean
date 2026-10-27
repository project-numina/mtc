module
public import PropertyF.Ground.CentreInduction.PositivePivotal
public import PropertyF.Ground.Dimensions.DualTensorNaturality

/-! Duals preserve braidings in rigid braided categories. -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.BraidedCategory
namespace PropertyF.Ground.CentreInduction
universe v u
set_option backward.isDefEq.respectTransparency false
variable {D : Type u} [Category.{v} D] [MonoidalCategory D] [BraidedCategory D] [RightRigidCategory D]

/-- A crossing slides past a right evaluation. -/
theorem eval_braiding_slide_right (X Y : D) :
    𝟙 ((Yᘁ) ⊗ (X ⊗ Y)) ⊗≫ (Yᘁ) ◁ (β_ X Y).hom ⊗≫
      ε_ Y (Yᘁ) ▷ X ⊗≫ 𝟙 X =
    𝟙 ((Yᘁ) ⊗ (X ⊗ Y)) ⊗≫ (β_ X (Yᘁ)).inv ▷ Y ⊗≫
      X ◁ ε_ Y (Yᘁ) ⊗≫ 𝟙 X := by
  calc
    _ = 𝟙 _ ⊗≫ ((β_ X (Yᘁ)).inv ▷ Y ≫ (β_ X (Yᘁ)).hom ▷ Y) ⊗≫
        (Yᘁ) ◁ (β_ X Y).hom ⊗≫ ε_ Y (Yᘁ) ▷ X ⊗≫ 𝟙 X := by
      rw [← comp_whiskerRight, Iso.inv_hom_id, id_whiskerRight]
      monoidal
    _ = 𝟙 _ ⊗≫ (β_ X (Yᘁ)).inv ▷ Y ⊗≫
        ((β_ X ((Yᘁ) ⊗ Y)).hom ≫ ε_ Y (Yᘁ) ▷ X) ⊗≫ 𝟙 X := by
      rw [braiding_tensor_right_hom]
      monoidal
    _ = 𝟙 _ ⊗≫ (β_ X (Yᘁ)).inv ▷ Y ⊗≫
        (X ◁ ε_ Y (Yᘁ) ≫ (β_ X (𝟙_ D)).hom) ⊗≫ 𝟙 X := by
      rw [braiding_naturality_right]
    _ = _ := by simp [braiding_tensorUnit_right, monoidalComp]

/-- The second crossing slide past a right evaluation. -/
theorem eval_braiding_slide_left (X Y : D) :
    𝟙 (((Xᘁ : D) ⊗ (Yᘁ : D)) ⊗ X) ⊗≫ (β_ (Xᘁ : D) (Yᘁ : D)).hom ▷ X ⊗≫
      (Yᘁ : D) ◁ ε_ X (Xᘁ : D) ⊗≫ 𝟙 (Yᘁ : D) =
    𝟙 (((Xᘁ : D) ⊗ (Yᘁ : D)) ⊗ X) ⊗≫ (Xᘁ : D) ◁ (β_ X (Yᘁ : D)).inv ⊗≫
      ε_ X (Xᘁ : D) ▷ (Yᘁ : D) ⊗≫ 𝟙 (Yᘁ : D) := by
  calc
    _ = 𝟙 _ ⊗≫ ((Xᘁ : D) ◁ (β_ X (Yᘁ : D)).inv ≫ (Xᘁ : D) ◁ (β_ X (Yᘁ : D)).hom) ⊗≫
        (β_ (Xᘁ : D) (Yᘁ : D)).hom ▷ X ⊗≫ (Yᘁ : D) ◁ ε_ X (Xᘁ : D) ⊗≫ 𝟙 (Yᘁ : D) := by
      rw [← whiskerLeft_comp, Iso.inv_hom_id, whiskerLeft_id]
      monoidal
    _ = 𝟙 _ ⊗≫ (Xᘁ : D) ◁ (β_ X (Yᘁ : D)).inv ⊗≫
        ((β_ ((Xᘁ : D) ⊗ X) (Yᘁ : D)).hom ≫ (Yᘁ : D) ◁ ε_ X (Xᘁ : D)) ⊗≫ 𝟙 (Yᘁ : D) := by
      rw [braiding_tensor_left_hom]
      monoidal
    _ = 𝟙 _ ⊗≫ (Xᘁ : D) ◁ (β_ X (Yᘁ : D)).inv ⊗≫
        (ε_ X (Xᘁ : D) ▷ (Yᘁ : D) ≫ (β_ (𝟙_ D) (Yᘁ : D)).hom) ⊗≫ 𝟙 (Yᘁ : D) := by
      rw [braiding_naturality_left]
    _ = _ := by simp [braiding_tensorUnit_left, monoidalComp]

/-- Dualizing a braiding gives the braiding of the duals. -/
theorem rightDualTensorIso_braiding (X Y : D) :
    ((β_ X Y).homᘁ) ≫ (rightDualTensorIso X Y).hom =
      (rightDualTensorIso Y X).hom ≫ (β_ (Xᘁ) (Yᘁ)).hom := by
  have h : (((β_ X Y).homᘁ) ≫ (rightDualTensorIso X Y).hom) ▷ (X ⊗ Y) ≫
        ε_ (X ⊗ Y) ((Yᘁ) ⊗ (Xᘁ)) =
      ((rightDualTensorIso Y X).hom ≫ (β_ (Xᘁ) (Yᘁ)).hom) ▷ (X ⊗ Y) ≫
        ε_ (X ⊗ Y) ((Yᘁ) ⊗ (Xᘁ)) := by
    have he := Dimensions.rightDualIso_evaluation
      (@HasRightDual.exact D _ _ (X ⊗ Y) (RightRigidCategory.rightDual _))
      (ExactPairing.tensor (X₁ := X) (X₂ := Y) (Y₁ := Xᘁ) (Y₂ := Yᘁ))
    change (rightDualTensorIso X Y).hom ▷ (X ⊗ Y) ≫
      ε_ (X ⊗ Y) ((Yᘁ) ⊗ (Xᘁ)) = ε_ (X ⊗ Y) ((X ⊗ Y)ᘁ) at he
    have he' := Dimensions.rightDualIso_evaluation
      (@HasRightDual.exact D _ _ (Y ⊗ X) (RightRigidCategory.rightDual _))
      (ExactPairing.tensor (X₁ := Y) (X₂ := X) (Y₁ := Yᘁ) (Y₂ := Xᘁ))
    change (rightDualTensorIso Y X).hom ▷ (Y ⊗ X) ≫
      ε_ (Y ⊗ X) ((Xᘁ) ⊗ (Yᘁ)) = ε_ (Y ⊗ X) ((Y ⊗ X)ᘁ) at he'
    simp only [comp_whiskerRight_assoc]
    rw [he,
      rightAdjointMate_comp_evaluation, ← he', whisker_exchange_assoc]
    congr 1
    change ((Xᘁ) ⊗ (Yᘁ)) ◁ (β_ X Y).hom ≫
        (𝟙 _ ⊗≫ (Xᘁ) ◁ (ε_ Y (Yᘁ) ▷ X) ⊗≫ ε_ X (Xᘁ)) =
      (β_ (Xᘁ) (Yᘁ)).hom ▷ (X ⊗ Y) ≫
        (𝟙 _ ⊗≫ (Yᘁ) ◁ (ε_ X (Xᘁ) ▷ Y) ⊗≫ ε_ Y (Yᘁ))
    calc
      _ = 𝟙 _ ⊗≫ (Xᘁ : D) ◁ (𝟙 ((Yᘁ : D) ⊗ (X ⊗ Y)) ⊗≫
            (Yᘁ : D) ◁ (β_ X Y).hom ⊗≫ ε_ Y (Yᘁ : D) ▷ X ⊗≫ 𝟙 X) ⊗≫
          ε_ X (Xᘁ : D) ⊗≫ 𝟙 _ := by monoidal
      _ = 𝟙 _ ⊗≫ (Xᘁ : D) ◁ (𝟙 ((Yᘁ : D) ⊗ (X ⊗ Y)) ⊗≫
            (β_ X (Yᘁ : D)).inv ▷ Y ⊗≫ X ◁ ε_ Y (Yᘁ : D) ⊗≫ 𝟙 X) ⊗≫
          ε_ X (Xᘁ : D) ⊗≫ 𝟙 _ := by rw [eval_braiding_slide_right]
      _ = 𝟙 _ ⊗≫ ((Xᘁ : D) ◁ (β_ X (Yᘁ : D)).inv) ▷ Y ⊗≫
          (((Xᘁ ⊗ X) ◁ ε_ Y (Yᘁ : D)) ≫ (ε_ X (Xᘁ : D) ▷ (𝟙_ D))) ⊗≫ 𝟙 _ := by
        monoidal
      _ = 𝟙 _ ⊗≫ ((Xᘁ : D) ◁ (β_ X (Yᘁ : D)).inv) ▷ Y ⊗≫
          ((ε_ X (Xᘁ : D) ▷ ((Yᘁ : D) ⊗ Y)) ≫ ((𝟙_ D) ◁ ε_ Y (Yᘁ : D))) ⊗≫ 𝟙 _ := by
        rw [whisker_exchange]
      _ = 𝟙 _ ⊗≫ ((𝟙 (((Xᘁ : D) ⊗ (Yᘁ : D)) ⊗ X) ⊗≫
            (Xᘁ : D) ◁ (β_ X (Yᘁ : D)).inv ⊗≫ ε_ X (Xᘁ : D) ▷ (Yᘁ : D) ⊗≫ 𝟙 (Yᘁ : D)) ▷ Y) ⊗≫
          ε_ Y (Yᘁ : D) ⊗≫ 𝟙 _ := by
        monoidal
      _ = 𝟙 _ ⊗≫ ((𝟙 (((Xᘁ : D) ⊗ (Yᘁ : D)) ⊗ X) ⊗≫
            (β_ (Xᘁ : D) (Yᘁ : D)).hom ▷ X ⊗≫ (Yᘁ : D) ◁ ε_ X (Xᘁ : D) ⊗≫ 𝟙 (Yᘁ : D)) ▷ Y) ⊗≫
          ε_ Y (Yᘁ : D) ⊗≫ 𝟙 _ := by rw [eval_braiding_slide_left]
      _ = _ := by monoidal
  let l := ((β_ X Y).homᘁ) ≫ (rightDualTensorIso X Y).hom
  let r := (rightDualTensorIso Y X).hom ≫ (β_ (Xᘁ) (Yᘁ)).hom
  change l ▷ (X ⊗ Y) ≫ ε_ (X ⊗ Y) (Yᘁ ⊗ Xᘁ) =
    r ▷ (X ⊗ Y) ≫ ε_ (X ⊗ Y) (Yᘁ ⊗ Xᘁ) at h
  letI : HasRightDual (X ⊗ Y) := { rightDual := (Yᘁ) ⊗ (Xᘁ), exact := ExactPairing.tensor }
  have he := congrArg (tensorRightHomEquiv ((Y ⊗ X)ᘁ) (X ⊗ Y) ((Yᘁ) ⊗ (Xᘁ)) (𝟙_ D)) h
  have hL := @tensorRightHomEquiv_whiskerRight_comp_evaluation D _ _ (X ⊗ Y) ((Y ⊗ X)ᘁ) this l
  have hR := @tensorRightHomEquiv_whiskerRight_comp_evaluation D _ _ (X ⊗ Y) ((Y ⊗ X)ᘁ) this r
  change (tensorRightHomEquiv ((Y ⊗ X)ᘁ) (X ⊗ Y) ((Yᘁ) ⊗ (Xᘁ)) (𝟙_ D))
    (l ▷ (X ⊗ Y) ≫ ε_ (X ⊗ Y) ((Yᘁ) ⊗ (Xᘁ))) = l ≫ (λ_ ((Yᘁ) ⊗ (Xᘁ))).inv at hL
  change (tensorRightHomEquiv ((Y ⊗ X)ᘁ) (X ⊗ Y) ((Yᘁ) ⊗ (Xᘁ)) (𝟙_ D))
    (r ▷ (X ⊗ Y) ≫ ε_ (X ⊗ Y) ((Yᘁ) ⊗ (Xᘁ))) = r ≫ (λ_ ((Yᘁ) ⊗ (Xᘁ))).inv at hR
  rw [hL, hR] at he
  exact (cancel_mono (λ_ ((Yᘁ) ⊗ (Xᘁ))).inv).1 he
end PropertyF.Ground.CentreInduction
