module
public import PropertyF.Ground.CentreInduction.PositivePivotal
public import PropertyF.Ground.Dimensions.DualTensorNaturality
public import PropertyF.Ground.Dimensions.DualBraiding

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
    _ = (α_ (Yᘁ) X Y).inv ≫ (𝟙 (((Yᘁ) ⊗ X) ⊗ Y) ⊗≫
        (Yᘁ) ◁ (β_ X Y).hom ⊗≫ ε_ Y (Yᘁ) ▷ X ⊗≫ (λ_ X).hom) := by
      monoidal
    _ = (α_ (Yᘁ) X Y).inv ≫ ((β_ X (Yᘁ)).inv ▷ Y ⊗≫
        X ◁ ε_ Y (Yᘁ) ⊗≫ (ρ_ X).hom) := by
      rw [← Dimensions.braiding_inverse_cap_slide Y X]
    _ = _ := by monoidal

/-- The second crossing slide past a right evaluation. -/
theorem eval_braiding_slide_left (X Y : D) :
    𝟙 (((Xᘁ : D) ⊗ (Yᘁ : D)) ⊗ X) ⊗≫ (β_ (Xᘁ : D) (Yᘁ : D)).hom ▷ X ⊗≫
      (Yᘁ : D) ◁ ε_ X (Xᘁ : D) ⊗≫ 𝟙 (Yᘁ : D) =
    𝟙 (((Xᘁ : D) ⊗ (Yᘁ : D)) ⊗ X) ⊗≫ (Xᘁ : D) ◁ (β_ X (Yᘁ : D)).inv ⊗≫
      ε_ X (Xᘁ : D) ▷ (Yᘁ : D) ⊗≫ 𝟙 (Yᘁ : D) := by
  calc
    _ = (β_ (Xᘁ) (Yᘁ)).hom ▷ X ⊗≫ (Yᘁ) ◁ ε_ X (Xᘁ) ⊗≫ (ρ_ (Yᘁ)).hom := by
      monoidal
    _ = 𝟙 (((Xᘁ) ⊗ (Yᘁ)) ⊗ X) ⊗≫ (Xᘁ) ◁ (β_ X (Yᘁ)).inv ⊗≫
        ε_ X (Xᘁ) ▷ (Yᘁ) ⊗≫ (λ_ (Yᘁ)).hom := by
      rw [Dimensions.braiding_cap_slide X (Yᘁ)]
    _ = _ := by monoidal

/-- Dualizing a braiding gives the braiding of the duals. -/
theorem rightDualTensorIso_braiding (X Y : D) :
    ((β_ X Y).homᘁ) ≫ (rightDualTensorIso X Y).hom =
      (rightDualTensorIso Y X).hom ≫ (β_ (Xᘁ) (Yᘁ)).hom :=
  Dimensions.rightDualTensorIso_braiding X Y
end PropertyF.Ground.CentreInduction
