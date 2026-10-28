module
public import PropertyF.Ground.Dimensions.DualCoherence

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.Dimensions
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
/-- A morphism into a dual object is determined by its evaluation pairing. -/
theorem evaluation_ext {C : Type u} [Category.{v} C] [MonoidalCategory C] {X Y Z : C} [ExactPairing X Y] {f g : Z ⟶ Y}
    (h : f ▷ X ≫ ε_ X Y = g ▷ X ≫ ε_ X Y) : f = g := by
  let hDual : HasRightDual X := { rightDual := Y, exact := inferInstance }
  let : HasRightDual X := hDual
  have h' := congrArg (tensorRightHomEquiv Z X Y (𝟙_ C)) h
  have hL := @tensorRightHomEquiv_whiskerRight_comp_evaluation C _ _ X Z hDual f
  have hR := @tensorRightHomEquiv_whiskerRight_comp_evaluation C _ _ X Z hDual g
  change (tensorRightHomEquiv Z X Y (𝟙_ C)) (f ▷ X ≫ ε_ X Y) = f ≫ (λ_ Y).inv at hL
  change (tensorRightHomEquiv Z X Y (𝟙_ C)) (g ▷ X ≫ ε_ X Y) = g ≫ (λ_ Y).inv at hR
  rw [hL, hR] at h'
  exact (cancel_mono (λ_ Y).inv).1 h'

set_option backward.isDefEq.respectTransparency false in
/-- Evaluation of tensor pairings is natural in both factors. -/
theorem tensorPairing_evaluation_natural {X X' Y Y' : C} (f : X ⟶ X') (g : Y ⟶ Y') : ((Y'ᘁ) ⊗ (X'ᘁ)) ◁ (f ⊗ₘ g) ≫ ε_ (X' ⊗ Y') ((Y'ᘁ) ⊗ (X'ᘁ)) =
        (gᘁ ⊗ₘ fᘁ) ▷ (X ⊗ Y) ≫ ε_ (X ⊗ Y) ((Yᘁ) ⊗ (Xᘁ)) := by
  change ((Y'ᘁ) ⊗ (X'ᘁ)) ◁ (f ⊗ₘ g) ≫
    (𝟙 _ ⊗≫ (Y'ᘁ) ◁ (ε_ X' (X'ᘁ) ▷ Y') ⊗≫ ε_ Y' (Y'ᘁ)) =
    (gᘁ ⊗ₘ fᘁ) ▷ (X ⊗ Y) ≫
    (𝟙 _ ⊗≫ (Yᘁ) ◁ (ε_ X (Xᘁ) ▷ Y) ⊗≫ ε_ Y (Yᘁ))
  calc
    _ = 𝟙 _ ⊗≫ (Y'ᘁ : C) ◁ (((X'ᘁ : C) ◁ f) ▷ Y ≫
      ((X'ᘁ ⊗ X') ◁ g) ≫ (ε_ X' (X'ᘁ) ▷ Y')) ⊗≫ ε_ Y' (Y'ᘁ) := by
        simp only [tensorHom_def, whiskerLeft_comp]
        monoidal
    _ = 𝟙 _ ⊗≫ (Y'ᘁ : C) ◁ (((X'ᘁ : C) ◁ f) ▷ Y ≫
      (ε_ X' (X'ᘁ) ▷ Y) ≫ ((𝟙_ C) ◁ g)) ⊗≫ ε_ Y' (Y'ᘁ) := by
        rw [← whisker_exchange]
    _ = 𝟙 _ ⊗≫ (Y'ᘁ : C) ◁ (((X'ᘁ : C) ◁ f ≫ ε_ X' (X'ᘁ)) ▷ Y) ⊗≫
      ((Y'ᘁ : C) ◁ g ≫ ε_ Y' (Y'ᘁ)) := by monoidal
    _ = 𝟙 _ ⊗≫ (Y'ᘁ : C) ◁ (((fᘁ) ▷ X ≫ ε_ X (Xᘁ)) ▷ Y) ⊗≫
      ((gᘁ) ▷ Y ≫ ε_ Y (Yᘁ)) := by
        rw [rightAdjointMate_comp_evaluation, rightAdjointMate_comp_evaluation]
    _ = 𝟙 _ ⊗≫ (Y'ᘁ : C) ◁ ((fᘁ ▷ X) ▷ Y) ⊗≫
      (((Y'ᘁ : C) ◁ (ε_ X (Xᘁ) ▷ Y)) ≫ (gᘁ ▷ ((𝟙_ C) ⊗ Y))) ⊗≫ ε_ Y (Yᘁ) := by
        simp only [whiskerLeft_comp, comp_whiskerRight]
        monoidal
    _ = 𝟙 _ ⊗≫ (Y'ᘁ : C) ◁ ((fᘁ ▷ X) ▷ Y) ⊗≫
      ((gᘁ ▷ (((Xᘁ) ⊗ X) ⊗ Y)) ≫ ((Yᘁ : C) ◁ (ε_ X (Xᘁ) ▷ Y))) ⊗≫ ε_ Y (Yᘁ) := by
        rw [whisker_exchange]
    _ = _ := by simp only [tensorHom_def', comp_whiskerRight]; monoidal

set_option backward.isDefEq.respectTransparency false in
theorem rightDualTensorIso_natural {X X' Y Y' : C} (f : X ⟶ X') (g : Y ⟶ Y') :
    ((f ⊗ₘ g)ᘁ) ≫ (rightDualTensorIso X Y).hom =
      (rightDualTensorIso X' Y').hom ≫ (gᘁ ⊗ₘ fᘁ) := by
  have h : (((f ⊗ₘ g)ᘁ) ≫ (rightDualTensorIso X Y).hom) ▷ (X ⊗ Y) ≫
        ε_ (X ⊗ Y) ((Yᘁ) ⊗ (Xᘁ)) =
      ((rightDualTensorIso X' Y').hom ≫ (gᘁ ⊗ₘ fᘁ)) ▷ (X ⊗ Y) ≫
        ε_ (X ⊗ Y) ((Yᘁ) ⊗ (Xᘁ)) := by
    have he := rightDualIso_evaluation
      (@HasRightDual.exact C _ _ (X ⊗ Y) (RightRigidCategory.rightDual _))
      (ExactPairing.tensor (X₁ := X) (X₂ := Y) (Y₁ := Xᘁ) (Y₂ := Yᘁ))
    simp only [comp_whiskerRight_assoc] at *
    change (rightDualTensorIso X Y).hom ▷ (X ⊗ Y) ≫
      ε_ (X ⊗ Y) ((Yᘁ) ⊗ (Xᘁ)) = ε_ (X ⊗ Y) ((X ⊗ Y)ᘁ) at he
    simp only [← Category.assoc, he]
    simp only [Category.assoc, rightAdjointMate_comp_evaluation]
    have aux := tensorPairing_evaluation_natural f g
    have he' := rightDualIso_evaluation
      (@HasRightDual.exact C _ _ (X' ⊗ Y') (RightRigidCategory.rightDual _))
      (ExactPairing.tensor (X₁ := X') (X₂ := Y') (Y₁ := X'ᘁ) (Y₂ := Y'ᘁ))
    change (rightDualTensorIso X' Y').hom ▷ (X' ⊗ Y') ≫
      ε_ (X' ⊗ Y') ((Y'ᘁ) ⊗ (X'ᘁ)) = ε_ (X' ⊗ Y') ((X' ⊗ Y')ᘁ) at he'
    calc
      _ = (X' ⊗ Y')ᘁ ◁ (f ⊗ₘ g) ≫ (rightDualTensorIso X' Y').hom ▷ (X' ⊗ Y') ≫
          ε_ (X' ⊗ Y') ((Y'ᘁ) ⊗ (X'ᘁ)) := by rw [he']
      _ = (rightDualTensorIso X' Y').hom ▷ (X ⊗ Y) ≫
          ((Y'ᘁ) ⊗ (X'ᘁ)) ◁ (f ⊗ₘ g) ≫ ε_ (X' ⊗ Y') ((Y'ᘁ) ⊗ (X'ᘁ)) := by
            rw [whisker_exchange_assoc]
      _ = _ := by rw [aux]
  exact evaluation_ext h

set_option backward.isDefEq.respectTransparency false in
/-- The inverse right-dual tensor comparison is natural. -/
theorem rightDualTensorIso_inv_natural {C : Type u} [Category.{v} C]
    [MonoidalCategory C] [RightRigidCategory C] {X X' Y Y' : C}
    (f : X ⟶ X') (g : Y ⟶ Y') :
    (gᘁ ⊗ₘ fᘁ) ≫ (rightDualTensorIso X Y).inv =
      (rightDualTensorIso X' Y').inv ≫ ((f ⊗ₘ g)ᘁ) := by
  apply (cancel_mono (rightDualTensorIso X Y).hom).1
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [rightDualTensorIso_natural]
  simp [← Category.assoc]

set_option backward.isDefEq.respectTransparency false in
/-- The canonical double-dual tensor comparison is natural in both factors. -/
theorem doubleDualTensorIso_natural {X X' Y Y' : C} (f : X ⟶ X') (g : Y ⟶ Y') :
    (((fᘁ)ᘁ) ⊗ₘ ((gᘁ)ᘁ)) ≫ (doubleDualTensorIso X' Y').hom =
      (doubleDualTensorIso X Y).hom ≫ (((f ⊗ₘ g)ᘁ)ᘁ) := by
  have h1' := rightDualTensorIso_inv_natural (gᘁ) (fᘁ)
  have h2 := congrArg (fun m => rightAdjointMate m) (rightDualTensorIso_natural f g)
  simp only [comp_rightAdjointMate] at h2
  simp only [doubleDualTensorIso, Iso.trans_hom, Iso.symm_hom, rightDualIsoMap, Category.assoc]
  rw [← Category.assoc, h1', Category.assoc, ← h2]
end PropertyF.Ground.Dimensions
