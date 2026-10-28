module
public import PropertyF.Ground.Dimensions.DualTensorNaturality

/-! # Braiding and dual tensor products

Evaluation cap slides show that the right-dual tensor comparison transports the braiding.

## Main results

* `braiding_cap_slide`: slides a braiding past an evaluation cap.
* `rightDualTensorIso_braiding`: establishes the braiding law for the right-dual tensor comparison.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.BraidedCategory
namespace PropertyF.Ground.Dimensions
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
variable {U W : C} (V : C) (f : U ⊗ W ⟶ 𝟙_ C)
set_option backward.isDefEq.respectTransparency false in
/-- A braiding slides past a morphism into the tensor unit. -/
theorem braiding_cap_slide :
    (β_ U V).hom ▷ W ⊗≫ V ◁ f ⊗≫ (ρ_ V).hom =
      𝟙 ((U ⊗ V) ⊗ W) ⊗≫ U ◁ (β_ W V).inv ⊗≫ f ▷ V ⊗≫ (λ_ V).hom := by
  have h := congrArg (fun g => g ≫ (ρ_ V).hom) (braiding_naturality_left f V)
  simp only [braiding_tensor_left_hom, Category.assoc, braiding_rightUnitor] at h
  calc
    _ = (α_ U V W).hom ≫ U ◁ (β_ W V).inv ≫ (α_ U W V).inv ≫
      (f ▷ V ≫ (λ_ V).hom) := by
        rw [h]
        simp only [Iso.inv_hom_id_assoc, ← whiskerLeft_comp_assoc,
          Iso.inv_hom_id, whiskerLeft_id, Category.id_comp, Iso.hom_inv_id_assoc]
        monoidal
    _ = _ := by monoidal
end PropertyF.Ground.Dimensions

end

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.BraidedCategory
namespace PropertyF.Ground.Dimensions
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [BraidedCategory C] [RightRigidCategory C]
variable (X Y : C)
set_option backward.isDefEq.respectTransparency false in
/-- Sliding the crossing through both caps relates the two tensor evaluations. -/
theorem dual_braiding_tensor_evaluations :
    (β_ (Xᘁ) (Yᘁ)).hom ▷ (X ⊗ Y) ≫ ε_ (X ⊗ Y) ((Yᘁ) ⊗ (Xᘁ)) =
      ((Xᘁ) ⊗ (Yᘁ)) ◁ (β_ X Y).hom ≫ ε_ (Y ⊗ X) ((Xᘁ) ⊗ (Yᘁ)) := by
  let U := Xᘁ
  let V := Yᘁ
  let p : ExactPairing (X ⊗ Y) (V ⊗ U) := ExactPairing.tensor
  let q : ExactPairing (Y ⊗ X) (U ⊗ V) := ExactPairing.tensor
  change (β_ U V).hom ▷ (X ⊗ Y) ≫ @ExactPairing.evaluation C _ _ _ _ p =
    (U ⊗ V) ◁ (β_ X Y).hom ≫ @ExactPairing.evaluation C _ _ _ _ q
  change (β_ U V).hom ▷ (X ⊗ Y) ≫
    (𝟙 _ ⊗≫ V ◁ (ε_ X U ▷ Y) ⊗≫ ε_ Y V) =
    (U ⊗ V) ◁ (β_ X Y).hom ≫
      (𝟙 _ ⊗≫ U ◁ (ε_ Y V ▷ X) ⊗≫ ε_ X U)
  calc
    _ = 𝟙 _ ⊗≫ ((β_ U V).hom ▷ X ⊗≫ V ◁ ε_ X U ⊗≫ (ρ_ V).hom) ▷ Y ⊗≫ ε_ Y V := by monoidal
    _ = 𝟙 _ ⊗≫ ((𝟙 ((U ⊗ V) ⊗ X) ⊗≫ U ◁ (β_ X V).inv ⊗≫ ε_ X U ▷ V ⊗≫ (λ_ V).hom) ▷ Y) ⊗≫ ε_ Y V := by
      rw [braiding_cap_slide]
    _ = 𝟙 _ ⊗≫ (U ◁ (β_ X V).inv) ▷ Y ⊗≫
        (ε_ X U ▷ (V ⊗ Y) ≫ (𝟙_ C) ◁ ε_ Y V) ⊗≫ 𝟙 (𝟙_ C) := by monoidal
    _ = 𝟙 _ ⊗≫ (U ◁ (β_ X V).inv) ▷ Y ⊗≫
        ((U ⊗ X) ◁ ε_ Y V ≫ ε_ X U ▷ (𝟙_ C)) ⊗≫ 𝟙 (𝟙_ C) := by rw [whisker_exchange]
    _ = 𝟙 _ ⊗≫ U ◁ ((β_ X V).inv ▷ Y ⊗≫ X ◁ ε_ Y V ⊗≫ (ρ_ X).hom) ⊗≫ ε_ X U := by monoidal
    _ = 𝟙 _ ⊗≫ U ◁ (𝟙 ((V ⊗ X) ⊗ Y) ⊗≫ V ◁ (β_ X Y).hom ⊗≫ ε_ Y V ▷ X ⊗≫ (λ_ X).hom) ⊗≫ ε_ X U := by
      rw [show (β_ X V).inv ▷ Y ⊗≫ X ◁ ε_ Y V ⊗≫ (ρ_ X).hom =
        𝟙 ((V ⊗ X) ⊗ Y) ⊗≫ V ◁ (β_ X Y).hom ⊗≫ ε_ Y V ▷ X ⊗≫ (λ_ X).hom from
          @braiding_cap_slide C _ _ (reverseBraiding C) V Y X (ε_ Y V)]
    _ = _ := by monoidal
set_option backward.isDefEq.respectTransparency false in
/-- The right-dual tensor comparison transports a braiding to the braiding of the duals. -/
theorem rightDualTensorIso_braiding :
    ((β_ X Y).homᘁ) ≫ (rightDualTensorIso X Y).hom =
      (rightDualTensorIso Y X).hom ≫ (β_ (Xᘁ) (Yᘁ)).hom :=
  evaluation_ext (X := X ⊗ Y) (by
    simp only [comp_whiskerRight_assoc, rightDualTensorIso_evaluation,
      rightAdjointMate_comp_evaluation]
    rw [dual_braiding_tensor_evaluations, ← whisker_exchange_assoc,
      rightDualTensorIso_evaluation])
end PropertyF.Ground.Dimensions

end
