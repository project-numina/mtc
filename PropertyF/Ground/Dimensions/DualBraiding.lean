module
public import PropertyF.Ground.Dimensions.BraidingCapSlide

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.BraidedCategory
namespace PropertyF.Ground.Dimensions
universe v u
set_option backward.isDefEq.respectTransparency false in
/-- Sliding the crossing through both caps relates the two tensor evaluations. -/
theorem dual_braiding_tensor_evaluations {C : Type u} [Category.{v} C] [MonoidalCategory C]
    [BraidedCategory C] [RightRigidCategory C] (X Y : C) :
    let p : ExactPairing (X ⊗ Y) ((Yᘁ) ⊗ (Xᘁ)) := ExactPairing.tensor
    let q : ExactPairing (Y ⊗ X) ((Xᘁ) ⊗ (Yᘁ)) := ExactPairing.tensor
    (β_ (Xᘁ) (Yᘁ)).hom ▷ (X ⊗ Y) ≫ @ExactPairing.evaluation C _ _ _ _ p =
      ((Xᘁ) ⊗ (Yᘁ)) ◁ (β_ X Y).hom ≫ @ExactPairing.evaluation C _ _ _ _ q := by
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
      rw [braiding_inverse_cap_slide]
    _ = _ := by monoidal
set_option backward.isDefEq.respectTransparency false in
/-- The right-dual tensor comparison transports a braiding to the braiding of the duals. -/
theorem rightDualTensorIso_braiding {C : Type u} [Category.{v} C] [MonoidalCategory C]
    [BraidedCategory C] [RightRigidCategory C] (X Y : C) :
    ((β_ X Y).homᘁ) ≫ (rightDualTensorIso X Y).hom =
      (rightDualTensorIso Y X).hom ≫ (β_ (Xᘁ) (Yᘁ)).hom := by
  let U := Xᘁ
  let V := Yᘁ
  let I := 𝟙_ C
  let W := X ⊗ Y
  let W' := Y ⊗ X
  let : HasRightDual W := RightRigidCategory.rightDual W
  let : HasRightDual W' := RightRigidCategory.rightDual W'
  let p : ExactPairing W (V ⊗ U) := ExactPairing.tensor
  let q : ExactPairing W' (U ⊗ V) := ExactPairing.tensor
  let t : Wᘁ ≅ V ⊗ U := rightDualTensorIso X Y
  let s : W'ᘁ ≅ U ⊗ V := rightDualTensorIso Y X
  let l : W'ᘁ ⟶ V ⊗ U := ((β_ X Y).homᘁ) ≫ t.hom
  let r : W'ᘁ ⟶ V ⊗ U := s.hom ≫ (β_ U V).hom
  have hp := rightDualIso_evaluation
    (@HasRightDual.exact C _ _ W (RightRigidCategory.rightDual W)) p
  change t.hom ▷ W ≫ @ExactPairing.evaluation C _ _ _ _ p = ε_ W (Wᘁ) at hp
  have hq := rightDualIso_evaluation
    (@HasRightDual.exact C _ _ W' (RightRigidCategory.rightDual W')) q
  change s.hom ▷ W' ≫ @ExactPairing.evaluation C _ _ _ _ q = ε_ W' (W'ᘁ) at hq
  have hc := dual_braiding_tensor_evaluations X Y
  change (β_ U V).hom ▷ W ≫ @ExactPairing.evaluation C _ _ _ _ p =
    (U ⊗ V) ◁ (β_ X Y).hom ≫ @ExactPairing.evaluation C _ _ _ _ q at hc
  have hl : l ▷ W ≫ @ExactPairing.evaluation C _ _ _ _ p =
      (W'ᘁ) ◁ (β_ X Y).hom ≫ ε_ W' (W'ᘁ) := by
    dsimp [l]
    rw [comp_whiskerRight_assoc, hp, rightAdjointMate_comp_evaluation]
  have hr : r ▷ W ≫ @ExactPairing.evaluation C _ _ _ _ p =
      (W'ᘁ) ◁ (β_ X Y).hom ≫ ε_ W' (W'ᘁ) := by
    dsimp [r]
    rw [comp_whiskerRight_assoc, hc, ← Category.assoc, ← whisker_exchange, Category.assoc, hq]
  have h := hl.trans hr.symm
  let : HasRightDual W := { rightDual := V ⊗ U, exact := p }
  have hh := congrArg (tensorRightHomEquiv (W'ᘁ) W (V ⊗ U) (𝟙_ C)) h
  have hL := @tensorRightHomEquiv_whiskerRight_comp_evaluation C _ _ W (W'ᘁ) this l
  have hR := @tensorRightHomEquiv_whiskerRight_comp_evaluation C _ _ W (W'ᘁ) this r
  change (tensorRightHomEquiv (W'ᘁ) W (V ⊗ U) I)
    (l ▷ W ≫ @ExactPairing.evaluation C _ _ _ _ p) = l ≫ (λ_ (V ⊗ U)).inv at hL
  change (tensorRightHomEquiv (W'ᘁ) W (V ⊗ U) I)
    (r ▷ W ≫ @ExactPairing.evaluation C _ _ _ _ p) = r ≫ (λ_ (V ⊗ U)).inv at hR
  rw [hL, hR] at hh
  exact (cancel_mono (λ_ (V ⊗ U)).inv).1 hh
end PropertyF.Ground.Dimensions
