module
public import PropertyF.Ground.Dimensions.DualBraiding
public import PropertyF.Ground.Modular.SMatrix

/-! # Tensor caps and monodromy

Braiding and evaluation identities simplify the tensor-cap expression for monodromy.

## Main results

* `drinfeld_tensor_cap_factor`: expresses the Drinfeld tensor comparison through a tensor cap.
* `monodromy_tensor_cap_expansion`: expands the cap in terms of monodromy.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.BraidedCategory
open PropertyF.Ground
namespace PropertyF.Ground.Dimensions
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [RightRigidCategory C] (X Y : C)
omit [RightRigidCategory C] in
set_option backward.isDefEq.respectTransparency false in
/-- Evaluating the tensor of the two Drinfeld maps closes the two crossed caps in sequence. -/
theorem drinfeld_tensor_cap_factor [HasRightDual X] [HasRightDual (Xᘁ)]
    [HasRightDual Y] [HasRightDual (Yᘁ)] :
    let V := (Yᘁ) ⊗ (Xᘁ)
    ((drinfeldIso X).hom ⊗ₘ (drinfeldIso Y).hom) ▷ V ≫
      ε_ V (((Xᘁ)ᘁ) ⊗ ((Yᘁ)ᘁ)) =
      𝟙 ((X ⊗ Y) ⊗ V) ⊗≫ (X ◁ (β_ Y (Yᘁ)).hom) ▷ (Xᘁ) ⊗≫
        (X ◁ ε_ Y (Yᘁ)) ▷ (Xᘁ) ⊗≫ (β_ X (Xᘁ)).hom ⊗≫ ε_ X (Xᘁ) := by
  let U := Xᘁ
  let V := Yᘁ
  let a := (drinfeldIso X).hom
  let b := (drinfeldIso Y).hom
  let P := V ⊗ U
  change (a ⊗ₘ b) ▷ P ≫
      (𝟙 _ ⊗≫ (Uᘁ) ◁ (ε_ V (Vᘁ) ▷ U) ⊗≫ ε_ U (Uᘁ)) = _
  calc
    _ = 𝟙 _ ⊗≫ (X ◁ (b ▷ V ≫ ε_ V (Vᘁ))) ▷ U ⊗≫ (a ▷ U ≫ ε_ U (Uᘁ)) := by
      simp only [tensorHom_def, comp_whiskerRight, whiskerLeft_comp]
      monoidal
      simp
      rw [whisker_exchange_assoc a (λ_ U).hom,
        whisker_exchange_assoc a (ε_ V (Vᘁ) ▷ U),
        whisker_exchange_assoc a (b ▷ V ▷ U), ← comp_whiskerRight_assoc,
        associator_naturality_left, comp_whiskerRight, Category.assoc,
        associator_naturality_left_assoc]
      monoidal
    _ = _ := by rw [drinfeld_eval, drinfeld_eval]; monoidal
end PropertyF.Ground.Dimensions

end

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.BraidedCategory
open PropertyF.Ground
namespace PropertyF.Ground.Dimensions
universe v u

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [RightRigidCategory C] (X Y : C)
-- The two right duals and their tensor product appear throughout the cap calculation.
local notation "U" => (Xᘁ)
local notation "V" => (Yᘁ)
local notation "P" => (V ⊗ U)

omit [RightRigidCategory C] in
/-- The monodromy of two objects closed against their tensor-product dual. -/
abbrev monodromyTensorCap [HasRightDual X] [HasRightDual Y] :
    (X ⊗ Y) ⊗ ((Yᘁ) ⊗ (Xᘁ)) ⟶ 𝟙_ C :=
  (Modular.doubleBraiding X Y ▷ ((Yᘁ) ⊗ (Xᘁ))) ≫
    (β_ (X ⊗ Y) ((Yᘁ) ⊗ (Xᘁ))).hom ≫ ε_ (X ⊗ Y) ((Yᘁ) ⊗ (Xᘁ))

omit [RightRigidCategory C] in
set_option backward.isDefEq.respectTransparency false in
/-- Expand monodromy and tensor braiding into their six individual crossings. -/
theorem monodromy_tensor_cap_expansion [HasRightDual X] [HasRightDual Y] :
    monodromyTensorCap X Y =
    𝟙 ((X ⊗ Y) ⊗ P) ⊗≫ (β_ X Y).hom ▷ P ⊗≫ (β_ Y X).hom ▷ P ⊗≫
      (X ◁ (β_ Y V).hom) ▷ U ⊗≫ ((β_ X V).hom ▷ Y) ▷ U ⊗≫
      V ◁ (X ◁ (β_ Y U).hom) ⊗≫ V ◁ ((β_ X U).hom ▷ Y) ⊗≫
      V ◁ (ε_ X U ▷ Y) ⊗≫ ε_ Y V := by
  let W := X ⊗ Y
  change (((β_ X Y).hom ≫ (β_ Y X).hom) ▷ P) ≫ (β_ W P).hom ≫
      (𝟙 (P ⊗ W) ⊗≫ V ◁ (ε_ X U ▷ Y) ⊗≫ ε_ Y V) = _
  dsimp only [W]
  simp only [comp_whiskerRight, braiding_tensor_right_hom, braiding_tensor_left_hom]
  monoidal
omit [RightRigidCategory C] in
set_option backward.isDefEq.respectTransparency false in
/-- Reorder the six crossings using the Yang–Baxter identity twice. -/
theorem monodromy_tensor_cap_braid_reordered [HasRightDual X] [HasRightDual Y] :
    monodromyTensorCap X Y =
    𝟙 ((X ⊗ Y) ⊗ P) ⊗≫ (β_ X Y).hom ▷ P ⊗≫
      (Y ◁ (β_ X V).hom) ▷ U ⊗≫ ((β_ Y V).hom ▷ X) ▷ U ⊗≫
      V ◁ (Y ◁ (β_ X U).hom) ⊗≫ V ◁ ((β_ Y U).hom ▷ X) ⊗≫
      V ◁ (U ◁ (β_ Y X).hom) ⊗≫ V ◁ (ε_ X U ▷ Y) ⊗≫ ε_ Y V := by
  let W := X ⊗ Y
  rw [monodromy_tensor_cap_expansion]
  calc
    _ = 𝟙 (W ⊗ P) ⊗≫ (β_ X Y).hom ▷ P ⊗≫
      (((β_ Y X).hom ▷ V ⊗≫ X ◁ (β_ Y V).hom ⊗≫ (β_ X V).hom ▷ Y) ▷ U) ⊗≫
      V ◁ (X ◁ (β_ Y U).hom) ⊗≫ V ◁ ((β_ X U).hom ▷ Y) ⊗≫
      V ◁ (ε_ X U ▷ Y) ⊗≫ ε_ Y V := by
        simp only [monoidalComp, comp_whiskerRight]
        monoidal
    _ = 𝟙 (W ⊗ P) ⊗≫ (β_ X Y).hom ▷ P ⊗≫
      ((𝟙 ((Y ⊗ X) ⊗ V) ⊗≫ (Y ◁ (β_ X V).hom ⊗≫ (β_ Y V).hom ▷ X ⊗≫ V ◁ (β_ Y X).hom) ⊗≫ 𝟙 ((V ⊗ X) ⊗ Y)) ▷ U) ⊗≫
      V ◁ (X ◁ (β_ Y U).hom) ⊗≫ V ◁ ((β_ X U).hom ▷ Y) ⊗≫
      V ◁ (ε_ X U ▷ Y) ⊗≫ ε_ Y V := by rw [yang_baxter']
    _ = 𝟙 (W ⊗ P) ⊗≫ (β_ X Y).hom ▷ P ⊗≫
      (Y ◁ (β_ X V).hom) ▷ U ⊗≫ ((β_ Y V).hom ▷ X) ▷ U ⊗≫
      V ◁ ((β_ Y X).hom ▷ U ⊗≫ X ◁ (β_ Y U).hom ⊗≫ (β_ X U).hom ▷ Y) ⊗≫
      V ◁ (ε_ X U ▷ Y) ⊗≫ ε_ Y V := by
        simp only [monoidalComp, comp_whiskerRight, whiskerLeft_comp]
        monoidal
    _ = 𝟙 (W ⊗ P) ⊗≫ (β_ X Y).hom ▷ P ⊗≫
      (Y ◁ (β_ X V).hom) ▷ U ⊗≫ ((β_ Y V).hom ▷ X) ▷ U ⊗≫
      V ◁ (𝟙 ((Y ⊗ X) ⊗ U) ⊗≫ (Y ◁ (β_ X U).hom ⊗≫ (β_ Y U).hom ▷ X ⊗≫ U ◁ (β_ Y X).hom) ⊗≫ 𝟙 ((U ⊗ X) ⊗ Y)) ⊗≫
      V ◁ (ε_ X U ▷ Y) ⊗≫ ε_ Y V := by rw [yang_baxter']
    _ = _ := by
      simp only [monoidalComp, whiskerLeft_comp]
      monoidal
omit [RightRigidCategory C] in
set_option backward.isDefEq.respectTransparency false in
/-- A braiding loop around a morphism into the tensor unit contracts by naturality. -/
theorem braiding_cap_loop (X : C) {Y Z : C} (f : Y ⊗ Z ⟶ 𝟙_ C) :
    (β_ X Y).hom ▷ Z ⊗≫ Y ◁ (β_ X Z).hom ⊗≫ f ▷ X ⊗≫ (λ_ X).hom =
      𝟙 ((X ⊗ Y) ⊗ Z) ⊗≫ X ◁ f ⊗≫ (ρ_ X).hom := by
  calc
    _ = (α_ X Y Z).hom ≫ (β_ X (Y ⊗ Z)).hom ≫ f ▷ X ≫ (λ_ X).hom := by
      rw [braiding_tensor_right_hom]
      monoidal
    _ = _ := by
      rw [← braiding_naturality_right_assoc, braiding_leftUnitor]
      monoidal
omit [RightRigidCategory C] in
set_option backward.isDefEq.respectTransparency false in
/-- Contract the first braiding loop in the monodromy evaluation. -/
theorem monodromy_tensor_cap_remove_loop [HasRightDual X] [HasRightDual Y] :
    monodromyTensorCap X Y =
    𝟙 ((X ⊗ Y) ⊗ P) ⊗≫ (β_ X Y).hom ▷ P ⊗≫
      (Y ◁ (β_ X V).hom) ▷ U ⊗≫ ((β_ Y V).hom ▷ X) ▷ U ⊗≫
      V ◁ (Y ◁ (β_ X U).hom) ⊗≫ V ◁ (Y ◁ ε_ X U) ⊗≫ ε_ Y V := by
  let W := X ⊗ Y
  rw [monodromy_tensor_cap_braid_reordered]
  calc
    _ = 𝟙 (W ⊗ P) ⊗≫ (β_ X Y).hom ▷ P ⊗≫
      (Y ◁ (β_ X V).hom) ▷ U ⊗≫ ((β_ Y V).hom ▷ X) ▷ U ⊗≫
      V ◁ (Y ◁ (β_ X U).hom) ⊗≫
      V ◁ ((β_ Y U).hom ▷ X ⊗≫ U ◁ (β_ Y X).hom ⊗≫ ε_ X U ▷ Y ⊗≫ (λ_ Y).hom) ⊗≫ ε_ Y V := by
        simp only [monoidalComp, whiskerLeft_comp]
        monoidal
    _ = 𝟙 (W ⊗ P) ⊗≫ (β_ X Y).hom ▷ P ⊗≫
      (Y ◁ (β_ X V).hom) ▷ U ⊗≫ ((β_ Y V).hom ▷ X) ▷ U ⊗≫
      V ◁ (Y ◁ (β_ X U).hom) ⊗≫
      V ◁ (𝟙 ((Y ⊗ U) ⊗ X) ⊗≫ Y ◁ ε_ X U ⊗≫ (ρ_ Y).hom) ⊗≫ ε_ Y V := by
        rw [braiding_cap_loop]
    _ = _ := by
      simp only [monoidalComp, whiskerLeft_comp]
      monoidal
omit [RightRigidCategory C] in
set_option backward.isDefEq.respectTransparency false in
/-- The monodromy tensor evaluation closes the two crossed caps in sequence. -/
theorem monodromy_tensor_cap_evaluated [HasRightDual X] [HasRightDual Y] :
    monodromyTensorCap X Y =
    𝟙 ((X ⊗ Y) ⊗ P) ⊗≫ (X ◁ (β_ Y V).hom) ▷ U ⊗≫
      (X ◁ ε_ Y V) ▷ U ⊗≫ (β_ X U).hom ⊗≫ ε_ X U := by
  let W := X ⊗ Y
  let I := 𝟙_ C
  let g : X ⊗ U ⟶ I := (β_ X U).hom ≫ ε_ X U
  let b : Y ⊗ V ⟶ I := (β_ Y V).hom ≫ ε_ Y V
  rw [monodromy_tensor_cap_remove_loop]
  calc
    _ = 𝟙 (W ⊗ P) ⊗≫ (β_ X Y).hom ▷ P ⊗≫
      (Y ◁ (β_ X V).hom) ▷ U ⊗≫ (β_ Y V).hom ▷ (X ⊗ U) ⊗≫
      ((V ⊗ Y) ◁ g ≫ ε_ Y V ▷ I) ⊗≫ 𝟙 I := by
        simp only [g, monoidalComp, whiskerLeft_comp]
        monoidal
    _ = 𝟙 (W ⊗ P) ⊗≫ (β_ X Y).hom ▷ P ⊗≫
      (Y ◁ (β_ X V).hom) ▷ U ⊗≫ (β_ Y V).hom ▷ (X ⊗ U) ⊗≫
      (ε_ Y V ▷ (X ⊗ U) ≫ I ◁ g) ⊗≫ 𝟙 I := by rw [whisker_exchange]
    _ = 𝟙 (W ⊗ P) ⊗≫
      (((β_ X Y).hom ▷ V ⊗≫ Y ◁ (β_ X V).hom ⊗≫ b ▷ X ⊗≫ (λ_ X).hom) ▷ U) ⊗≫ g := by
        simp only [b, monoidalComp, comp_whiskerRight]
        monoidal
    _ = 𝟙 (W ⊗ P) ⊗≫
      ((𝟙 ((X ⊗ Y) ⊗ V) ⊗≫ X ◁ b ⊗≫ (ρ_ X).hom) ▷ U) ⊗≫ g := by
        rw [braiding_cap_loop]
    _ = _ := by
      simp only [b, g, monoidalComp, comp_whiskerRight, whiskerLeft_comp]
      monoidal
omit [RightRigidCategory C] in
/-- The actual Drinfeld tensor pairing cap identity holds for chosen duals. -/
theorem drinfeld_tensor_pairing_cap [HasRightDual X] [HasRightDual (Xᘁ)]
    [HasRightDual Y] [HasRightDual (Yᘁ)] :
    monodromyTensorCap X Y =
      ((drinfeldIso X).hom ⊗ₘ (drinfeldIso Y).hom) ▷ ((Yᘁ) ⊗ (Xᘁ)) ≫
        ε_ ((Yᘁ) ⊗ (Xᘁ)) (((Xᘁ)ᘁ) ⊗ ((Yᘁ)ᘁ)) :=
  (monodromy_tensor_cap_evaluated X Y).trans (drinfeld_tensor_cap_factor X Y).symm
end PropertyF.Ground.Dimensions

end
