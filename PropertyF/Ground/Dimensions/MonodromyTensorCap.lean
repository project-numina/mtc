module
public import PropertyF.Ground.Dimensions.DualBraiding
public import PropertyF.Ground.Modular.SMatrix

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.BraidedCategory
open PropertyF.Ground
namespace PropertyF.Ground.Dimensions
universe v u
set_option backward.isDefEq.respectTransparency false in
/-- Evaluating the tensor of the two Drinfeld maps closes the two crossed caps in sequence. -/
theorem drinfeld_tensor_cap_factor (C : BraidedFusionCategory.{v,u}) (X Y : C.Obj) :
    let W := X ⊗ Y
    let V := (Yᘁ) ⊗ (Xᘁ)
    let q : ExactPairing V (((Xᘁ)ᘁ) ⊗ ((Yᘁ)ᘁ)) := ExactPairing.tensor
    ((doubleDualIso C X).hom ⊗ₘ (doubleDualIso C Y).hom) ▷ V ≫
      @ExactPairing.evaluation C.Obj _ _ V _ q =
      𝟙 (W ⊗ V) ⊗≫ (X ◁ (β_ Y (Yᘁ)).hom) ▷ (Xᘁ) ⊗≫
        (X ◁ ε_ Y (Yᘁ)) ▷ (Xᘁ) ⊗≫ (β_ X (Xᘁ)).hom ⊗≫ ε_ X (Xᘁ) := by
  let U := Xᘁ
  let V := Yᘁ
  let a := (doubleDualIso C X).hom
  let b := (doubleDualIso C Y).hom
  let W := X ⊗ Y
  let P := V ⊗ U
  let q : ExactPairing P ((Uᘁ) ⊗ (Vᘁ)) := ExactPairing.tensor
  change (a ⊗ₘ b) ▷ P ≫ @ExactPairing.evaluation C.Obj _ _ P _ q = _
  change (a ⊗ₘ b) ▷ P ≫
      (𝟙 _ ⊗≫ (Uᘁ) ◁ (ε_ V (Vᘁ) ▷ U) ⊗≫ ε_ U (Uᘁ)) = _
  calc
    _ = 𝟙 _ ⊗≫ (X ◁ (b ▷ V ≫ ε_ V (Vᘁ))) ▷ U ⊗≫ (a ▷ U ≫ ε_ U (Uᘁ)) := by
      simp only [tensorHom_def, comp_whiskerRight, whiskerLeft_comp]
      monoidal
      simp
      rw [whisker_exchange_assoc a (λ_ U).hom]
      rw [whisker_exchange_assoc a (ε_ V (Vᘁ) ▷ U)]
      rw [whisker_exchange_assoc a (b ▷ V ▷ U)]
      rw [← comp_whiskerRight_assoc, associator_naturality_left]
      rw [comp_whiskerRight, Category.assoc, associator_naturality_left_assoc]
      monoidal
    _ = _ := by rw [drinfeld_eval, drinfeld_eval]; monoidal
end PropertyF.Ground.Dimensions

end

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.BraidedCategory
open PropertyF.Ground
namespace PropertyF.Ground.Dimensions
universe v u

section
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [BraidedCategory C] [RightRigidCategory C]

end

set_option backward.isDefEq.respectTransparency false in
/-- Expand monodromy and tensor braiding into their six individual crossings. -/
theorem monodromy_tensor_cap_expansion (C : BraidedFusionCategory.{v,u}) (X Y : C.Obj) :
    let U := Xᘁ
    let V := Yᘁ
    let W := X ⊗ Y
    let P := V ⊗ U
    let p : ExactPairing W P := ExactPairing.tensor
    (Modular.doubleBraiding X Y ▷ P) ≫ (β_ W P).hom ≫ @ExactPairing.evaluation C.Obj _ _ W P p =
    𝟙 (W ⊗ P) ⊗≫ (β_ X Y).hom ▷ P ⊗≫ (β_ Y X).hom ▷ P ⊗≫
      (X ◁ (β_ Y V).hom) ▷ U ⊗≫ ((β_ X V).hom ▷ Y) ▷ U ⊗≫
      V ◁ (X ◁ (β_ Y U).hom) ⊗≫ V ◁ ((β_ X U).hom ▷ Y) ⊗≫
      V ◁ (ε_ X U ▷ Y) ⊗≫ ε_ Y V := by
  let U := Xᘁ
  let V := Yᘁ
  let W := X ⊗ Y
  let P := V ⊗ U
  let p : ExactPairing W P := ExactPairing.tensor
  change (((β_ X Y).hom ≫ (β_ Y X).hom) ▷ P) ≫ (β_ W P).hom ≫
      (𝟙 (P ⊗ W) ⊗≫ V ◁ (ε_ X U ▷ Y) ⊗≫ ε_ Y V) = _
  dsimp only [W, P]
  simp only [comp_whiskerRight, braiding_tensor_right_hom, braiding_tensor_left_hom]
  monoidal
set_option backward.isDefEq.respectTransparency false in
/-- Reorder the six crossings using the Yang–Baxter identity twice. -/
theorem monodromy_tensor_cap_braid_reordered (C : BraidedFusionCategory.{v,u}) (X Y : C.Obj) :
    let U := Xᘁ
    let V := Yᘁ
    let W := X ⊗ Y
    let P := V ⊗ U
    let p : ExactPairing W P := ExactPairing.tensor
    (Modular.doubleBraiding X Y ▷ P) ≫ (β_ W P).hom ≫ @ExactPairing.evaluation C.Obj _ _ W P p =
    𝟙 (W ⊗ P) ⊗≫ (β_ X Y).hom ▷ P ⊗≫
      (Y ◁ (β_ X V).hom) ▷ U ⊗≫ ((β_ Y V).hom ▷ X) ▷ U ⊗≫
      V ◁ (Y ◁ (β_ X U).hom) ⊗≫ V ◁ ((β_ Y U).hom ▷ X) ⊗≫
      V ◁ (U ◁ (β_ Y X).hom) ⊗≫ V ◁ (ε_ X U ▷ Y) ⊗≫ ε_ Y V := by
  let U := Xᘁ
  let V := Yᘁ
  let W := X ⊗ Y
  let P := V ⊗ U
  dsimp only
  rw [monodromy_tensor_cap_expansion]
  calc
    _ = 𝟙 (W ⊗ P) ⊗≫ (β_ X Y).hom ▷ P ⊗≫
      (((β_ Y X).hom ▷ V ⊗≫ X ◁ (β_ Y V).hom ⊗≫ (β_ X V).hom ▷ Y) ▷ U) ⊗≫
      V ◁ (X ◁ (β_ Y U).hom) ⊗≫ V ◁ ((β_ X U).hom ▷ Y) ⊗≫
      V ◁ (ε_ X U ▷ Y) ⊗≫ ε_ Y V := by
        simp only [monoidalComp, comp_whiskerRight, whiskerLeft_comp]
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
      simp only [monoidalComp, comp_whiskerRight, whiskerLeft_comp]
      monoidal
set_option backward.isDefEq.respectTransparency false in
/-- A braiding loop around an evaluation cap contracts by naturality. -/
theorem braiding_right_cap_loop {C : Type u} [Category.{v} C] [MonoidalCategory C]
    [BraidedCategory C] [RightRigidCategory C] (X Y : C) :
    (β_ Y (Xᘁ)).hom ▷ X ⊗≫ (Xᘁ) ◁ (β_ Y X).hom ⊗≫
      ε_ X (Xᘁ) ▷ Y ⊗≫ (λ_ Y).hom =
      𝟙 ((Y ⊗ (Xᘁ)) ⊗ X) ⊗≫ Y ◁ ε_ X (Xᘁ) ⊗≫ (ρ_ Y).hom := by
  have hn := braiding_naturality_right Y (ε_ X (Xᘁ))
  have h := congrArg (fun f => f ≫ (λ_ Y).hom) hn
  simp only [Category.assoc, braiding_leftUnitor] at h
  calc
    _ = (α_ Y (Xᘁ) X).hom ≫ (β_ Y ((Xᘁ) ⊗ X)).hom ≫
        (ε_ X (Xᘁ) ▷ Y) ≫ (λ_ Y).hom := by
      rw [braiding_tensor_right_hom]
      monoidal
    _ = _ := by rw [← h]; monoidal
set_option backward.isDefEq.respectTransparency false in
/-- Contract the first braiding loop in the monodromy evaluation. -/
theorem monodromy_tensor_cap_remove_loop (C : BraidedFusionCategory.{v,u}) (X Y : C.Obj) :
    let U := Xᘁ
    let V := Yᘁ
    let W := X ⊗ Y
    let P := V ⊗ U
    let p : ExactPairing W P := ExactPairing.tensor
    (Modular.doubleBraiding X Y ▷ P) ≫ (β_ W P).hom ≫ @ExactPairing.evaluation C.Obj _ _ W P p =
    𝟙 (W ⊗ P) ⊗≫ (β_ X Y).hom ▷ P ⊗≫
      (Y ◁ (β_ X V).hom) ▷ U ⊗≫ ((β_ Y V).hom ▷ X) ▷ U ⊗≫
      V ◁ (Y ◁ (β_ X U).hom) ⊗≫ V ◁ (Y ◁ ε_ X U) ⊗≫ ε_ Y V := by
  let U := Xᘁ
  let V := Yᘁ
  let W := X ⊗ Y
  let P := V ⊗ U
  dsimp only
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
        rw [braiding_right_cap_loop]
    _ = _ := by
      simp only [monoidalComp, whiskerLeft_comp]
      monoidal
set_option backward.isDefEq.respectTransparency false in
/-- A braiding loop contracts around a crossed evaluation cap. -/
theorem braiding_crossed_cap_loop {C : Type u} [Category.{v} C] [MonoidalCategory C]
    [BraidedCategory C] [RightRigidCategory C] (X Y : C) :
    (β_ X Y).hom ▷ (Yᘁ) ⊗≫ Y ◁ (β_ X (Yᘁ)).hom ⊗≫
      ((β_ Y (Yᘁ)).hom ≫ ε_ Y (Yᘁ)) ▷ X ⊗≫ (λ_ X).hom =
      𝟙 ((X ⊗ Y) ⊗ (Yᘁ)) ⊗≫ X ◁ ((β_ Y (Yᘁ)).hom ≫ ε_ Y (Yᘁ)) ⊗≫ (ρ_ X).hom := by
  let b := (β_ Y (Yᘁ)).hom ≫ ε_ Y (Yᘁ)
  have hn := braiding_naturality_right X b
  have h := congrArg (fun f => f ≫ (λ_ X).hom) hn
  simp only [Category.assoc, braiding_leftUnitor] at h
  calc
    _ = (α_ X Y (Yᘁ)).hom ≫ (β_ X (Y ⊗ (Yᘁ))).hom ≫ b ▷ X ≫ (λ_ X).hom := by
      rw [braiding_tensor_right_hom]
      monoidal
    _ = _ := by rw [← h]; monoidal
set_option backward.isDefEq.respectTransparency false in
/-- The monodromy tensor evaluation closes the two crossed caps in sequence. -/
theorem monodromy_tensor_cap_evaluated (C : BraidedFusionCategory.{v,u}) (X Y : C.Obj) :
    let U := Xᘁ
    let V := Yᘁ
    let W := X ⊗ Y
    let P := V ⊗ U
    let p : ExactPairing W P := ExactPairing.tensor
    (Modular.doubleBraiding X Y ▷ P) ≫ (β_ W P).hom ≫ @ExactPairing.evaluation C.Obj _ _ W P p =
    𝟙 (W ⊗ P) ⊗≫ (X ◁ (β_ Y V).hom) ▷ U ⊗≫
      (X ◁ ε_ Y V) ▷ U ⊗≫ (β_ X U).hom ⊗≫ ε_ X U := by
  let U := Xᘁ
  let V := Yᘁ
  let W := X ⊗ Y
  let P := V ⊗ U
  let I := 𝟙_ C.Obj
  let g : X ⊗ U ⟶ I := (β_ X U).hom ≫ ε_ X U
  let b : Y ⊗ V ⟶ I := (β_ Y V).hom ≫ ε_ Y V
  dsimp only
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
        rw [braiding_crossed_cap_loop]
    _ = _ := by
      simp only [b, g, monoidalComp, comp_whiskerRight, whiskerLeft_comp]
      monoidal
/-- The actual Drinfeld tensor pairing cap identity holds for all objects. -/
theorem drinfeld_tensor_pairing_cap (C : BraidedFusionCategory.{v,u}) (X Y : C.Obj) :
    let W := X ⊗ Y
    let V := (Yᘁ) ⊗ (Xᘁ)
    let p : ExactPairing W V := ExactPairing.tensor
    let q : ExactPairing V (((Xᘁ)ᘁ) ⊗ ((Yᘁ)ᘁ)) := ExactPairing.tensor
    (Modular.doubleBraiding X Y ▷ V) ≫ (β_ W V).hom ≫
      @ExactPairing.evaluation C.Obj _ _ W V p =
    ((doubleDualIso C X).hom ⊗ₘ (doubleDualIso C Y).hom) ▷ V ≫
      @ExactPairing.evaluation C.Obj _ _ V _ q :=
  (monodromy_tensor_cap_evaluated C X Y).trans (drinfeld_tensor_cap_factor C X Y).symm
end PropertyF.Ground.Dimensions

end
