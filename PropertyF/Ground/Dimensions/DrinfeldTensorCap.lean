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
