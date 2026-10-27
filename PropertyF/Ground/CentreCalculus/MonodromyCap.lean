module
public import PropertyF.Ground.Dimensions.DualBraiding
public import PropertyF.Ground.Modular.SMatrix

/-! Sliding double braidings through tensor-product evaluation. -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.BraidedCategory
namespace PropertyF.Ground.CentreCalculus
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [BraidedCategory C] [RightRigidCategory C]

set_option backward.isDefEq.respectTransparency false in
/-- A double braiding on a tensor product can be moved through its evaluation
cap to the reversed double braiding of the two dual strands. -/
theorem doubleBraiding_tensor_evaluation (X Y : C) :
    let W := X ⊗ Y
    let V := (Yᘁ) ⊗ (Xᘁ)
    let p : ExactPairing W V := ExactPairing.tensor
    V ◁ Modular.doubleBraiding X Y ≫ @ExactPairing.evaluation C _ _ W V p =
      Modular.doubleBraiding (Yᘁ) (Xᘁ) ▷ W ≫ @ExactPairing.evaluation C _ _ W V p := by
  let U := Xᘁ
  let V := Yᘁ
  let p : ExactPairing (X ⊗ Y) (V ⊗ U) := ExactPairing.tensor
  let q : ExactPairing (Y ⊗ X) (U ⊗ V) := ExactPairing.tensor
  have h1 := Dimensions.dual_braiding_tensor_evaluations Y X
  change (β_ V U).hom ▷ (Y ⊗ X) ≫ @ExactPairing.evaluation C _ _ (Y ⊗ X) (U ⊗ V) q =
    (V ⊗ U) ◁ (β_ Y X).hom ≫ @ExactPairing.evaluation C _ _ (X ⊗ Y) (V ⊗ U) p at h1
  have h2 := Dimensions.dual_braiding_tensor_evaluations X Y
  change (β_ U V).hom ▷ (X ⊗ Y) ≫ @ExactPairing.evaluation C _ _ (X ⊗ Y) (V ⊗ U) p =
    (U ⊗ V) ◁ (β_ X Y).hom ≫ @ExactPairing.evaluation C _ _ (Y ⊗ X) (U ⊗ V) q at h2
  change (V ⊗ U) ◁ ((β_ X Y).hom ≫ (β_ Y X).hom) ≫
      @ExactPairing.evaluation C _ _ (X ⊗ Y) (V ⊗ U) p =
    ((β_ V U).hom ≫ (β_ U V).hom) ▷ (X ⊗ Y) ≫
      @ExactPairing.evaluation C _ _ (X ⊗ Y) (V ⊗ U) p
  simp only [whiskerLeft_comp, comp_whiskerRight, Category.assoc]
  rw [← h1]
  rw [whisker_exchange_assoc]
  rw [← h2]

end PropertyF.Ground.CentreCalculus
