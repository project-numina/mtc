module
public import PropertyF.Ground.Dimensions.DoubleDualMonoidal

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.Dimensions
universe v u
set_option backward.isDefEq.respectTransparency false in
/-- Closing the middle dual pair in the tensor-product coevaluation recovers
the coevaluation of the right dual. -/
theorem tensorPairing_coevaluation_evaluation {C : Type u} [Category.{v} C]
    [MonoidalCategory C] [RightRigidCategory C] (X : C) :
    let W := (Xᘁ) ⊗ X
    let V := (Xᘁ) ⊗ ((Xᘁ)ᘁ)
    letI : ExactPairing W V := ExactPairing.tensor
    η_ W V ≫ (ε_ X (Xᘁ) ▷ V) ≫ (λ_ V).hom = η_ (Xᘁ) ((Xᘁ)ᘁ) := by
  let W := (Xᘁ) ⊗ X
  let V := (Xᘁ) ⊗ ((Xᘁ)ᘁ)
  let q : ExactPairing W V := ExactPairing.tensor
  let : ExactPairing W V := q
  change @ExactPairing.coevaluation C _ _ W V q ≫ (ε_ X (Xᘁ) ▷ V) ≫ (λ_ V).hom = _
  have hq : @ExactPairing.coevaluation C _ _ W V q =
      (η_ (Xᘁ) ((Xᘁ)ᘁ) ⊗≫ ((Xᘁ) ◁ η_ X (Xᘁ)) ▷ ((Xᘁ)ᘁ) ⊗≫ 𝟙 (W ⊗ V)) := by
    change (@ExactPairing.tensor C _ _ (Xᘁ) X ((Xᘁ)ᘁ) (Xᘁ)
      HasRightDual.exact HasRightDual.exact).coevaluation' = _
    unfold ExactPairing.tensor
    dsimp
  rw [hq]
  calc
    _ = η_ (Xᘁ) ((Xᘁ)ᘁ) ⊗≫
      (((Xᘁ) ◁ η_ X (Xᘁ) ≫ (α_ (Xᘁ) X (Xᘁ)).inv ≫ ε_ X (Xᘁ) ▷ (Xᘁ)) ▷ ((Xᘁ)ᘁ)) ⊗≫ 𝟙 _ := by
        simp only [comp_whiskerRight]
        monoidal
    _ = _ := by
      rw [ExactPairing.coevaluation_evaluation]
      monoidal
set_option backward.isDefEq.respectTransparency false in
/-- Dualizing evaluation and transporting the dual of a tensor product gives
the coevaluation of the dual object. -/
theorem rightDualEvaluation_coevaluation {C : Type u} [Category.{v} C]
    [MonoidalCategory C] [RightRigidCategory C] (X : C) :
    letI : HasRightDual (𝟙_ C) := RightRigidCategory.rightDual (𝟙_ C)
    (rightDualUnitIso (C := C)).inv ≫ ((ε_ X (Xᘁ))ᘁ) ≫
      (rightDualTensorIso (Xᘁ) X).hom = η_ (Xᘁ) ((Xᘁ)ᘁ) := by
  let I := 𝟙_ C
  let : HasRightDual I := RightRigidCategory.rightDual I
  let W := (Xᘁ) ⊗ X
  let V := (Xᘁ) ⊗ ((Xᘁ)ᘁ)
  let : HasRightDual W := RightRigidCategory.rightDual W
  let r : Iᘁ ≅ I := rightDualUnitIso
  let t : Wᘁ ≅ V := rightDualTensorIso (Xᘁ) X
  let q : ExactPairing W V := ExactPairing.tensor
  have hu := coevaluation_rightDualIso_inv
    (@HasRightDual.exact C _ _ I (RightRigidCategory.rightDual I))
    (exactPairingUnit (C := C))
  change (ρ_ I).inv ≫ I ◁ r.inv = η_ I (Iᘁ) at hu
  have ht := coevaluation_rightDualIso
    (@HasRightDual.exact C _ _ W (RightRigidCategory.rightDual W)) q
  change η_ W (Wᘁ) ≫ W ◁ t.hom = @ExactPairing.coevaluation C _ _ W V q at ht
  have hm := coevaluation_comp_rightAdjointMate (ε_ X (Xᘁ))
  change η_ I (Iᘁ) ≫ I ◁ ((ε_ X (Xᘁ))ᘁ) =
    η_ W (Wᘁ) ≫ (ε_ X (Xᘁ)) ▷ (Wᘁ) at hm
  have hm' := congrArg (fun f => f ≫ I ◁ t.hom ≫ (λ_ V).hom) hm
  have hc : @ExactPairing.coevaluation C _ _ W V q ≫ (ε_ X (Xᘁ) ▷ V) ≫ (λ_ V).hom =
      η_ (Xᘁ) ((Xᘁ)ᘁ) := tensorPairing_coevaluation_evaluation X
  calc
    _ = ((ρ_ I).inv ≫ I ◁ r.inv ≫ I ◁ ((ε_ X (Xᘁ))ᘁ) ≫ I ◁ t.hom) ≫ (λ_ V).hom := by monoidal
    _ = (η_ W (Wᘁ) ≫ (ε_ X (Xᘁ)) ▷ (Wᘁ)) ≫ I ◁ t.hom ≫ (λ_ V).hom := by
      simpa only [← Category.assoc, hu] using hm'
    _ = @ExactPairing.coevaluation C _ _ W V q ≫ (ε_ X (Xᘁ) ▷ V) ≫ (λ_ V).hom := by
      rw [← ht]
      simp only [Category.assoc]
      rw [← whisker_exchange_assoc]
    _ = _ := hc
end PropertyF.Ground.Dimensions
