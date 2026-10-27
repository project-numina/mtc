module
public import PropertyF.Ground.Dimensions.DualEvaluation

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.Dimensions
universe v u
set_option backward.isDefEq.respectTransparency false in
/-- Closing the middle pair in a tensor-product evaluation leaves the outer evaluation. -/
theorem tensorPairing_evaluation_coevaluation {C : Type u} [Category.{v} C]
    [MonoidalCategory C] [RightRigidCategory C] (X : C) :
    let W := X ⊗ (Xᘁ)
    let V := ((Xᘁ)ᘁ) ⊗ (Xᘁ)
    letI : ExactPairing W V := ExactPairing.tensor
    (ρ_ V).inv ≫ V ◁ η_ X (Xᘁ) ≫ ε_ W V = ε_ (Xᘁ) ((Xᘁ)ᘁ) := by
  let W := X ⊗ (Xᘁ)
  let V := ((Xᘁ)ᘁ) ⊗ (Xᘁ)
  let q : ExactPairing W V := ExactPairing.tensor
  let : ExactPairing W V := q
  change (ρ_ V).inv ≫ V ◁ η_ X (Xᘁ) ≫ @ExactPairing.evaluation C _ _ W V q = _
  have hq : @ExactPairing.evaluation C _ _ W V q =
      (𝟙 (V ⊗ W) ⊗≫ ((Xᘁ)ᘁ) ◁ (ε_ X (Xᘁ) ▷ (Xᘁ)) ⊗≫ ε_ (Xᘁ) ((Xᘁ)ᘁ)) := by
    change (@ExactPairing.tensor C _ _ X (Xᘁ) (Xᘁ) ((Xᘁ)ᘁ)
      HasRightDual.exact HasRightDual.exact).evaluation' = _
    unfold ExactPairing.tensor
    dsimp
  rw [hq]
  calc
    _ = 𝟙 V ⊗≫ (((Xᘁ)ᘁ) ◁ ((Xᘁ) ◁ η_ X (Xᘁ) ≫ (α_ (Xᘁ) X (Xᘁ)).inv ≫ ε_ X (Xᘁ) ▷ (Xᘁ))) ⊗≫ ε_ (Xᘁ) ((Xᘁ)ᘁ) := by
      simp only [whiskerLeft_comp]
      monoidal
    _ = _ := by
      rw [ExactPairing.coevaluation_evaluation]
      monoidal
set_option backward.isDefEq.respectTransparency false in
/-- Dualizing coevaluation gives the evaluation of the right dual. -/
theorem rightDualCoevaluation_evaluation {C : Type u} [Category.{v} C]
    [MonoidalCategory C] [RightRigidCategory C] (X : C) :
    letI : HasRightDual (𝟙_ C) := RightRigidCategory.rightDual (𝟙_ C)
    (rightDualTensorIso X (Xᘁ)).inv ≫ ((η_ X (Xᘁ))ᘁ) ≫
      (rightDualUnitIso (C := C)).hom = ε_ (Xᘁ) ((Xᘁ)ᘁ) := by
  let I := 𝟙_ C
  let : HasRightDual I := RightRigidCategory.rightDual I
  let W := X ⊗ (Xᘁ)
  let V := ((Xᘁ)ᘁ) ⊗ (Xᘁ)
  let : HasRightDual W := RightRigidCategory.rightDual W
  let r : Iᘁ ≅ I := rightDualUnitIso
  let t : Wᘁ ≅ V := rightDualTensorIso X (Xᘁ)
  let q : ExactPairing W V := ExactPairing.tensor
  have hu := rightDualIso_evaluation
    (@HasRightDual.exact C _ _ I (RightRigidCategory.rightDual I))
    (exactPairingUnit (C := C))
  change r.hom ▷ I ≫ (ρ_ I).hom = ε_ I (Iᘁ) at hu
  have ht := rightDualIso_inv_evaluation
    (@HasRightDual.exact C _ _ W (RightRigidCategory.rightDual W)) q
  change t.inv ▷ W ≫ ε_ W (Wᘁ) = @ExactPairing.evaluation C _ _ W V q at ht
  have hm := rightAdjointMate_comp_evaluation (η_ X (Xᘁ))
  change ((η_ X (Xᘁ))ᘁ) ▷ I ≫ ε_ I (Iᘁ) = Wᘁ ◁ η_ X (Xᘁ) ≫ ε_ W (Wᘁ) at hm
  have hm' := congrArg (fun f => (ρ_ V).inv ≫ t.inv ▷ I ≫ f) hm
  have hc : (ρ_ V).inv ≫ V ◁ η_ X (Xᘁ) ≫ @ExactPairing.evaluation C _ _ W V q =
      ε_ (Xᘁ) ((Xᘁ)ᘁ) := tensorPairing_evaluation_coevaluation X
  change t.inv ≫ ((η_ X (Xᘁ))ᘁ) ≫ r.hom = _
  calc
    _ = (ρ_ V).inv ≫ t.inv ▷ I ≫ (((η_ X (Xᘁ))ᘁ) ▷ I ≫ ε_ I (Iᘁ)) := by
      rw [← hu]
      simp only [← Category.assoc, ← comp_whiskerRight]
      monoidal
    _ = (ρ_ V).inv ≫ t.inv ▷ I ≫ (Wᘁ ◁ η_ X (Xᘁ) ≫ ε_ W (Wᘁ)) := hm'
    _ = (ρ_ V).inv ≫ V ◁ η_ X (Xᘁ) ≫ @ExactPairing.evaluation C _ _ W V q := by
      rw [← ht]
      rw [whisker_exchange_assoc]
    _ = _ := hc
set_option backward.isDefEq.respectTransparency false in
/-- The canonical strong monoidal double-dual functor preserves evaluation. -/
theorem doubleDual_evaluation {C : Type u} [Category.{v} C]
    [MonoidalCategory C] [RightRigidCategory C] (X : C) :
    letI : HasRightDual (𝟙_ C) := RightRigidCategory.rightDual (𝟙_ C)
    (doubleDualTensorIso (Xᘁ) X).hom ≫ (((ε_ X (Xᘁ))ᘁ)ᘁ) ≫
      (doubleDualUnitIso (C := C)).inv = ε_ ((Xᘁ)ᘁ) (((Xᘁ)ᘁ)ᘁ) := by
  let I := 𝟙_ C
  let : HasRightDual I := RightRigidCategory.rightDual I
  let W := (Xᘁ) ⊗ X
  let V := (Xᘁ) ⊗ ((Xᘁ)ᘁ)
  let : HasRightDual W := RightRigidCategory.rightDual W
  let : HasRightDual V := RightRigidCategory.rightDual V
  let r : Iᘁ ≅ I := rightDualUnitIso
  let t : Wᘁ ≅ V := rightDualTensorIso (Xᘁ) X
  let s : Vᘁ ≅ (((Xᘁ)ᘁ)ᘁ) ⊗ ((Xᘁ)ᘁ) := rightDualTensorIso (Xᘁ) ((Xᘁ)ᘁ)
  have he := rightDualEvaluation_coevaluation X
  change r.inv ≫ ((ε_ X (Xᘁ))ᘁ) ≫ t.hom = η_ (Xᘁ) ((Xᘁ)ᘁ) at he
  have hd := congrArg (fun f : I ⟶ V => fᘁ) he
  simp only [comp_rightAdjointMate] at hd
  have hc := rightDualCoevaluation_evaluation (Xᘁ)
  change s.inv ≫ ((η_ (Xᘁ) ((Xᘁ)ᘁ))ᘁ) ≫ r.hom = _ at hc
  change (s.inv ≫ t.homᘁ) ≫ (((ε_ X (Xᘁ))ᘁ)ᘁ) ≫ (r.invᘁ ≫ r.hom) = _
  have hx := congrArg (fun f => s.inv ≫ f ≫ r.hom) hd
  simpa only [Category.assoc] using hx.trans hc
set_option backward.isDefEq.respectTransparency false in
/-- The canonical strong monoidal double-dual functor preserves coevaluation. -/
theorem doubleDual_coevaluation {C : Type u} [Category.{v} C]
    [MonoidalCategory C] [RightRigidCategory C] (X : C) :
    letI : HasRightDual (𝟙_ C) := RightRigidCategory.rightDual (𝟙_ C)
    (doubleDualUnitIso (C := C)).hom ≫ (((η_ X (Xᘁ))ᘁ)ᘁ) ≫
      (doubleDualTensorIso X (Xᘁ)).inv = η_ ((Xᘁ)ᘁ) (((Xᘁ)ᘁ)ᘁ) := by
  let I := 𝟙_ C
  let : HasRightDual I := RightRigidCategory.rightDual I
  let W := X ⊗ (Xᘁ)
  let V := ((Xᘁ)ᘁ) ⊗ (Xᘁ)
  let : HasRightDual W := RightRigidCategory.rightDual W
  let : HasRightDual V := RightRigidCategory.rightDual V
  let r : Iᘁ ≅ I := rightDualUnitIso
  let t : Wᘁ ≅ V := rightDualTensorIso X (Xᘁ)
  let s : Vᘁ ≅ ((Xᘁ)ᘁ) ⊗ (((Xᘁ)ᘁ)ᘁ) := rightDualTensorIso ((Xᘁ)ᘁ) (Xᘁ)
  have he := rightDualCoevaluation_evaluation X
  change t.inv ≫ ((η_ X (Xᘁ))ᘁ) ≫ r.hom = ε_ (Xᘁ) ((Xᘁ)ᘁ) at he
  have hd := congrArg (fun f : V ⟶ I => fᘁ) he
  simp only [comp_rightAdjointMate] at hd
  have hc := rightDualEvaluation_coevaluation (Xᘁ)
  change r.inv ≫ ((ε_ (Xᘁ) ((Xᘁ)ᘁ))ᘁ) ≫ s.hom = _ at hc
  change (r.inv ≫ r.homᘁ) ≫ (((η_ X (Xᘁ))ᘁ)ᘁ) ≫ (t.invᘁ ≫ s.hom) = _
  have hx := congrArg (fun f => r.inv ≫ f ≫ s.hom) hd
  simpa only [Category.assoc] using hx.trans hc
end PropertyF.Ground.Dimensions
