module
public import PropertyF.Ground.CentreDimensions.PivotalTwist
public import PropertyF.Ground.Dimensions.SimpleHomBasis
public import PropertyF.Ground.Dimensions.IntrinsicNonzero
public import PropertyF.Ground.Fusion.Reciprocity
public import PropertyF.Ground.CentreCabling.ImageCore
public import PropertyF.Ground.Fusion.GeneratedRigidity
public import PropertyF.Ground.Dimensions.PivotalDual
public import PropertyF.Ground.Dimensions.SphericalReal
public import PropertyF.Ground.Dimensions.DualBraiding
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.BraidedCategory
open PropertyF.Ground PropertyF.Ground.Dimensions
universe v u
@[expose] public noncomputable section
namespace PropertyF.Ground.CentreIntegrate
set_option backward.isDefEq.respectTransparency false

/-- Evaluating a double-dual tensor map reduces to the tensor pairing on
the dual factors. -/
theorem doubleDualTensor_evaluation {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
    (X Y : C) (u : X ⟶ (Xᘁ)ᘁ) (v : Y ⟶ (Yᘁ)ᘁ) :
    ((u ⊗ₘ v) ≫ (doubleDualTensorIso X Y).hom) ▷ ((X ⊗ Y)ᘁ) ≫
      ε_ ((X ⊗ Y)ᘁ) (((X ⊗ Y)ᘁ)ᘁ) =
      (u ⊗ₘ v) ▷ ((X ⊗ Y)ᘁ) ≫
        (((Xᘁ)ᘁ ⊗ (Yᘁ)ᘁ) ◁ (rightDualTensorIso X Y).hom) ≫
          ε_ ((Yᘁ) ⊗ (Xᘁ)) (((Xᘁ)ᘁ) ⊗ ((Yᘁ)ᘁ)) := by
  let W := X ⊗ Y
  let V := (Yᘁ) ⊗ (Xᘁ)
  let t : Wᘁ ≅ V := rightDualTensorIso X Y
  let s : Vᘁ ≅ ((Xᘁ)ᘁ) ⊗ ((Yᘁ)ᘁ) := rightDualTensorIso (Yᘁ) (Xᘁ)
  let q : ExactPairing V (((Xᘁ)ᘁ) ⊗ ((Yᘁ)ᘁ)) := ExactPairing.tensor
  have hs := rightDualIso_inv_evaluation
    (@HasRightDual.exact C _ _ V (RightRigidCategory.rightDual V)) q
  change s.inv ▷ V ≫ ε_ V (Vᘁ) = @ExactPairing.evaluation C _ _ V _ q at hs
  have ht := rightAdjointMate_comp_evaluation t.hom
  change (t.homᘁ) ▷ Wᘁ ≫ ε_ (Wᘁ) (((Wᘁ)ᘁ)) = Vᘁ ◁ t.hom ≫ ε_ V Vᘁ at ht
  change ((u ⊗ₘ v) ≫ (s.inv ≫ (t.homᘁ))) ▷ Wᘁ ≫ ε_ (Wᘁ) (((Wᘁ)ᘁ)) =
    (u ⊗ₘ v) ▷ Wᘁ ≫ (((Xᘁ)ᘁ ⊗ (Yᘁ)ᘁ) ◁ t.hom) ≫ @ExactPairing.evaluation C _ _ V _ q
  simp only [comp_whiskerRight, Category.assoc, ht]
  rw [← whisker_exchange_assoc, hs]

/-- The Drinfeld tensor equation implies pivotal twist balancing. -/
theorem balance_of_drinfeld_tensor
    (C : BraidedFusionCategory.{v,u}) (p : PivotalStructure (C := C.Obj)) (X Y : C.Obj)
    (h : Modular.doubleBraiding X Y ≫ (doubleDualIso C (X ⊗ Y)).hom =
      ((doubleDualIso C X).hom ⊗ₘ (doubleDualIso C Y).hom) ≫
        (doubleDualTensorIso X Y).hom) :
    (pivotalBraidedTwist C p (X ⊗ Y)).hom =
      ((pivotalBraidedTwist C p X).hom ⊗ₘ (pivotalBraidedTwist C p Y).hom) ≫
        Modular.doubleBraiding X Y := by
  apply (cancel_mono (doubleDualIso C (X ⊗ Y)).hom).1
  simp only [pivotalBraidedTwist, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]
  rw [h, p.tensor]
  rw [← Category.assoc, tensorHom_comp_tensorHom]
  simp [Category.assoc]

/-- The tensor-pairing cap identity implies the Drinfeld tensor equation. -/
theorem drinfeld_tensor_of_pairing_cap (C : BraidedFusionCategory.{v,u}) (X Y : C.Obj)
    (hcap : let W := X ⊗ Y
      let V := (Yᘁ) ⊗ (Xᘁ)
      let p : ExactPairing W V := ExactPairing.tensor
      let q : ExactPairing V (((Xᘁ)ᘁ) ⊗ ((Yᘁ)ᘁ)) := ExactPairing.tensor
      (Modular.doubleBraiding X Y ▷ V) ≫ (β_ W V).hom ≫
        @ExactPairing.evaluation C.Obj _ _ W V p =
      ((doubleDualIso C X).hom ⊗ₘ (doubleDualIso C Y).hom) ▷ V ≫
        @ExactPairing.evaluation C.Obj _ _ V _ q) :
    Modular.doubleBraiding X Y ≫ (doubleDualIso C (X ⊗ Y)).hom =
      ((doubleDualIso C X).hom ⊗ₘ (doubleDualIso C Y).hom) ≫
        (doubleDualTensorIso X Y).hom := by
  let W := X ⊗ Y
  let V := (Yᘁ) ⊗ (Xᘁ)
  let t : Wᘁ ≅ V := rightDualTensorIso X Y
  let p : ExactPairing W V := ExactPairing.tensor
  let q : ExactPairing V (((Xᘁ)ᘁ) ⊗ ((Yᘁ)ᘁ)) := ExactPairing.tensor
  have he := rightDualIso_evaluation
    (@HasRightDual.exact C.Obj _ _ W (RightRigidCategory.rightDual W)) p
  change t.hom ▷ W ≫ @ExactPairing.evaluation C.Obj _ _ W V p = ε_ W (Wᘁ) at he
  have hs := doubleDualTensor_evaluation X Y (doubleDualIso C X).hom (doubleDualIso C Y).hom
  change (((doubleDualIso C X).hom ⊗ₘ (doubleDualIso C Y).hom) ≫
    (doubleDualTensorIso X Y).hom) ▷ Wᘁ ≫ ε_ (Wᘁ) ((Wᘁ)ᘁ) =
    ((doubleDualIso C X).hom ⊗ₘ (doubleDualIso C Y).hom) ▷ Wᘁ ≫
      (((Xᘁ)ᘁ ⊗ (Yᘁ)ᘁ) ◁ t.hom) ≫ @ExactPairing.evaluation C.Obj _ _ V _ q at hs
  have htest : (Modular.doubleBraiding X Y ≫ (doubleDualIso C W).hom) ▷ Wᘁ ≫
      ε_ (Wᘁ) ((Wᘁ)ᘁ) =
      (((doubleDualIso C X).hom ⊗ₘ (doubleDualIso C Y).hom) ≫
        (doubleDualTensorIso X Y).hom) ▷ Wᘁ ≫ ε_ (Wᘁ) ((Wᘁ)ᘁ) := by
    rw [comp_whiskerRight_assoc, drinfeld_eval, ← he, hs]
    rw [← braiding_naturality_right_assoc]
    rw [← whisker_exchange_assoc, ← whisker_exchange_assoc]
    rw [hcap]
  have hh := congrArg (tensorRightHomEquiv W (Wᘁ) ((Wᘁ)ᘁ) (𝟙_ C.Obj)) htest
  simp only [tensorRightHomEquiv_whiskerRight_comp_evaluation] at hh
  exact (cancel_mono (λ_ ((Wᘁ)ᘁ)).inv).1 hh

/-- In the usual convention, twist balancing has monodromy first. -/
theorem pivotal_balance_of_drinfeld_tensor (C : BraidedFusionCategory.{v,u})
    (p : PivotalStructure (C := C.Obj)) (X Y : C.Obj)
    (h : Modular.doubleBraiding X Y ≫ (doubleDualIso C (X ⊗ Y)).hom =
      ((doubleDualIso C X).hom ⊗ₘ (doubleDualIso C Y).hom) ≫
        (doubleDualTensorIso X Y).hom) :
    Modular.doubleBraiding X Y ≫
      ((pivotalBraidedTwist C p X).hom ⊗ₘ (pivotalBraidedTwist C p Y).hom) =
        (pivotalBraidedTwist C p (X ⊗ Y)).hom := by
  rw [balance_of_drinfeld_tensor C p X Y h]
  exact CentreCabling.doubleBraiding_natural _ _

end PropertyF.Ground.CentreIntegrate
