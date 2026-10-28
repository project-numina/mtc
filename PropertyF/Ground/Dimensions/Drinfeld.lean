module
public import PropertyF.Ground.Target
public import PropertyF.Ground.Dimensions.DualTensorNaturality

/-! # The Drinfeld isomorphism

The braided double-dual isomorphism is natural and induces the fourth-dual isomorphism.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.BraidedCategory
open PropertyF.Ground
namespace PropertyF.Ground.Dimensions
universe v u

variable (C : BraidedFusionCategory.{v,u})
/-- The braided double-dual isomorphism is characterized by its evaluation map. -/
theorem drinfeld_eval (C : BraidedFusionCategory.{v,u}) (X : C.Obj) :
    (doubleDualIso C X).hom ▷ (Xᘁ) ≫ ε_ (Xᘁ) ((Xᘁ)ᘁ) =
      (β_ X (Xᘁ)).hom ≫ ε_ X (Xᘁ) :=
  rightDualIso_evaluation (BraidedCategory.exactPairing_swap X (Xᘁ))
    (@HasRightDual.exact C.Obj _ _ (Xᘁ) (RightRigidCategory.rightDual (Xᘁ)))
/-- The braided double-dual isomorphism is natural. -/
@[reassoc]
theorem doubleDualIso_natural (C : BraidedFusionCategory.{v,u}) {X Y : C.Obj} (f : X ⟶ Y) :
    f ≫ (doubleDualIso C Y).hom = (doubleDualIso C X).hom ≫ (fᘁ)ᘁ := by
  have h : (f ≫ (doubleDualIso C Y).hom) ▷ (Yᘁ) ≫ ε_ (Yᘁ) ((Yᘁ)ᘁ) =
      ((doubleDualIso C X).hom ≫ (fᘁ)ᘁ) ▷ (Yᘁ) ≫ ε_ (Yᘁ) ((Yᘁ)ᘁ) := by
    calc
      _ = f ▷ (Yᘁ) ≫ (β_ Y (Yᘁ)).hom ≫ ε_ Y (Yᘁ) := by
        rw [comp_whiskerRight_assoc, drinfeld_eval]
      _ = (β_ X (Yᘁ)).hom ≫ (Yᘁ) ◁ f ≫ ε_ Y (Yᘁ) := by
        rw [braiding_naturality_left_assoc]
      _ = (β_ X (Yᘁ)).hom ≫ (fᘁ) ▷ X ≫ ε_ X (Xᘁ) := by
        rw [rightAdjointMate_comp_evaluation]
      _ = X ◁ (fᘁ) ≫ (β_ X (Xᘁ)).hom ≫ ε_ X (Xᘁ) := by
        rw [braiding_naturality_right_assoc]
      _ = X ◁ (fᘁ) ≫ (doubleDualIso C X).hom ▷ (Xᘁ) ≫ ε_ (Xᘁ) ((Xᘁ)ᘁ) := by
        rw [drinfeld_eval]
      _ = (doubleDualIso C X).hom ▷ (Yᘁ) ≫ ((Xᘁ)ᘁ) ◁ (fᘁ) ≫ ε_ (Xᘁ) ((Xᘁ)ᘁ) := by
        rw [whisker_exchange_assoc]
      _ = ((doubleDualIso C X).hom ≫ (fᘁ)ᘁ) ▷ (Yᘁ) ≫ ε_ (Yᘁ) ((Yᘁ)ᘁ) := by
        rw [← rightAdjointMate_comp_evaluation, comp_whiskerRight_assoc]
  exact evaluation_ext h

/-- The braided fourth-dual isomorphism, objectwise. -/
def fourthDualIso (C : BraidedFusionCategory.{v,u}) (X : C.Obj) :
    X ≅ ((((Xᘁ)ᘁ)ᘁ)ᘁ) :=
  doubleDualIso C X ≪≫ (rightDualIsoMap (doubleDualIso C (Xᘁ))).symm

/-- The braided fourth-dual isomorphism is natural. Monoidality is a separate obligation. -/
theorem fourthDualIso_natural (C : BraidedFusionCategory.{v,u}) {X Y : C.Obj} (f : X ⟶ Y) :
    f ≫ (fourthDualIso C Y).hom = (fourthDualIso C X).hom ≫ ((((fᘁ)ᘁ)ᘁ)ᘁ) := by
  have hinv : (doubleDualIso C (Yᘁ)).inv ≫ (fᘁ) =
      (((fᘁ)ᘁ)ᘁ) ≫ (doubleDualIso C (Xᘁ)).inv :=
    (iso_inv_naturality_of_hom (doubleDualIso C (Yᘁ)) (doubleDualIso C (Xᘁ))
      (doubleDualIso_natural C (fᘁ))).symm
  have hd := congrArg (fun (a : (((Yᘁ)ᘁ)ᘁ) ⟶ (Xᘁ)) => rightAdjointMate a) hinv
  simp only [comp_rightAdjointMate] at hd
  simp only [fourthDualIso, Iso.trans_hom, Iso.symm_hom, rightDualIsoMap, Category.assoc]
  rw [doubleDualIso_natural_assoc, hd]

set_option backward.isDefEq.respectTransparency false in
/-- The natural braided double-dual map commutes with applying double dual. -/
theorem doubleDualIso_doubleDual (X : C.Obj) :
    (doubleDualIso C ((Xᘁ)ᘁ)).hom = (((doubleDualIso C X).homᘁ)ᘁ) := by
  apply (cancel_epi (doubleDualIso C X).hom).1
  exact doubleDualIso_natural C (doubleDualIso C X).hom

set_option backward.isDefEq.respectTransparency false in
/-- The braided fourth-dual map intertwines duals with its inverse. -/
theorem fourthDualIso_rightDual (X : C.Obj) :
    fourthDualIso C (Xᘁ) = (rightDualIsoMap (fourthDualIso C X)).symm := by
  have hi : (doubleDualIso C ((Xᘁ)ᘁ)).inv = (((doubleDualIso C X).invᘁ)ᘁ) := by
    have hh : doubleDualIso C ((Xᘁ)ᘁ) = rightDualIsoMap (rightDualIsoMap (doubleDualIso C X)) := by
      apply Iso.ext
      exact doubleDualIso_doubleDual C X
    exact congrArg Iso.inv hh
  apply Iso.ext
  simp only [fourthDualIso, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, rightDualIsoMap,
    comp_rightAdjointMate]
  rw [hi]
  change (doubleDualIso C (Xᘁ)).hom ≫ (((((doubleDualIso C X).invᘁ)ᘁ)ᘁ)) =
    ((doubleDualIso C X).invᘁ) ≫ ((((doubleDualIso C (Xᘁ)).homᘁ)ᘁ))
  rw [← doubleDualIso_doubleDual C (Xᘁ)]
  exact (doubleDualIso_natural C ((doubleDualIso C X).invᘁ)).symm


end PropertyF.Ground.Dimensions
