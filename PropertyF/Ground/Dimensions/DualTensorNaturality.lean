module
public import PropertyF.Ground.Dimensions.DualCoherence
public import PropertyF.Ground.Target

/-! # Dual tensor comparisons and the Drinfeld isomorphism

Evaluation pairings establish naturality of dual tensor isomorphisms and the Drinfeld isomorphism.

## Main results

* `evaluation_ext`: compares dual morphisms by composing with evaluation.
* `rightDualTensorIso_natural`: proves naturality of the right-dual tensor comparison.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.Dimensions
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
/-- A morphism into a dual object is determined by its evaluation pairing. -/
theorem evaluation_ext {C : Type u} [Category.{v} C] [MonoidalCategory C] {X Y Z : C} [ExactPairing X Y] {f g : Z ⟶ Y}
    (h : f ▷ X ≫ ε_ X Y = g ▷ X ≫ ε_ X Y) : f = g := by
  let hDual : HasRightDual X := { rightDual := Y, exact := inferInstance }
  let : HasRightDual X := hDual
  have h' := congrArg (tensorRightHomEquiv Z X Y (𝟙_ C)) h
  rw [show (tensorRightHomEquiv Z X Y (𝟙_ C)) (f ▷ X ≫ ε_ X Y) = f ≫ (λ_ Y).inv from
      @tensorRightHomEquiv_whiskerRight_comp_evaluation C _ _ X Z hDual f,
    show (tensorRightHomEquiv Z X Y (𝟙_ C)) (g ▷ X ≫ ε_ X Y) = g ≫ (λ_ Y).inv from
      @tensorRightHomEquiv_whiskerRight_comp_evaluation C _ _ X Z hDual g] at h'
  exact (cancel_mono (λ_ Y).inv).1 h'

set_option backward.isDefEq.respectTransparency false in
/-- Evaluation of tensor pairings is natural in both factors. -/
theorem tensorPairing_evaluation_natural {X X' Y Y' : C} (f : X ⟶ X') (g : Y ⟶ Y') : ((Y'ᘁ) ⊗ (X'ᘁ)) ◁ (f ⊗ₘ g) ≫ ε_ (X' ⊗ Y') ((Y'ᘁ) ⊗ (X'ᘁ)) =
        (gᘁ ⊗ₘ fᘁ) ▷ (X ⊗ Y) ≫ ε_ (X ⊗ Y) ((Yᘁ) ⊗ (Xᘁ)) := by
  change ((Y'ᘁ) ⊗ (X'ᘁ)) ◁ (f ⊗ₘ g) ≫
    (𝟙 _ ⊗≫ (Y'ᘁ) ◁ (ε_ X' (X'ᘁ) ▷ Y') ⊗≫ ε_ Y' (Y'ᘁ)) =
    (gᘁ ⊗ₘ fᘁ) ▷ (X ⊗ Y) ≫
    (𝟙 _ ⊗≫ (Yᘁ) ◁ (ε_ X (Xᘁ) ▷ Y) ⊗≫ ε_ Y (Yᘁ))
  calc
    _ = 𝟙 _ ⊗≫ (Y'ᘁ : C) ◁ (((X'ᘁ : C) ◁ f) ▷ Y ≫
      ((X'ᘁ ⊗ X') ◁ g) ≫ (ε_ X' (X'ᘁ) ▷ Y')) ⊗≫ ε_ Y' (Y'ᘁ) := by
        simp only [tensorHom_def, whiskerLeft_comp]
        monoidal
    _ = 𝟙 _ ⊗≫ (Y'ᘁ : C) ◁ (((X'ᘁ : C) ◁ f) ▷ Y ≫
      (ε_ X' (X'ᘁ) ▷ Y) ≫ ((𝟙_ C) ◁ g)) ⊗≫ ε_ Y' (Y'ᘁ) := by
        rw [← whisker_exchange]
    _ = 𝟙 _ ⊗≫ (Y'ᘁ : C) ◁ (((X'ᘁ : C) ◁ f ≫ ε_ X' (X'ᘁ)) ▷ Y) ⊗≫
      ((Y'ᘁ : C) ◁ g ≫ ε_ Y' (Y'ᘁ)) := by monoidal
    _ = 𝟙 _ ⊗≫ (Y'ᘁ : C) ◁ (((fᘁ) ▷ X ≫ ε_ X (Xᘁ)) ▷ Y) ⊗≫
      ((gᘁ) ▷ Y ≫ ε_ Y (Yᘁ)) := by
        rw [rightAdjointMate_comp_evaluation, rightAdjointMate_comp_evaluation]
    _ = 𝟙 _ ⊗≫ (Y'ᘁ : C) ◁ ((fᘁ ▷ X) ▷ Y) ⊗≫
      (((Y'ᘁ : C) ◁ (ε_ X (Xᘁ) ▷ Y)) ≫ (gᘁ ▷ ((𝟙_ C) ⊗ Y))) ⊗≫ ε_ Y (Yᘁ) := by
        simp only [whiskerLeft_comp, comp_whiskerRight]
        monoidal
    _ = 𝟙 _ ⊗≫ (Y'ᘁ : C) ◁ ((fᘁ ▷ X) ▷ Y) ⊗≫
      ((gᘁ ▷ (((Xᘁ) ⊗ X) ⊗ Y)) ≫ ((Yᘁ : C) ◁ (ε_ X (Xᘁ) ▷ Y))) ⊗≫ ε_ Y (Yᘁ) := by
        rw [whisker_exchange]
    _ = _ := by simp only [tensorHom_def', comp_whiskerRight]; monoidal

set_option backward.isDefEq.respectTransparency false in
theorem rightDualTensorIso_natural {X X' Y Y' : C} (f : X ⟶ X') (g : Y ⟶ Y') :
    ((f ⊗ₘ g)ᘁ) ≫ (rightDualTensorIso X Y).hom =
      (rightDualTensorIso X' Y').hom ≫ (gᘁ ⊗ₘ fᘁ) := by
  have h : (((f ⊗ₘ g)ᘁ) ≫ (rightDualTensorIso X Y).hom) ▷ (X ⊗ Y) ≫
        ε_ (X ⊗ Y) ((Yᘁ) ⊗ (Xᘁ)) =
      ((rightDualTensorIso X' Y').hom ≫ (gᘁ ⊗ₘ fᘁ)) ▷ (X ⊗ Y) ≫
        ε_ (X ⊗ Y) ((Yᘁ) ⊗ (Xᘁ)) := by
    have he := rightDualTensorIso_evaluation X Y
    simp only [comp_whiskerRight_assoc] at *
    simp only [← Category.assoc, he]
    simp only [Category.assoc, rightAdjointMate_comp_evaluation]
    have aux := tensorPairing_evaluation_natural f g
    have he' := rightDualTensorIso_evaluation X' Y'
    calc
      _ = (X' ⊗ Y')ᘁ ◁ (f ⊗ₘ g) ≫ (rightDualTensorIso X' Y').hom ▷ (X' ⊗ Y') ≫
          ε_ (X' ⊗ Y') ((Y'ᘁ) ⊗ (X'ᘁ)) := by rw [he']
      _ = (rightDualTensorIso X' Y').hom ▷ (X ⊗ Y) ≫
          ((Y'ᘁ) ⊗ (X'ᘁ)) ◁ (f ⊗ₘ g) ≫ ε_ (X' ⊗ Y') ((Y'ᘁ) ⊗ (X'ᘁ)) := by
            rw [whisker_exchange_assoc]
      _ = _ := by rw [aux]
  exact evaluation_ext h

set_option backward.isDefEq.respectTransparency false in
/-- The inverse right-dual tensor comparison is natural. -/
theorem rightDualTensorIso_inv_natural {C : Type u} [Category.{v} C]
    [MonoidalCategory C] [RightRigidCategory C] {X X' Y Y' : C}
    (f : X ⟶ X') (g : Y ⟶ Y') :
    (gᘁ ⊗ₘ fᘁ) ≫ (rightDualTensorIso X Y).inv =
      (rightDualTensorIso X' Y').inv ≫ ((f ⊗ₘ g)ᘁ) :=
  iso_inv_naturality_of_hom (rightDualTensorIso_natural f g)

set_option backward.isDefEq.respectTransparency false in
/-- The canonical double-dual tensor comparison is natural in both factors. -/
theorem doubleDualTensorIso_natural {X X' Y Y' : C} (f : X ⟶ X') (g : Y ⟶ Y') :
    (((fᘁ)ᘁ) ⊗ₘ ((gᘁ)ᘁ)) ≫ (doubleDualTensorIso X' Y').hom =
      (doubleDualTensorIso X Y).hom ≫ (((f ⊗ₘ g)ᘁ)ᘁ) := by
  have h1' := rightDualTensorIso_inv_natural (gᘁ) (fᘁ)
  have h2 := congrArg (fun m => rightAdjointMate m) (rightDualTensorIso_natural f g)
  simp only [comp_rightAdjointMate] at h2
  simp only [doubleDualTensorIso, Iso.trans_hom, Iso.symm_hom, rightDualIsoMap, Category.assoc]
  rw [← Category.assoc, h1', Category.assoc, ← h2]
end PropertyF.Ground.Dimensions

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
  have hd := congrArg (fun (a : (((Yᘁ)ᘁ)ᘁ) ⟶ (Xᘁ)) => rightAdjointMate a)
    (iso_inv_naturality_of_hom (doubleDualIso_natural C (fᘁ))).symm
  simp only [comp_rightAdjointMate] at hd
  simp only [fourthDualIso, Iso.trans_hom, Iso.symm_hom, rightDualIsoMap, Category.assoc]
  rw [doubleDualIso_natural_assoc, hd]

set_option backward.isDefEq.respectTransparency false in
/-- The natural braided double-dual map commutes with applying double dual. -/
theorem doubleDualIso_doubleDual (X : C.Obj) :
    (doubleDualIso C ((Xᘁ)ᘁ)).hom = (((doubleDualIso C X).homᘁ)ᘁ) :=
  (cancel_epi (doubleDualIso C X).hom).1 (doubleDualIso_natural C (doubleDualIso C X).hom)

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
