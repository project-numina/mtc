module
public import MTC.CategoryTheory.Dimensions.DualCoherence
public import MTC.PropertyF.Statement

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
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
/-- A morphism into a dual object is determined by its evaluation pairing. -/
theorem evaluation_ext {X Y Z : C} [ExactPairing X Y] {f g : Z ⟶ Y}
    (h : f ▷ X ≫ ε_ X Y = g ▷ X ≫ ε_ X Y) : f = g := by
  let hDual : HasRightDual X := { rightDual := Y, exact := inferInstance }
  let : HasRightDual X := hDual
  exact (cancel_mono (λ_ Y).inv).1 <|
    (@tensorRightHomEquiv_whiskerRight_comp_evaluation C _ _ X Z hDual f).symm.trans <|
      (congrArg (tensorRightHomEquiv Z X Y (𝟙_ C)) h).trans
        (@tensorRightHomEquiv_whiskerRight_comp_evaluation C _ _ X Z hDual g)

section
variable {X Y A B A' B' : C} (pX : ExactPairing X A) (qX : ExactPairing X A')
  (pY : ExactPairing Y B) (qY : ExactPairing Y B')

set_option backward.isDefEq.respectTransparency false in
/-- The canonical comparison of duals preserves tensor products of pairings. -/
theorem rightDualIso_tensor :
    (rightDualIso (@ExactPairing.tensor C _ _ X Y A B pX pY)
      (@ExactPairing.tensor C _ _ X Y A' B' qX qY)).hom =
        (rightDualIso pY qY).hom ⊗ₘ (rightDualIso pX qX).hom :=
  let : ExactPairing X A := pX
  let : ExactPairing Y B := pY
  let : ExactPairing X A' := qX
  let : ExactPairing Y B' := qY
  evaluation_ext (X := X ⊗ Y) <| by
    rw [rightDualIso_evaluation]
    symm
    rw [tensorHom_def, comp_whiskerRight_assoc,
      tensorPairing_evaluation_whiskerLeft (p := pX) (q := qX) (r := qY)
        (rightDualIso pX qX).hom (rightDualIso_evaluation pX qX),
      tensorPairing_evaluation_whiskerRight (p := pX) (q := pY) (r := qY)
        (rightDualIso pY qY).hom (rightDualIso_evaluation pY qY)]
end

variable [RightRigidCategory C]
variable {X X' Y Y' : C} (f : X ⟶ X') (g : Y ⟶ Y')

omit [RightRigidCategory C] in
set_option backward.isDefEq.respectTransparency false in
/-- Evaluation of tensor pairings is natural in both factors. -/
theorem tensorPairing_evaluation_natural [HasRightDual X] [HasRightDual X']
    [HasRightDual Y] [HasRightDual Y'] : ((Y'ᘁ) ⊗ (X'ᘁ)) ◁ (f ⊗ₘ g) ≫ ε_ (X' ⊗ Y') ((Y'ᘁ) ⊗ (X'ᘁ)) =
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

omit [RightRigidCategory C] in
set_option backward.isDefEq.respectTransparency false in
theorem rightDualTensorIso_natural [HasRightDual X] [HasRightDual X']
    [HasRightDual Y] [HasRightDual Y'] [HasRightDual (X ⊗ Y)] [HasRightDual (X' ⊗ Y')] :
    ((f ⊗ₘ g)ᘁ) ≫ (rightDualTensorIso X Y).hom =
      (rightDualTensorIso X' Y').hom ≫ (gᘁ ⊗ₘ fᘁ) :=
  evaluation_ext (X := X ⊗ Y) (by
    rw [comp_whiskerRight_assoc, comp_whiskerRight_assoc,
      rightDualTensorIso_evaluation, rightAdjointMate_comp_evaluation,
      ← rightDualTensorIso_evaluation X' Y', whisker_exchange_assoc,
      tensorPairing_evaluation_natural])

omit [RightRigidCategory C] in
set_option backward.isDefEq.respectTransparency false in
/-- The inverse right-dual tensor comparison is natural. -/
theorem rightDualTensorIso_inv_natural [HasRightDual X] [HasRightDual X']
    [HasRightDual Y] [HasRightDual Y'] [HasRightDual (X ⊗ Y)] [HasRightDual (X' ⊗ Y')] :
    (gᘁ ⊗ₘ fᘁ) ≫ (rightDualTensorIso X Y).inv =
      (rightDualTensorIso X' Y').inv ≫ ((f ⊗ₘ g)ᘁ) :=
  (CommSq.vert_inv (CommSq.mk (rightDualTensorIso_natural f g))).w

set_option backward.isDefEq.respectTransparency false in
/-- The canonical double-dual tensor comparison is natural in both factors. -/
theorem doubleDualTensorIso_natural :
    (((fᘁ)ᘁ) ⊗ₘ ((gᘁ)ᘁ)) ≫ (doubleDualTensorIso X' Y').hom =
      (doubleDualTensorIso X Y).hom ≫ (((f ⊗ₘ g)ᘁ)ᘁ) := by
  have h2 := congrArg (fun m => rightAdjointMate m) (rightDualTensorIso_natural f g)
  rw [comp_rightAdjointMate, comp_rightAdjointMate] at h2
  simp only [doubleDualTensorIso, Iso.trans_hom, Iso.symm_hom, rightDualIsoMap, Category.assoc,
    reassoc_of% (rightDualTensorIso_inv_natural (gᘁ) (fᘁ)), ← h2]
end PropertyF.Ground.Dimensions

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.BraidedCategory
open PropertyF.Ground
namespace PropertyF.Ground.Dimensions
universe v u

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [RightRigidCategory C]

omit [RightRigidCategory C] in
/-- The braided isomorphism from an object to its double right dual. -/
def drinfeldIso (X : C) [HasRightDual X] [HasRightDual (Xᘁ)] : X ≅ (Xᘁ)ᘁ :=
  rightDualIso (BraidedCategory.exactPairing_swap X (Xᘁ)) HasRightDual.exact

omit [RightRigidCategory C] in
/-- The braided double-dual isomorphism is characterized by its evaluation map. -/
theorem drinfeld_eval (X : C) [HasRightDual X] [HasRightDual (Xᘁ)] :
    (drinfeldIso X).hom ▷ (Xᘁ) ≫ ε_ (Xᘁ) ((Xᘁ)ᘁ) =
      (β_ X (Xᘁ)).hom ≫ ε_ X (Xᘁ) :=
  rightDualIso_evaluation (BraidedCategory.exactPairing_swap X (Xᘁ))
    (@HasRightDual.exact C _ _ (Xᘁ) inferInstance)
omit [RightRigidCategory C] in
/-- The braided double-dual isomorphism is natural. -/
@[reassoc]
theorem drinfeldIso_natural {X Y : C} [HasRightDual X] [HasRightDual (Xᘁ)]
    [HasRightDual Y] [HasRightDual (Yᘁ)] (f : X ⟶ Y) :
    f ≫ (drinfeldIso Y).hom = (drinfeldIso X).hom ≫ (fᘁ)ᘁ :=
  evaluation_ext (X := Yᘁ) (by
    rw [comp_whiskerRight_assoc, comp_whiskerRight_assoc,
      drinfeld_eval Y, braiding_naturality_left_assoc,
      ← rightAdjointMate_comp_evaluation, ← braiding_naturality_right_assoc,
      ← drinfeld_eval X, whisker_exchange_assoc, ← rightAdjointMate_comp_evaluation])

omit [RightRigidCategory C] in
/-- The braided fourth-dual isomorphism, objectwise. -/
def fourthDualIso (X : C) [HasRightDual X] [HasRightDual (Xᘁ)]
    [HasRightDual ((Xᘁ)ᘁ)] [HasRightDual (((Xᘁ)ᘁ)ᘁ)] :
    X ≅ ((((Xᘁ)ᘁ)ᘁ)ᘁ) :=
  drinfeldIso X ≪≫ (rightDualIsoMap (drinfeldIso (Xᘁ))).symm

/-- The fourth-dual isomorphism is compatible with tensoring two objects. -/
abbrev fourthDualTensorLaw (X Y : C) : Prop :=
  (fourthDualIso (X ⊗ Y)).hom =
    ((fourthDualIso X).hom ⊗ₘ (fourthDualIso Y).hom) ≫
      (doubleDualTensorIso ((Xᘁ)ᘁ) ((Yᘁ)ᘁ)).hom ≫
        (((doubleDualTensorIso X Y).homᘁ)ᘁ)

/-- The braided fourth-dual isomorphism is natural. Monoidality is a separate obligation. -/
theorem fourthDualIso_natural {X Y : C} (f : X ⟶ Y) :
    f ≫ (fourthDualIso Y).hom = (fourthDualIso X).hom ≫ ((((fᘁ)ᘁ)ᘁ)ᘁ) := by
  have hd := congrArg (fun (a : (((Yᘁ)ᘁ)ᘁ) ⟶ (Xᘁ)) => rightAdjointMate a)
    ((CommSq.vert_inv (CommSq.mk (drinfeldIso_natural (fᘁ)))).w).symm
  rw [comp_rightAdjointMate, comp_rightAdjointMate] at hd
  simp only [fourthDualIso, Iso.trans_hom, Iso.symm_hom, rightDualIsoMap, Category.assoc,
    drinfeldIso_natural_assoc, hd]

omit [RightRigidCategory C] in
set_option backward.isDefEq.respectTransparency false in
/-- The natural braided double-dual map commutes with applying double dual. -/
theorem drinfeldIso_doubleDual (X : C) [HasRightDual X] [HasRightDual (Xᘁ)]
    [HasRightDual ((Xᘁ)ᘁ)] [HasRightDual (((Xᘁ)ᘁ)ᘁ)] :
    (drinfeldIso ((Xᘁ)ᘁ)).hom = (((drinfeldIso X).homᘁ)ᘁ) :=
  (cancel_epi (drinfeldIso X).hom).1 (drinfeldIso_natural (drinfeldIso X).hom)

omit [RightRigidCategory C] in
set_option backward.isDefEq.respectTransparency false in
/-- The braided fourth-dual map intertwines duals with its inverse. -/
theorem fourthDualIso_rightDual (X : C) [HasRightDual X] [HasRightDual (Xᘁ)]
    [HasRightDual ((Xᘁ)ᘁ)] [HasRightDual (((Xᘁ)ᘁ)ᘁ)]
    [HasRightDual ((((Xᘁ)ᘁ)ᘁ)ᘁ)] :
    fourthDualIso (Xᘁ) = (rightDualIsoMap (fourthDualIso X)).symm := Iso.ext <| by
  have hi : (drinfeldIso ((Xᘁ)ᘁ)).inv = (((drinfeldIso X).invᘁ)ᘁ) :=
    congrArg Iso.inv (Iso.ext (drinfeldIso_doubleDual X) :
      drinfeldIso ((Xᘁ)ᘁ) = rightDualIsoMap (rightDualIsoMap (drinfeldIso X)))
  simp only [fourthDualIso, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, rightDualIsoMap,
    comp_rightAdjointMate, hi]
  change (drinfeldIso (Xᘁ)).hom ≫ (((((drinfeldIso X).invᘁ)ᘁ)ᘁ)) =
    ((drinfeldIso X).invᘁ) ≫ ((((drinfeldIso (Xᘁ)).homᘁ)ᘁ))
  simpa only [drinfeldIso_doubleDual] using (drinfeldIso_natural ((drinfeldIso X).invᘁ)).symm


end PropertyF.Ground.Dimensions
