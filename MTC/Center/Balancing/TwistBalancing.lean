module
public import MTC.Center.Dimensions.PivotalTwist
public import MTC.CategoryTheory.Dimensions.SimpleHomBasis
public import MTC.CategoryTheory.Dimensions.DimensionCharacter
public import MTC.PropertyF.Reduction.CharacterReality
public import MTC.Modular.SMatrix
public import MTC.Fusion.Reciprocity
public import MTC.Center.Braid.ImageCore
public import MTC.Fusion.UnitPower
public import MTC.CategoryTheory.Dimensions.DoubleDualPairing
public import MTC.CategoryTheory.Dimensions.DualBraiding

open MTC.Fusion

open MTC.Braided

/-!
# Drinfeld tensor compatibility

Evaluation against duals reduces the Drinfeld tensor equation to a cap identity.
The resulting compatibility supplies the balancing equation for the pivotal twist.
-/
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.BraidedCategory
open MTC MTC.CategoryTheory.Dimensions
universe v u
@[expose] public noncomputable section
namespace MTC.Center.Balancing
set_option backward.isDefEq.respectTransparency false

/-- Evaluating a double-dual tensor map reduces to the tensor pairing on
the dual factors. -/
theorem doubleDualTensor_evaluation {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
    {X Y : C} : (doubleDualTensorIso X Y).hom ▷ ((X ⊗ Y)ᘁ) ≫ ε_ ((X ⊗ Y)ᘁ) (((X ⊗ Y)ᘁ)ᘁ) =
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
  change (s.inv ≫ (t.homᘁ)) ▷ Wᘁ ≫ ε_ (Wᘁ) (((Wᘁ)ᘁ)) =
    (((Xᘁ)ᘁ ⊗ (Yᘁ)ᘁ) ◁ t.hom) ≫ @ExactPairing.evaluation C _ _ V _ q
  simp only [comp_whiskerRight, Category.assoc, ht]
  rw [← whisker_exchange_assoc, hs]

variable {D : Type u} [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]
  [RightRigidCategory D]

/-- The Drinfeld comparison satisfies the tensor equation at two objects. -/
abbrev HasDrinfeldTensorEquation (d : ∀ Z : D, Z ≅ (Zᘁ)ᘁ) (X Y : D) : Prop :=
  Modular.doubleBraiding X Y ≫ (d (X ⊗ Y)).hom =
    ((d X).hom ⊗ₘ (d Y).hom) ≫ (doubleDualTensorIso X Y).hom

/-- The automorphism obtained by comparing a pivotal map with a double-dual map. -/
abbrev relativeTwist (p : PivotalStructure (C := D))
    (d : ∀ Z : D, Z ≅ (Zᘁ)ᘁ) (X : D) : X ≅ X := p.iso X ≪≫ (d X).symm

section Twist
variable (p : PivotalStructure (C := D)) (d : ∀ Z : D, Z ≅ (Zᘁ)ᘁ)

/-- A compatible double-dual tensor equation implies pivotal twist balancing. -/
theorem balance_of_drinfeld_tensor {X Y : D} (h : HasDrinfeldTensorEquation d X Y) :
    (relativeTwist p d (X ⊗ Y)).hom =
      (relativeTwist p d X ⊗ᵢ relativeTwist p d Y).hom ≫ Modular.doubleBraiding X Y := by
  apply (cancel_mono (d (X ⊗ Y)).hom).1
  simp [relativeTwist, Category.assoc, h, p.tensor]

/-- In the usual convention, twist balancing has monodromy first. -/
theorem pivotal_balance_of_drinfeld_tensor {X Y : D} (h : HasDrinfeldTensorEquation d X Y) :
    Modular.doubleBraiding X Y ≫ (relativeTwist p d X ⊗ᵢ relativeTwist p d Y).hom =
      (relativeTwist p d (X ⊗ Y)).hom :=
  (Modular.doubleBraiding_natural _ _).trans (balance_of_drinfeld_tensor p d h).symm


end Twist

/-- The tensor-pairing cap identity for a double-dual comparison. -/
abbrev HasDrinfeldTensorCap (d : ∀ Z : D, Z ≅ (Zᘁ)ᘁ) (X Y : D) : Prop :=
  let W := X ⊗ Y
  let V := (Yᘁ) ⊗ (Xᘁ)
  let p : ExactPairing W V := ExactPairing.tensor
  let q : ExactPairing V (((Xᘁ)ᘁ) ⊗ ((Yᘁ)ᘁ)) := ExactPairing.tensor
  (Modular.doubleBraiding X Y ▷ V) ≫ (β_ W V).hom ≫
    @ExactPairing.evaluation D _ _ W V p =
  ((d X).hom ⊗ₘ (d Y).hom) ▷ V ≫ @ExactPairing.evaluation D _ _ V _ q

/-- The tensor-pairing cap identity implies the Drinfeld tensor equation. -/
theorem drinfeld_tensor_of_pairing_cap {X Y : D} (d : ∀ Z : D, Z ≅ (Zᘁ)ᘁ)
    (hd : HasDrinfeldEvaluation (d (X ⊗ Y)))
    (hcap : HasDrinfeldTensorCap d X Y) :
    HasDrinfeldTensorEquation d X Y := by
  let W := X ⊗ Y
  let V := (Yᘁ) ⊗ (Xᘁ)
  let t : Wᘁ ≅ V := rightDualTensorIso X Y
  let p : ExactPairing W V := ExactPairing.tensor
  let q : ExactPairing V (((Xᘁ)ᘁ) ⊗ ((Yᘁ)ᘁ)) := ExactPairing.tensor
  have he := rightDualIso_evaluation
    (@HasRightDual.exact D _ _ W (RightRigidCategory.rightDual W)) p
  change t.hom ▷ W ≫ @ExactPairing.evaluation D _ _ W V p = ε_ W (Wᘁ) at he
  have hs := doubleDualTensor_evaluation (C := D) (X := X) (Y := Y)
  change (doubleDualTensorIso X Y).hom ▷ Wᘁ ≫ ε_ (Wᘁ) ((Wᘁ)ᘁ) =
    (((Xᘁ)ᘁ ⊗ (Yᘁ)ᘁ) ◁ t.hom) ≫ @ExactPairing.evaluation D _ _ V _ q at hs
  apply evaluation_ext (X := Wᘁ)
  dsimp only [HasDrinfeldEvaluation] at hd
  rw [comp_whiskerRight_assoc, hd, ← he, comp_whiskerRight_assoc, hs]
  rw [← braiding_naturality_right_assoc]
  rw [← whisker_exchange_assoc, ← whisker_exchange_assoc]
  dsimp only [HasDrinfeldTensorCap] at hcap
  rw [hcap]


end MTC.Center.Balancing
