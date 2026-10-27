module
public import PropertyF.Ground.Target
public import PropertyF.Ground.Dimensions.DualCoherence

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.BraidedCategory
open PropertyF.Ground
namespace PropertyF.Ground.Dimensions
universe v u
/-- The braided double-dual isomorphism is characterized by its evaluation map. -/
theorem drinfeld_eval (C : BraidedFusionCategory.{v,u}) (X : C.Obj) :
    (doubleDualIso C X).hom ▷ (Xᘁ) ≫ ε_ (Xᘁ) ((Xᘁ)ᘁ) =
      (β_ X (Xᘁ)).hom ≫ ε_ X (Xᘁ) := by
  have he := rightDualIso_evaluation (BraidedCategory.exactPairing_swap X (Xᘁ))
    (@HasRightDual.exact C.Obj _ _ (Xᘁ) (RightRigidCategory.rightDual (Xᘁ)))
  exact he
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
  have he := congrArg (tensorRightHomEquiv X (Yᘁ) ((Yᘁ)ᘁ) (𝟙_ C.Obj)) h
  simp only [tensorRightHomEquiv_whiskerRight_comp_evaluation] at he
  exact (cancel_mono (λ_ ((Yᘁ)ᘁ)).inv).1 he

/-- The braided fourth-dual isomorphism, objectwise. -/
def fourthDualIso (C : BraidedFusionCategory.{v,u}) (X : C.Obj) :
    X ≅ ((((Xᘁ)ᘁ)ᘁ)ᘁ) :=
  doubleDualIso C X ≪≫ (rightDualIsoMap (doubleDualIso C (Xᘁ))).symm

/-- The braided fourth-dual isomorphism is natural. Monoidality is a separate obligation. -/
theorem fourthDualIso_natural (C : BraidedFusionCategory.{v,u}) {X Y : C.Obj} (f : X ⟶ Y) :
    f ≫ (fourthDualIso C Y).hom = (fourthDualIso C X).hom ≫ ((((fᘁ)ᘁ)ᘁ)ᘁ) := by
  have hinv : (doubleDualIso C (Yᘁ)).inv ≫ (fᘁ) =
      (((fᘁ)ᘁ)ᘁ) ≫ (doubleDualIso C (Xᘁ)).inv := by
    apply (cancel_mono (doubleDualIso C (Xᘁ)).hom).1
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [doubleDualIso_natural C (fᘁ)]
    simp [← Category.assoc]
  have hd := congrArg (fun (a : (((Yᘁ)ᘁ)ᘁ) ⟶ (Xᘁ)) => rightAdjointMate a) hinv
  simp only [comp_rightAdjointMate] at hd
  simp only [fourthDualIso, Iso.trans_hom, Iso.symm_hom, rightDualIsoMap, Category.assoc]
  rw [doubleDualIso_natural_assoc, hd]

end PropertyF.Ground.Dimensions
