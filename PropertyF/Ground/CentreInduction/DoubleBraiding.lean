module
public import PropertyF.Ground.CentreInduction.DualBraiding

/-! The double dual functor preserves braiding. -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.BraidedCategory
namespace PropertyF.Ground.CentreInduction
universe v u
set_option backward.isDefEq.respectTransparency false
variable {D : Type u} [Category.{v} D] [MonoidalCategory D] [BraidedCategory D] [RightRigidCategory D]

/-- The double dual tensorator intertwines braiding. -/
theorem doubleDualTensorIso_braiding (X Y : D) :
    (Dimensions.doubleDualTensorIso X Y).hom ≫ (((β_ X Y).homᘁ)ᘁ) =
      (β_ ((Xᘁ)ᘁ) ((Yᘁ)ᘁ)).hom ≫ (Dimensions.doubleDualTensorIso Y X).hom := by
  have h1 := congrArg (fun f => rightAdjointMate f) (rightDualTensorIso_braiding X Y)
  simp only [comp_rightAdjointMate] at h1
  have h2 := rightDualTensorIso_braiding (Xᘁ) (Yᘁ)
  have h2' : (rightDualTensorIso (Yᘁ) (Xᘁ)).inv ≫ ((β_ (Xᘁ) (Yᘁ)).homᘁ) =
      (β_ ((Xᘁ)ᘁ) ((Yᘁ)ᘁ)).hom ≫ (rightDualTensorIso (Xᘁ) (Yᘁ)).inv := by
    apply (cancel_mono (rightDualTensorIso (Xᘁ) (Yᘁ)).hom).1
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [h2]
    simp [Category.assoc]
  simp only [Dimensions.doubleDualTensorIso, Iso.trans_hom, Iso.symm_hom,
    Dimensions.rightDualIsoMap, Category.assoc]
  rw [h1]
  simp only [← Category.assoc]
  rw [h2']
end PropertyF.Ground.CentreInduction
