module
public import PropertyF.Ground.Dimensions.DualBraiding
public import PropertyF.Ground.Dimensions.DoubleDualMonoidal

/-! # Braiding of double duals

The double-dual tensor comparison preserves the braiding.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.BraidedCategory
namespace PropertyF.Ground.Dimensions
universe v u
set_option backward.isDefEq.respectTransparency false in
/-- The canonical double-dual tensor comparison preserves the braiding. -/
theorem doubleDualTensorIso_braiding {C : Type u} [Category.{v} C] [MonoidalCategory C]
    [BraidedCategory C] [RightRigidCategory C] (X Y : C) :
    (doubleDualTensorIso X Y).hom ≫ (((β_ X Y).homᘁ)ᘁ) =
      (β_ ((Xᘁ)ᘁ) ((Yᘁ)ᘁ)).hom ≫ (doubleDualTensorIso Y X).hom := by
  let U := Xᘁ
  let V := Yᘁ
  let W := X ⊗ Y
  let W' := Y ⊗ X
  let : HasRightDual W := RightRigidCategory.rightDual W
  let : HasRightDual W' := RightRigidCategory.rightDual W'
  let : HasRightDual (U ⊗ V) := RightRigidCategory.rightDual (U ⊗ V)
  let : HasRightDual (V ⊗ U) := RightRigidCategory.rightDual (V ⊗ U)
  let t := rightDualTensorIso X Y
  let s := rightDualTensorIso Y X
  let a := rightDualTensorIso U V
  let b := rightDualTensorIso V U
  have h := rightDualTensorIso_braiding X Y
  change ((β_ X Y).homᘁ) ≫ t.hom = s.hom ≫ (β_ U V).hom at h
  have hd := congrArg (fun f : W'ᘁ ⟶ V ⊗ U => fᘁ) h
  simp only [comp_rightAdjointMate] at hd
  have hb := rightDualTensorIso_braiding U V
  change ((β_ U V).homᘁ) ≫ a.hom = b.hom ≫ (β_ (Uᘁ) (Vᘁ)).hom at hb
  have hm : b.inv ≫ ((β_ U V).homᘁ) = (β_ (Uᘁ) (Vᘁ)).hom ≫ a.inv :=
    (iso_inv_naturality_of_hom b a hb).symm
  change (b.inv ≫ t.homᘁ) ≫ (((β_ X Y).homᘁ)ᘁ) =
    (β_ (Uᘁ) (Vᘁ)).hom ≫ (a.inv ≫ s.homᘁ)
  simp only [Category.assoc, hd]
  rw [← Category.assoc, hm, Category.assoc]
end PropertyF.Ground.Dimensions
