module
public import PropertyF.Ground.CentreInduction.DualBraiding
public import PropertyF.Ground.Dimensions.DoubleDualBraiding

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
      (β_ ((Xᘁ)ᘁ) ((Yᘁ)ᘁ)).hom ≫ (Dimensions.doubleDualTensorIso Y X).hom :=
  Dimensions.doubleDualTensorIso_braiding X Y
end PropertyF.Ground.CentreInduction
