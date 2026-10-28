module
public import PropertyF.Ground.CentreInduction.PositivePivotal
public import PropertyF.Ground.Dimensions.DualTensorNaturality
public import PropertyF.Ground.Dimensions.DualBraiding
public import PropertyF.Ground.Dimensions.DoubleDualBraiding

/-! The dual functors transport monodromy through their tensorators. -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.BraidedCategory
namespace PropertyF.Ground.CentreInduction
universe v u
set_option backward.isDefEq.respectTransparency false
variable {D : Type u} [Category.{v} D] [MonoidalCategory D] [BraidedCategory D] [RightRigidCategory D]

/-- Right duality reverses the tensor factors of mixed monodromy. -/
theorem rightDualTensorIso_monodromy (X Y : D) :
    (Modular.doubleBraiding X Y)ᘁ ≫ (rightDualTensorIso X Y).hom =
      (rightDualTensorIso X Y).hom ≫ Modular.doubleBraiding (Yᘁ) (Xᘁ) := by
  unfold Modular.doubleBraiding
  simp only [comp_rightAdjointMate, Category.assoc]
  rw [Dimensions.rightDualTensorIso_braiding X Y]
  rw [← Category.assoc ((β_ Y X).homᘁ), Dimensions.rightDualTensorIso_braiding Y X]
  simp [Category.assoc]

end PropertyF.Ground.CentreInduction
