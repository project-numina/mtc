module
public import PropertyF.Ground.Dimensions.DoubleDualAssociativity

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.Dimensions
universe v u
set_option backward.isDefEq.respectTransparency false in
/-- The canonical double-dual assignment is strongly monoidal. -/
def doubleDualCoreMonoidal (C : Type u) [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C] :
    (doubleDualFunctor C).CoreMonoidal where
  εIso := doubleDualUnitIso
  μIso := doubleDualTensorIso
  μIso_hom_natural_left := by
    intro X Y f X'
    have h := doubleDualTensorIso_natural f (𝟙 X')
    simpa only [doubleDualFunctor, rightAdjointMate_id, tensorHom_id] using h
  μIso_hom_natural_right := by
    intro X Y X' f
    have h := doubleDualTensorIso_natural (𝟙 X') f
    simpa only [doubleDualFunctor, rightAdjointMate_id, id_tensorHom] using h
  associativity := by
    intro X Y Z
    exact doubleDualTensorIso_associativity X Y Z
  left_unitality := by
    intro X
    exact (doubleDualTensorIso_unit_left X).symm
  right_unitality := by
    intro X
    exact (doubleDualTensorIso_unit_right X).symm

@[instance_reducible] def doubleDualMonoidal (C : Type u) [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C] :
    (doubleDualFunctor C).Monoidal := (doubleDualCoreMonoidal C).toMonoidal
end PropertyF.Ground.Dimensions
