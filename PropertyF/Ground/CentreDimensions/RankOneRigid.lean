module
public import PropertyF.Ground.Dimensions.RankOneCriterion
public import PropertyF.Ground.CentreInduction.RankOne
public import Mathlib.CategoryTheory.Monoidal.Rigid.OfEquivalence

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.Dimensions
universe v u
/-- The actual centre of a rank-one category is rigid by the monoidal forgetful equivalence. -/
@[instance_reducible] def rankOne_centerRigid (C : Ground.BraidedFusionCategory.{v,u})
    [Subsingleton (Fin (Ground.rank C))] : RigidCategory (CategoryTheory.Center C.Obj) := by
  let e := Ground.CentreInduction.centerForgetEquivalenceOfRankOne C
  let F := CategoryTheory.Center.forget C.Obj
  let : F.Full := Ground.CentreInduction.centerForgetFullOfRankOne C
  let : F.IsEquivalence := e.isEquivalence_functor
  let : e.functor.Monoidal := by
    change F.Monoidal
    infer_instance
  exact rigidCategoryOfEquivalence e.toAdjunction
end PropertyF.Ground.Dimensions
