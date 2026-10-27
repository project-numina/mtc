module
public import PropertyF.Ground.CentreDimensions.RankOneCenter
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
/-- The actual rank-one centre has fusion and positive spherical structures,
and its categorical dimension is the FP square, with no extra assumptions. -/
theorem rankOne_center_spherical_and_globalDimension (C : Ground.BraidedFusionCategory.{v,u})
    [Subsingleton (Fin (Ground.rank C))] :
    letI : RigidCategory (CategoryTheory.Center C.Obj) := rankOne_centerRigid C
    letI : Ground.IsFusionCategory (CategoryTheory.Center C.Obj) := Ground.CentreInduction.fusion_of_rank_one C
    ∃ p : PivotalStructure (C := (Ground.Integrate.bundledCenter C).Obj), p.IsSpherical ∧
      (∀ i, pivotalDimension (Ground.Integrate.bundledCenter C) p
        (Ground.simples (Ground.Integrate.bundledCenter C) i) =
          (Ground.fpSimple (Ground.Integrate.bundledCenter C) i : ℂ)) ∧
      Ground.globalDimension (Ground.Integrate.bundledCenter C) = (Ground.globalFPDimension C : ℂ) ^ 2 := by
  let : RigidCategory (CategoryTheory.Center C.Obj) := rankOne_centerRigid C
  exact center_spherical_and_globalDimension_of_rank_one C
end PropertyF.Ground.Dimensions
