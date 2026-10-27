module
public import PropertyF.Ground.CentreDimensions.RankOneRigid
public import PropertyF.Ground.CentreInduction.ForgetDual
open CategoryTheory CategoryTheory.MonoidalCategory
universe v u
@[expose] public noncomputable section
namespace PropertyF.Ground.CentreInduction
variable (C : BraidedFusionCategory.{v,u}) [Subsingleton (Fin (rank C))]

/-- In rank one, the unit of the actual centre induction adjunction is an isomorphism. -/
theorem rankOne_induction_unit_isIso (Z : CategoryTheory.Center C.Obj) :
    IsIso ((actualAdjunction C).unit.app Z) := by
  let F := CategoryTheory.Center.forget C.Obj
  letI : F.Full := centerForgetFullOfRankOne C
  infer_instance

/-- Rank-one centre objects are retracts of their actual induced underlying objects. -/
theorem rankOne_induction_retract (Z : CategoryTheory.Center C.Obj) :
    Nonempty (Retract Z ((induction C).obj Z.1)) := by
  let e := @asIso (CategoryTheory.Center C.Obj) _ _ _ ((actualAdjunction C).unit.app Z)
    (rankOne_induction_unit_isIso C Z)
  exact ⟨Retract.ofIso e⟩

end PropertyF.Ground.CentreInduction
