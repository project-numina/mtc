module
public import PropertyF.Ground.Fusion.Agreement
public import PropertyF.Ground.CentreCabling.TwistFinite

/-! Nonzero scalar units associated with pivotal twists. -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.CentreCabling
universe v u

/-- The actual pivotal twist scalars, viewed as nonzero complex numbers. -/
def pivotalTwistUnit (C : Ground.BraidedFusionCategory.{v,u})
    (p : Dimensions.PivotalStructure (C := C.Obj)) (i : Fin (rank C)) : ℂˣ := by
  letI : Simple (simples C i) := simples_simple C i
  exact Units.mk0 (Dimensions.pivotalBraidedTwistScalar C p (simples C i))
    (Dimensions.pivotalBraidedTwistScalar_ne_zero C p (simples C i))


end PropertyF.Ground.CentreCabling
