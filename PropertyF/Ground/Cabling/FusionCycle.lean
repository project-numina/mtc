module
public import PropertyF.Ground.Fusion.GeneratedRigidity
public import PropertyF.Ground.Fusion.BalancedFlow
public import PropertyF.Ground.Fusion.Agreement
public import PropertyF.Ground.Cabling.UnitPower
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open scoped BigOperators
@[expose] public noncomputable section
namespace PropertyF.Ground.Cabling
universe v u

/-- A positive fusion coefficient gives an actual split inclusion. -/
theorem fusionCoeffRetract (D : Ground.BraidedFusionCategory.{v,u})
    (i a b : Fin (rank D)) (h : 0 < fusionCoeff D i a b) :
    Nonempty (Retract (simples D b) (simples D i ⊗ simples D a)) :=
  Ground.fusionCoeff_retract D i a b h

end PropertyF.Ground.Cabling
