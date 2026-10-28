module
public import PropertyF.Ground.Fusion.GeneratedRigidity
public import PropertyF.Ground.Fusion.UnitPower
public import PropertyF.Ground.Fusion.Agreement
public import PropertyF.Ground.Cabling.UnitPower
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open scoped BigOperators
@[expose] public noncomputable section
namespace PropertyF.Ground.Cabling
universe v u

/-- Every simple fusion matrix has a directed cycle through the unit. -/
theorem fusion_unit_cycle (D : Ground.BraidedFusionCategory.{v,u})
    (i : Fin (rank D)) :
    ∃ j, 0 < fusionCoeff D i (unitIndex D) j ∧
      Relation.ReflTransGen (fun a b => 0 < fusionCoeff D i a b) j (unitIndex D) := by
  classical
  have hout : 0 < Ground.fusionFlow D i (unitIndex D) i := by
    unfold Ground.fusionFlow
    rw [fusionCoeff_comm D i (unitIndex D), fusionCoeff_unit]
    simpa [fpSimple_unit] using fpSimple_pos D i
  obtain ⟨j, hj, path⟩ := Ground.balanced_flow_cycle (Ground.fusionFlow D i)
    (Ground.fusionFlow_nonneg D i) (Ground.fusionFlow_balance D i) (unitIndex D) ⟨i, hout⟩
  have coeff_pos {a b} (h : 0 < Ground.fusionFlow D i a b) : 0 < fusionCoeff D i a b := by
    by_contra hz
    have hz' : fusionCoeff D i a b = 0 := Nat.eq_zero_of_not_pos hz
    simp [Ground.fusionFlow, hz'] at h
  exact ⟨j, coeff_pos hj, Relation.ReflTransGen.mono (fun _ _ h => coeff_pos h) _ _ path⟩

/-- A positive fusion coefficient gives an actual split inclusion. -/
theorem fusionCoeffRetract (D : Ground.BraidedFusionCategory.{v,u})
    (i a b : Fin (rank D)) (h : 0 < fusionCoeff D i a b) :
    Nonempty (Retract (simples D b) (simples D i ⊗ simples D a)) :=
  Ground.fusionCoeff_retract D i a b h

/-- Along any fusion path, an occurrence of its initial label in a power
extends to an occurrence of its final label in a later power. -/
theorem fusion_path_retract (D : Ground.BraidedFusionCategory.{v,u})
    (i : Fin (rank D)) {a b : Fin (rank D)}
    (path : Relation.ReflTransGen (fun a b => 0 < fusionCoeff D i a b) a b)
    (n : ℕ) (r : Retract (simples D a) (tensorPower (simples D i) (n + 1))) :
    ∃ m, Nonempty (Retract (simples D b) (tensorPower (simples D i) (m + 1))) := by
  induction path generalizing n with
  | refl => exact ⟨n, ⟨r⟩⟩
  | @tail b c p h ih =>
    obtain ⟨m, ⟨s⟩⟩ := ih n r
    obtain ⟨q⟩ := fusionCoeffRetract D i b c h
    let t := q.trans (s.map (tensorLeft (simples D i)))
    exact ⟨m + 1, ⟨t⟩⟩

end PropertyF.Ground.Cabling
