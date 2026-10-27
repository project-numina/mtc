module
public import PropertyF.Ground.Fusion.BalancedFlow
public import PropertyF.Ground.Fusion.ObjectDimension
public import PropertyF.Ground.Modular.BraidIso

/-! Every simple object has a positive tensor power containing the unit. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open scoped BigOperators
namespace PropertyF.Ground
universe v u

/-- The FP-weighted directed fusion graph is a balanced flow. -/
def fusionFlow (D : BraidedFusionCategory.{v,u}) (i j k : Fin (rank D)) : ℝ :=
  fpSimple D j * (fusionCoeff D i j k : ℝ) * fpSimple D k

theorem fusionFlow_nonneg (D : BraidedFusionCategory.{v,u}) (i j k : Fin (rank D)) :
    0 ≤ fusionFlow D i j k := by
  exact mul_nonneg (mul_nonneg (fpSimple_pos D j).le (Nat.cast_nonneg _)) (fpSimple_pos D k).le

theorem fusionFlow_balance (D : BraidedFusionCategory.{v,u}) (i j : Fin (rank D)) :
    (∑ k, fusionFlow D i j k) = ∑ k, fusionFlow D i k j := by
  classical
  have hc (k : Fin (rank D)) : fusionCoeff D i k j = fusionCoeff D (dualIndex D i) j k := by
    rw [fusionCoeff_comm D i k, fusionCoeff_reciprocity_labels, fusionCoeff_comm]
  calc
    _ = fpSimple D j * (∑ k, (fusionCoeff D i j k : ℝ) * fpSimple D k) := by
      simp only [fusionFlow, Finset.mul_sum, mul_assoc]
    _ = fpSimple D j * (fpSimple D i * fpSimple D j) := by rw [← fpSimple_mul]
    _ = fpSimple D j * (fpSimple D (dualIndex D i) * fpSimple D j) := by rw [fpSimple_dual]
    _ = fpSimple D j * (∑ k, (fusionCoeff D (dualIndex D i) j k : ℝ) * fpSimple D k) := by rw [fpSimple_mul]
    _ = _ := by
      simp only [fusionFlow, Finset.mul_sum, hc]
      apply Finset.sum_congr rfl
      intro k _
      ring

/-- A positive fusion coefficient gives an actual retract. -/
theorem fusionCoeff_retract (D : BraidedFusionCategory.{v,u})
    (i j k : Fin (rank D)) (h : 0 < fusionCoeff D i j k) :
    Nonempty (Retract (simples D k) (simples D i ⊗ simples D j)) := by
  letI : FiniteDimensional ℂ (simples D k ⟶ simples D i ⊗ simples D j) :=
    IsFusionCategory.hom_finite _ _
  obtain ⟨f, hf⟩ := Module.finrank_pos_iff_exists_ne_zero.mp h
  letI : Simple (simples D k) := simples_simple D k
  obtain ⟨r, hr⟩ := split_from_simple f hf
  exact ⟨{ i := f, r := r, retract := hr }⟩

/-- Along a fusion path beginning at i, the endpoint is a retract of a
positive tensor power of the simple i. -/
theorem fusionPath_retract (D : BraidedFusionCategory.{v,u}) (i k : Fin (rank D))
    (h : Relation.ReflTransGen (fun j k => 0 < fusionFlow D i j k) i k) :
    ∃ n, Nonempty (Retract (simples D k) (tensorPower (simples D i) (n + 1))) := by
  induction h with
  | refl =>
    exact ⟨0, ⟨Retract.ofIso (ρ_ (simples D i)).symm⟩⟩
  | @tail j k h edge ih =>
    obtain ⟨n, ⟨r⟩⟩ := ih
    have hn : 0 < fusionCoeff D i j k := by
      have hp : 0 < (fusionCoeff D i j k : ℝ) := by
        have hh := edge
        unfold fusionFlow at hh
        exact (mul_pos_iff_of_pos_left (fpSimple_pos D j)).mp
          ((mul_pos_iff_of_pos_right (fpSimple_pos D k)).mp hh)
      exact_mod_cast hp
    obtain ⟨s⟩ := fusionCoeff_retract D i j k hn
    let t : Retract (simples D i ⊗ simples D j)
        (simples D i ⊗ tensorPower (simples D i) (n + 1)) :=
      { i := 𝟙 _ ⊗ₘ r.i
        r := 𝟙 _ ⊗ₘ r.r
        retract := by rw [tensorHom_comp_tensorHom, Category.id_comp, r.retract, id_tensorHom_id] }
    exact ⟨n + 1, ⟨s.trans t⟩⟩

/-- A simple object has a positive tensor power containing the unit. -/
theorem unit_retract_tensorPower (D : BraidedFusionCategory.{v,u})
    (X : D.Obj) [Simple X] : ∃ n, Nonempty (Retract (𝟙_ D.Obj) (tensorPower X (n + 1))) := by
  classical
  obtain ⟨i, ⟨e⟩⟩ := exists_simple_iso D X
  have hout : 0 < fusionFlow D i (unitIndex D) i := by
    unfold fusionFlow
    rw [fusionCoeff_comm D i (unitIndex D), fusionCoeff_unit, if_pos rfl, Nat.cast_one]
    simpa [fpSimple_unit] using fpSimple_pos D i
  obtain ⟨j, hj, hp⟩ := balanced_flow_cycle (fusionFlow D i) (fusionFlow_nonneg D i)
    (fusionFlow_balance D i) (unitIndex D) ⟨i, hout⟩
  have hji : j = i := by
    unfold fusionFlow at hj
    rw [fusionCoeff_comm D i (unitIndex D), fusionCoeff_unit] at hj
    by_contra h
    simp [h] at hj
  subst j
  obtain ⟨n, ⟨r⟩⟩ := fusionPath_retract D i (unitIndex D) hp
  obtain ⟨u⟩ := unitIndex_iso D
  exact ⟨n, ⟨(Retract.ofIso u.symm).trans (r.trans (Retract.ofIso (Modular.tensorPowerIso e.symm _)))⟩⟩

end PropertyF.Ground
