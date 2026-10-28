module
public import PropertyF.Ground.Dimensions.GroundNorm
public import Mathlib.Tactic

/-! # Bounds for global dimension

Simple-object bounds and equality conditions control the intrinsic global dimension.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
open scoped BigOperators
namespace PropertyF.Ground.Dimensions
universe v u

variable (C : BraidedFusionCategory.{v,u})
/-- The global inequality follows from the simple-object estimates; this
separates the sum-of-squares argument from the remaining ENO estimate. -/
theorem target_globalDimension_le_of_simple_bounds
    (d : Fin (rank C) → ℝ)
    (hbound : ∀ i, |d i| ≤ fpSimple C i) :
    ∑ i, (d i) ^ 2 ≤ globalFPDimension C := by
  unfold globalFPDimension
  apply Finset.sum_le_sum
  intro i _
  have hneg : -fpSimple C i ≤ d i := (abs_le.mp (hbound i)).1
  have hpos : d i ≤ fpSimple C i := (abs_le.mp (hbound i)).2
  have hsum : 0 ≤ d i + fpSimple C i := by linarith
  nlinarith [mul_nonneg (sub_nonneg.mpr hpos) hsum]

/-- If each real simple dimension is bounded by its FP dimension, equality of
the global sums is equivalent to saturation at every simple. -/
theorem global_sum_squares_eq_iff
    (d : Fin (rank C) → ℝ)
    (hbound : ∀ i, |d i| ≤ fpSimple C i) :
    (∑ i, (d i) ^ 2) = globalFPDimension C ↔
      ∀ i, |d i| = fpSimple C i := by
  have hsq : ∀ i, (d i) ^ 2 ≤ (fpSimple C i) ^ 2 := by
    intro i
    have hneg : -fpSimple C i ≤ d i := (abs_le.mp (hbound i)).1
    have hpos : d i ≤ fpSimple C i := (abs_le.mp (hbound i)).2
    have hsum : 0 ≤ d i + fpSimple C i := by linarith
    nlinarith [mul_nonneg (sub_nonneg.mpr hpos) hsum]
  rw [globalFPDimension, Finset.sum_eq_sum_iff_of_le (fun i _ => hsq i)]
  constructor
  · intro heq i
    have h := heq i (Finset.mem_univ i)
    have ha : 0 ≤ |d i| := abs_nonneg _
    have hb : 0 ≤ fpSimple C i := le_trans ha (hbound i)
    nlinarith [sq_abs (d i)]
  · intro heq i _
    rw [← heq i, sq_abs]

/-- If some simple has real dimension one, the global sum is at least one. -/
theorem global_sum_squares_one_le {ι : Type*} [Fintype ι]
    (d : ι → ℝ) (h : ∃ i, d i = 1) : 1 ≤ ∑ i, (d i) ^ 2 := by
  classical
  obtain ⟨i, hi⟩ := h
  simpa [hi] using
    (Finset.single_le_sum (fun j _ => sq_nonneg (d j)) (Finset.mem_univ i))

end PropertyF.Ground.Dimensions
