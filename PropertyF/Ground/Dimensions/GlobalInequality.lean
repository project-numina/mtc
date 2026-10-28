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
    ∑ i, (d i) ^ 2 ≤ globalFPDimension C :=
  Finset.sum_le_sum fun i _ => sq_le_sq' (abs_le.mp (hbound i)).1 (abs_le.mp (hbound i)).2

/-- If each real simple dimension is bounded by its FP dimension, equality of
the global sums is equivalent to saturation at every simple. -/
theorem global_sum_squares_eq_iff
    (d : Fin (rank C) → ℝ)
    (hbound : ∀ i, |d i| ≤ fpSimple C i) :
    (∑ i, (d i) ^ 2) = globalFPDimension C ↔
      ∀ i, |d i| = fpSimple C i := by
  rw [globalFPDimension, Finset.sum_eq_sum_iff_of_le
    (fun i _ => sq_le_sq' (abs_le.mp (hbound i)).1 (abs_le.mp (hbound i)).2)]
  constructor
  · intro heq i
    apply (sq_eq_sq₀ (abs_nonneg _) ((abs_nonneg _).trans (hbound i))).mp
    simpa only [sq_abs] using heq i (Finset.mem_univ i)
  · intro heq i _
    rw [← heq i, sq_abs]

/-- A pseudo-unitary global dimension saturates every FP bound when the
intrinsic norms are the squared norms of the given dimensions. -/
theorem norm_saturation_of_pseudoUnitary (d : Fin (rank C) → ℂ)
    (hbound : ∀ i, ‖d i‖ ≤ fpSimple C i)
    (hnorm : ∀ i, squaredNorm C (simples C i) = ((‖d i‖ ^ 2 : ℝ) : ℂ))
    (hpu : PseudoUnitary C) : ∀ i, ‖d i‖ = fpSimple C i := by
  have hb : ∀ i, |‖d i‖| ≤ fpSimple C i := by
    intro i
    simpa only [abs_of_nonneg (norm_nonneg _)] using hbound i
  have hg : (∑ i, ‖d i‖ ^ 2) = globalFPDimension C := by
    have h := hpu
    change globalDimension C = (globalFPDimension C : ℂ) at h
    unfold globalDimension at h
    simp only [hnorm, ← Complex.ofReal_sum] at h
    exact Complex.ofReal_injective h
  intro i
  simpa only [abs_of_nonneg (norm_nonneg _)] using
    (global_sum_squares_eq_iff C (fun i => ‖d i‖) hb).1 hg i

/-- If some simple has real dimension one, the global sum is at least one. -/
theorem global_sum_squares_one_le {ι : Type*} [Fintype ι]
    (d : ι → ℝ) (h : ∃ i, d i = 1) : 1 ≤ ∑ i, (d i) ^ 2 := by
  classical
  obtain ⟨i, hi⟩ := h
  simpa [hi] using
    (Finset.single_le_sum (fun j _ => sq_nonneg (d j)) (Finset.mem_univ i))

end PropertyF.Ground.Dimensions
