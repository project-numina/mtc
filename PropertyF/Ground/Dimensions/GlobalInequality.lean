module
public import PropertyF.Ground.Dimensions.GroundNorm
public import Mathlib.Tactic

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
open scoped BigOperators
namespace PropertyF.Ground.Dimensions
universe v u

/-- Once the simple spherical dimensions are real, the intrinsic global
dimension is their sum of squares. -/
theorem target_globalDimension_real (C : Ground.BraidedFusionCategory.{v,u})
    (p : PivotalStructure (C := C.Obj)) (hp : p.IsSpherical)
    (d : Fin (Ground.rank C) → ℝ)
    (hd : ∀ i, Ground.unitScalar C (rightQuantumTrace (p.iso (Ground.simples C i))) = (d i : ℂ)) :
    Ground.globalDimension C = ((∑ i, (d i) ^ 2 : ℝ) : ℂ) := by
  rw [target_globalDimension_eq_sum_squares C p hp]
  simp [hd, Complex.ofReal_sum, Complex.ofReal_pow]

/-- The global inequality follows from the simple-object estimates; this
separates the sum-of-squares argument from the remaining ENO estimate. -/
theorem target_globalDimension_le_of_simple_bounds (C : Ground.BraidedFusionCategory.{v,u})
    (d : Fin (Ground.rank C) → ℝ)
    (hbound : ∀ i, |d i| ≤ Ground.fpSimple C i) :
    ∑ i, (d i) ^ 2 ≤ Ground.globalFPDimension C := by
  unfold Ground.globalFPDimension
  apply Finset.sum_le_sum
  intro i _
  have hneg : -Ground.fpSimple C i ≤ d i := (abs_le.mp (hbound i)).1
  have hpos : d i ≤ Ground.fpSimple C i := (abs_le.mp (hbound i)).2
  have hsum : 0 ≤ d i + Ground.fpSimple C i := by linarith
  nlinarith [mul_nonneg (sub_nonneg.mpr hpos) hsum]

/-- A nonzero real simple dimension makes the sum of squares strictly positive. -/
theorem global_sum_squares_positive {ι : Type*} [Fintype ι]
    (d : ι → ℝ) (h : ∃ i, d i ≠ 0) : 0 < ∑ i, (d i) ^ 2 := by
  classical
  obtain ⟨i, hi⟩ := h
  apply Finset.sum_pos'
  · intro j _
    exact sq_nonneg (d j)
  · exact ⟨i, Finset.mem_univ i, sq_pos_of_ne_zero hi⟩

end PropertyF.Ground.Dimensions
