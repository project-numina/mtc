module
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.Data.Fintype.Lattice
public import Mathlib.Tactic

/-! Elementary uniqueness of a positive matrix eigenvector. -/

@[expose] public noncomputable section
open scoped BigOperators Matrix

namespace PropertyF.Ground

/-- For a strictly positive matrix, the eigenspace of any strictly positive
eigenvector is one-dimensional. No spectral theorem is assumed. -/
theorem positive_matrix_eigenspace_unique {ι : Type*} [Fintype ι] [Nonempty ι]
    (A : Matrix ι ι ℝ) (hA : ∀ i j, 0 < A i j)
    (x y : ι → ℝ) (hx : ∀ i, 0 < x i) (d : ℝ)
    (hxe : A *ᵥ x = d • x) (hye : A *ᵥ y = d • y) :
    ∃ c : ℝ, y = c • x := by
  classical
  obtain ⟨i, _, hmin⟩ := Finset.exists_min_image Finset.univ (fun j => y j / x j)
    Finset.univ_nonempty
  let c := y i / x i
  have hnonneg (j : ι) : 0 ≤ y j - c * x j := by
    have hj := hmin j (Finset.mem_univ j)
    dsimp [c] at hj ⊢
    have hmul := mul_le_mul_of_nonneg_right hj (hx j).le
    have : y i / x i * x j ≤ y j := by
      simpa [div_mul_cancel₀ _ (ne_of_gt (hx j))] using hmul
    linarith
  have hzero : y i - c * x i = 0 := by
    simp [c, div_mul_cancel₀ _ (ne_of_gt (hx i))]
  have hsum : ∑ j, A i j * (y j - c * x j) = 0 := by
    have ex := congrFun hxe i
    have ey := congrFun hye i
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at ex ey
    calc
      _ = (∑ j, A i j * y j) - c * (∑ j, A i j * x j) := by
        simp only [mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
        apply congrArg₂ (· - ·) rfl
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = d * (y i - c * x i) := by rw [ex, ey]; ring
      _ = 0 := by rw [hzero, mul_zero]
  have hall : ∀ j, y j - c * x j = 0 := by
    intro j
    have hj := (Finset.sum_eq_zero_iff_of_nonneg
      (fun j _ => mul_nonneg (hA i j).le (hnonneg j))).mp hsum j (Finset.mem_univ j)
    exact (mul_eq_zero.mp hj).resolve_left (ne_of_gt (hA i j))
  refine ⟨c, ?_⟩
  funext j
  simp only [Pi.smul_apply, smul_eq_mul]
  linarith [hall j]

end PropertyF.Ground
