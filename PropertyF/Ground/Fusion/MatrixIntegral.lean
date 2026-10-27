module
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic

/-! Eigenvalues of integer matrices are algebraic integers. -/

@[expose] public noncomputable section
open scoped BigOperators Matrix

namespace PropertyF.Ground

/-- A real eigenvalue of an integer matrix is integral over the integers.
The nonzero-vector hypothesis is an explicit coordinate, so this also works
uniformly when the index type is potentially empty. -/
theorem integer_matrix_eigenvalue_isIntegral {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℤ) (d : ℝ) (v : ι → ℝ) (i : ι) (hvi : v i ≠ 0)
    (hv : A.map (Int.castRingHom ℝ) *ᵥ v = d • v) : IsIntegral ℤ d := by
  let B : Matrix ι ι ℝ := A.map (Int.castRingHom ℝ)
  have hzero : (Matrix.scalar ι d - B) *ᵥ v = 0 := by
    rw [Matrix.sub_mulVec, hv]
    ext j
    simp [Matrix.scalar_apply]
  have hdet : (Matrix.scalar ι d - B).det = 0 := by
    exact Matrix.det_eq_zero_of_mulVec_eq_zero_of_mem_nonZeroDivisors hzero
      (mem_nonZeroDivisors_of_ne_zero hvi)
  refine ⟨A.charpoly, A.charpoly_monic, ?_⟩
  change Polynomial.eval₂ (Int.castRingHom ℝ) d A.charpoly = 0
  rw [Polynomial.eval₂_eq_eval_map, ← Matrix.charpoly_map, Matrix.eval_charpoly]
  exact hdet

end PropertyF.Ground
