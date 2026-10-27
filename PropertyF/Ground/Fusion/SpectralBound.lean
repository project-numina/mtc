module
public import PropertyF.Ground.Fusion.PositiveMatrix
public import Mathlib.Analysis.Complex.Basic

/-! Spectral bounds from a positive eigenvector. -/

@[expose] public noncomputable section
open scoped BigOperators Matrix

namespace PropertyF.Ground

/-- A positive real eigenvector bounds the modulus of every complex eigenvalue
of a nonnegative real matrix. -/
theorem complex_eigenvalue_le_positive_eigenvalue {ι : Type*} [Fintype ι] [Nonempty ι]
    (A : Matrix ι ι ℝ) (hA : ∀ i j, 0 ≤ A i j) (w : ι → ℝ)
    (hw : ∀ i, 0 < w i) (d : ℝ) (hwe : A *ᵥ w = d • w)
    (z : ℂ) (v : ι → ℂ) (hv : v ≠ 0)
    (hve : A.map Complex.ofRealHom *ᵥ v = z • v) : ‖z‖ ≤ d := by
  classical
  obtain ⟨i, _, hmax⟩ := Finset.exists_max_image Finset.univ (fun j => ‖v j‖ / w j)
    Finset.univ_nonempty
  have hiv : v i ≠ 0 := by
    intro hi
    have hall : ∀ j, v j = 0 := by
      intro j
      have h := hmax j (Finset.mem_univ j)
      simp [hi] at h
      have : ‖v j‖ = 0 := by
        apply le_antisymm
        · have hh := (div_le_iff₀ (hw j)).mp h
          simpa using hh
        · exact norm_nonneg _
      exact norm_eq_zero.mp this
    apply hv
    funext j
    simpa using hall j
  have hbound (j : ι) : ‖v j‖ ≤ (‖v i‖ / w i) * w j := by
    have h := hmax j (Finset.mem_univ j)
    exact (div_le_iff₀ (hw j)).mp h
  have hrow := congrFun hwe i
  have hrowc := congrFun hve i
  simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at hrow hrowc
  change (∑ j, (A i j : ℂ) * v j) = z * v i at hrowc
  have hineq : ‖z‖ * ‖v i‖ ≤ d * ‖v i‖ := by
    calc
      _ = ‖∑ j, (A i j : ℂ) * v j‖ := by rw [hrowc, norm_mul]
      _ ≤ ∑ j, ‖(A i j : ℂ) * v j‖ := norm_sum_le _ _
      _ = ∑ j, A i j * ‖v j‖ := by
        apply Finset.sum_congr rfl
        intro j _
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hA i j)]
      _ ≤ ∑ j, A i j * ((‖v i‖ / w i) * w j) := by
        exact Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hbound j) (hA i j)
      _ = (‖v i‖ / w i) * (∑ j, A i j * w j) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = (‖v i‖ / w i) * (d * w i) := by rw [hrow]
      _ = d * ‖v i‖ := by field_simp [ne_of_gt (hw i)]
  exact le_of_mul_le_mul_right hineq (norm_pos_iff.mpr hiv)

end PropertyF.Ground
