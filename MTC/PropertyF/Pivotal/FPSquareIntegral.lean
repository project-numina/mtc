module
public import MTC.PropertyF.Pivotal.GaloisDimensionTransport
public import MTC.Fusion.ObjectDimension

/-! # Squared FP dimensions in weakly integral fusion categories

A Galois conjugate of the FP character is bounded coordinatewise by the FP
character. If global FP dimension is an integer, its fixed sum of squares
forces equality at every coordinate, hence every squared simple FP dimension
is an integer.
-/

@[expose] public noncomputable section
open CategoryTheory MTC.Fusion MTC.Braided MTC.PropertyF.Reduction
open MTC.CategoryTheory.Dimensions
open scoped BigOperators
namespace MTC.PropertyF.Pivotal
universe v u
variable (C : BraidedFusionCategory.{v,u})

/-- Every complex-field automorphism fixes the squared FP dimension of each
simple when the actual global FP dimension is an integer. -/
theorem fpSimple_sq_galois_fixed_of_weaklyIntegral
    (h : WeaklyIntegral (globalFPDimension C)) (σ : ℂ ≃+* ℂ)
    (i : Fin (rank C)) : σ ((fpSimple C i : ℂ) ^ 2) = (fpSimple C i : ℂ) ^ 2 := by
  let g (j : Fin (rank C)) : ℝ := (σ (fpSimple C j : ℂ)).re
  have hg (j : Fin (rank C)) : (g j : ℂ) = σ (fpSimple C j : ℂ) :=
    fp_simple_galois_real C σ j
  have hb (j : Fin (rank C)) : |g j| ≤ fpSimple C j :=
    fp_simple_galois_abs_le C σ j
  have hsum : ∑ j, g j ^ 2 = ∑ j, fpSimple C j ^ 2 := by
    have hfix := weaklyIntegral_galois_fixed (globalFPDimension C) h σ
    change σ ((∑ j, fpSimple C j ^ 2 : ℝ) : ℂ) = _ at hfix
    simp only [Complex.ofReal_sum, Complex.ofReal_pow, map_sum, map_pow, ← hg] at hfix
    exact_mod_cast hfix
  have hle (j : Fin (rank C)) : g j ^ 2 ≤ fpSimple C j ^ 2 := by
    have hj := hb j
    have hp := (fpSimple_pos C j).le
    nlinarith [sq_abs (g j), abs_nonneg (g j)]
  have heq := (Finset.sum_eq_sum_iff_of_le (fun j _ ↦ hle j)).mp hsum i (Finset.mem_univ i)
  rw [map_pow, ← hg i, ← Complex.ofReal_pow, heq, Complex.ofReal_pow]

/-- Weak integrality forces each simple FP dimension to have integral square. -/
theorem fpSimple_sq_integral_of_weaklyIntegral
    (h : WeaklyIntegral (globalFPDimension C)) (i : Fin (rank C)) :
    WeaklyIntegral (fpSimple C i ^ 2) :=
  integral_eq_int_of_complex_galois_fixed ((fpSimple_isIntegral i).pow 2)
    (fun σ ↦ by
      change σ (((fpSimple C i ^ 2 : ℝ) : ℂ)) = ((fpSimple C i ^ 2 : ℝ) : ℂ)
      simpa only [Complex.ofReal_pow] using
        fpSimple_sq_galois_fixed_of_weaklyIntegral C h σ i)

/-- The squared FP dimension of every actual simple object is an integer in a
weakly integral braided fusion category. -/
theorem simple_fpDimension_sq_integral_of_weaklyIntegral
    (h : WeaklyIntegral (globalFPDimension C)) (X : C.Obj) [Simple X] :
    WeaklyIntegral (fpDimension C X ^ 2) := by
  obtain ⟨i, ⟨e⟩⟩ := exists_simple_iso C X
  rw [fpDimension_iso e, fpDimension_simple]
  exact fpSimple_sq_integral_of_weaklyIntegral C h i

end MTC.PropertyF.Pivotal
end
