module
public import PropertyF.Ground.Fusion.Multiplicity
public import PropertyF.Ground.Fusion.MatrixIntegral
public import Mathlib.Analysis.Normed.Algebra.GelfandFormula
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
public import Mathlib.Analysis.Matrix.Normed

/-! Algebraic integrality for the target spectral-radius dimensions. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
open scoped BigOperators Matrix.Norms.Operator

namespace PropertyF.Ground

/-- The fusion matrix of the tensor unit is the identity. -/
theorem fusionMatrix_unit (D : BraidedFusionCategory) :
    fusionMatrix D (unitIndex D) = 1 := by
  classical
  ext k j
  change (fusionCoeff D (unitIndex D) j k : ℂ) = _
  rw [fusionCoeff_unit]
  simp [Matrix.one_apply]

/-- The spectral-radius FP dimension is normalized on the tensor unit. -/
theorem fpSimple_unit (D : BraidedFusionCategory) :
    fpSimple D (unitIndex D) = 1 := by
  classical
  letI : Nonempty (Fin (rank D)) := ⟨unitIndex D⟩
  simp [fpSimple, fusionMatrix_unit, spectrum.spectralRadius_one]

/-- The global FP dimension is at least one, from the unit contribution. -/
theorem one_le_globalFPDimension (D : BraidedFusionCategory) :
    1 ≤ globalFPDimension D := by
  classical
  unfold globalFPDimension
  have h := Finset.single_le_sum (f := fun i => fpSimple D i ^ 2)
    (fun i _ => sq_nonneg (fpSimple D i)) (Finset.mem_univ (unitIndex D))
  simpa [fpSimple_unit] using h

/-- The squared spectral radius of an integer matrix is integral over ℤ.
The index type is nonempty so that the complex matrix algebra is nontrivial. -/
theorem integer_matrix_spectralRadius_sq_isIntegral {ι : Type*} [Fintype ι]
    [DecidableEq ι] [Nonempty ι] (A : Matrix ι ι ℤ) :
    IsIntegral ℤ ((spectralRadius ℂ (A.map (Int.castRingHom ℂ))).toReal ^ 2) := by
  let B : Matrix ι ι ℂ := A.map (Int.castRingHom ℂ)
  obtain ⟨z, hz, hzmax⟩ := spectrum.exists_nnnorm_eq_spectralRadius B
  have hroot := (Matrix.mem_spectrum_iff_isRoot_charpoly.mp hz).eq_zero
  have hzint : IsIntegral ℤ z := by
    refine ⟨A.charpoly, A.charpoly_monic, ?_⟩
    change Polynomial.eval₂ (Int.castRingHom ℂ) z A.charpoly = 0
    rw [Polynomial.eval₂_eq_eval_map, ← Matrix.charpoly_map]
    exact hroot
  have hconj : IsIntegral ℤ (starRingEnd ℂ z) := hzint.map Complex.conjAe
  have hprod : IsIntegral ℤ (starRingEnd ℂ z * z) := hconj.mul hzint
  have hnorm : IsIntegral ℤ (‖z‖ ^ 2 : ℝ) := by
    have hc : IsIntegral ℤ ((‖z‖ ^ 2 : ℝ) : ℂ) := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self]
      exact hprod
    exact (isIntegral_algebraMap_iff (R := ℤ) (A := ℝ) (B := ℂ)).mp hc
  have hreal : (spectralRadius ℂ B).toReal = ‖z‖ := by
    rw [← hzmax]
    simp
  rw [← hreal] at hnorm
  exact hnorm

/-- Every target simple FP dimension is integral over ℤ. -/
theorem fpSimple_isIntegral (D : BraidedFusionCategory) (i : Fin (rank D)) :
    IsIntegral ℤ (fpSimple D i) := by
  classical
  letI : Nonempty (Fin (rank D)) := ⟨unitIndex D⟩
  let A : Matrix (Fin (rank D)) (Fin (rank D)) ℤ := fun k j =>
    fusionCoeff D i j k
  have hmatrix : A.map (Int.castRingHom ℂ) = fusionMatrix D i := by
    ext k j
    change (((Module.finrank ℂ (simples D k ⟶ simples D i ⊗ simples D j) : ℤ) : ℂ)) = _
    simp [fusionMatrix]
  have hsquared := integer_matrix_spectralRadius_sq_isIntegral A
  rw [hmatrix] at hsquared
  exact IsIntegral.of_pow (by decide : 0 < 2) hsquared

/-- The target's global FP dimension is integral over ℤ, independently of
the construction of a positive fusion-ring character. -/
theorem globalFPDimension_isIntegral (D : BraidedFusionCategory) :
    IsIntegral ℤ (globalFPDimension D) := by
  unfold globalFPDimension
  apply IsIntegral.sum
  intro i _
  exact (fpSimple_isIntegral D i).pow 2

end PropertyF.Ground
