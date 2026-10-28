module
public import PropertyF.Ground.Fusion.Multiplicity
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
public import Mathlib.Analysis.Normed.Algebra.GelfandFormula
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
public import Mathlib.Analysis.Matrix.Normed

/-! # Integrality of spectral-radius dimensions

The spectral radius of an integer matrix on a nonempty index type has an integral
square. Applying this to the fusion matrices proves `fpSimple_isIntegral`; the unit matrix also gives
`fpSimple_unit` and the lower bound on the global FP dimension.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
open scoped BigOperators Matrix.Norms.Operator

namespace PropertyF.Ground

variable (D : BraidedFusionCategory)

/-- The tensor unit supplies a simple label. -/
local instance (D : BraidedFusionCategory) : Nonempty (Fin (rank D)) := ⟨unitIndex D⟩

/-- The spectral-radius FP dimension is normalized on the tensor unit. -/
theorem fpSimple_unit :
    fpSimple D (unitIndex D) = 1 :=
  by rw [fpSimple, show fusionMatrix D (unitIndex D) = 1 from Matrix.ext fun k j ↦ by
    change (fusionCoeff D (unitIndex D) j k : ℂ) = _
    simp [fusionCoeff_unit, Matrix.one_apply], spectrum.spectralRadius_one, ENNReal.toReal_one]

/-- The global FP dimension is at least one, from the unit contribution. -/
theorem one_le_globalFPDimension :
    1 ≤ globalFPDimension D :=
  by simpa [globalFPDimension, fpSimple_unit] using
    (Finset.single_le_sum (f := fun i => fpSimple D i ^ 2)
      (fun i _ => sq_nonneg (fpSimple D i)) (Finset.mem_univ (unitIndex D)))

/-- The squared spectral radius of an integer matrix is integral over ℤ.
The index type is nonempty so that the complex matrix algebra is nontrivial. -/
theorem integer_matrix_spectralRadius_sq_isIntegral {ι : Type*} [Fintype ι]
    [DecidableEq ι] [Nonempty ι] (A : Matrix ι ι ℤ) :
    IsIntegral ℤ ((spectralRadius ℂ (A.map (Int.castRingHom ℂ))).toReal ^ 2) := by
  let B : Matrix ι ι ℂ := A.map (Int.castRingHom ℂ)
  obtain ⟨z, hz, hzmax⟩ := spectrum.exists_nnnorm_eq_spectralRadius B
  have hzint : IsIntegral ℤ z := ⟨A.charpoly, A.charpoly_monic, by
    change Polynomial.eval₂ (Int.castRingHom ℂ) z A.charpoly = 0
    rw [Polynomial.eval₂_eq_eval_map, ← Matrix.charpoly_map]
    exact ((Matrix.mem_spectrum_iff_isRoot_charpoly.mp hz).eq_zero)⟩
  rw [← hzmax, ENNReal.coe_toReal, coe_nnnorm]
  apply (isIntegral_algebraMap_iff (R := ℤ) (A := ℝ) (B := ℂ)).mp
  change IsIntegral ℤ ((‖z‖ ^ 2 : ℝ) : ℂ)
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self]
  exact (hzint.map Complex.conjAe).mul hzint

variable {D} in
/-- Every target simple FP dimension is integral over ℤ. -/
theorem fpSimple_isIntegral (i : Fin (rank D)) :
    IsIntegral ℤ (fpSimple D i) := by
  let A : Matrix (Fin (rank D)) (Fin (rank D)) ℤ := fun k j =>
    fusionCoeff D i j k
  have hmatrix : A.map (Int.castRingHom ℂ) = fusionMatrix D i := by
    ext k j
    change (((Module.finrank ℂ (simples D k ⟶ simples D i ⊗ simples D j) : ℤ) : ℂ)) = _
    simp [fusionMatrix]
  apply IsIntegral.of_pow (Nat.zero_lt_succ 1)
  simpa only [hmatrix, fpSimple] using integer_matrix_spectralRadius_sq_isIntegral A


end PropertyF.Ground
