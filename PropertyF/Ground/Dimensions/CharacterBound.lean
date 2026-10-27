module
public import PropertyF.Ground.Fusion.SpectralIntegral
public import Mathlib.Analysis.Matrix.Spectrum

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
open scoped BigOperators Matrix Matrix.Norms.Operator ENNReal
namespace PropertyF.Ground.Dimensions

/-- Each value of any nonzero fusion-ring character is bounded in absolute value
by the spectral-radius FP dimension. No positivity of the character is needed. -/
theorem character_norm_le_fpSimple (C : Ground.BraidedFusionCategory)
    (χ : Fin (Ground.rank C) → ℂ) (i₀ : Fin (Ground.rank C)) (hχ : χ i₀ ≠ 0)
    (hchar : ∀ i j, χ i * χ j = ∑ k,
      (Ground.fusionCoeff C i j k : ℂ) * χ k) (i : Fin (Ground.rank C)) :
    ‖χ i‖ ≤ Ground.fpSimple C i := by
  classical
  let A := (Ground.fusionMatrix C i)ᵀ
  have heigen : A *ᵥ χ = χ i • χ := by
    ext j
    change (∑ k, (Ground.fusionCoeff C i j k : ℂ) * χ k) = χ i * χ j
    exact (hchar i j).symm
  have hzero : (Matrix.scalar (Fin (Ground.rank C)) (χ i) - A) *ᵥ χ = 0 := by
    rw [Matrix.sub_mulVec, heigen]
    ext j
    simp [Matrix.scalar_apply]
  have hdet : (Matrix.scalar (Fin (Ground.rank C)) (χ i) - A).det = 0 :=
    Matrix.det_eq_zero_of_mulVec_eq_zero_of_mem_nonZeroDivisors hzero
      (mem_nonZeroDivisors_of_ne_zero hχ)
  have hz : χ i ∈ spectrum ℂ A := by
    apply Matrix.mem_spectrum_iff_isRoot_charpoly.mpr
    change Polynomial.eval (χ i) A.charpoly = 0
    rw [Matrix.eval_charpoly]
    exact hdet
  have hle : (‖χ i‖₊ : ℝ≥0∞) ≤ spectralRadius ℂ A := by
    rw [spectralRadius_eq_of_unital]
    exact le_iSup_of_le (χ i) (le_iSup_of_le hz le_rfl)
  have htop : spectralRadius ℂ A ≠ ⊤ := by
    exact ne_of_lt (lt_of_le_of_lt (spectralRadius_le_nnnorm (𝕜 := ℂ) A) (by simp))
  have hreal := ENNReal.toReal_mono htop hle
  simpa [Ground.fpSimple, A, Matrix.spectralRadius_transpose] using hreal

/-- Every value of a nonzero fusion character is an algebraic integer: it is
an eigenvalue of the corresponding integral fusion matrix. -/
theorem character_value_isIntegral (C : Ground.BraidedFusionCategory)
    (χ : Fin (Ground.rank C) → ℂ) (i₀ : Fin (Ground.rank C)) (hχ : χ i₀ ≠ 0)
    (hchar : ∀ i j, χ i * χ j = ∑ k,
      (Ground.fusionCoeff C i j k : ℂ) * χ k) (i : Fin (Ground.rank C)) :
    IsIntegral ℤ (χ i) := by
  classical
  let M : Matrix (Fin (Ground.rank C)) (Fin (Ground.rank C)) ℤ := fun j k =>
    Ground.fusionCoeff C i j k
  let A := M.map (Int.castRingHom ℂ)
  have heigen : A *ᵥ χ = χ i • χ := by
    ext j
    change (∑ k, (((Ground.fusionCoeff C i j k : ℤ) : ℂ)) * χ k) = χ i * χ j
    simpa using (hchar i j).symm
  have hzero : (Matrix.scalar (Fin (Ground.rank C)) (χ i) - A) *ᵥ χ = 0 := by
    rw [Matrix.sub_mulVec, heigen]
    ext j
    simp [Matrix.scalar_apply]
  have hdet : (Matrix.scalar (Fin (Ground.rank C)) (χ i) - A).det = 0 :=
    Matrix.det_eq_zero_of_mulVec_eq_zero_of_mem_nonZeroDivisors hzero
      (mem_nonZeroDivisors_of_ne_zero hχ)
  refine ⟨M.charpoly, M.charpoly_monic, ?_⟩
  change Polynomial.eval₂ (Int.castRingHom ℂ) (χ i) M.charpoly = 0
  rw [Polynomial.eval₂_eq_eval_map, ← Matrix.charpoly_map, Matrix.eval_charpoly]
  exact hdet

/-- Every complex field conjugate of a fusion character obeys the same FP
bound, because field automorphisms preserve the integer fusion coefficients. -/
theorem galois_character_norm_le_fpSimple (C : Ground.BraidedFusionCategory)
    (χ : Fin (Ground.rank C) → ℂ) (i₀ : Fin (Ground.rank C)) (hχ : χ i₀ ≠ 0)
    (hchar : ∀ i j, χ i * χ j = ∑ k,
      (Ground.fusionCoeff C i j k : ℂ) * χ k)
    (σ : ℂ ≃+* ℂ) (i : Fin (Ground.rank C)) :
    ‖σ (χ i)‖ ≤ Ground.fpSimple C i := by
  apply character_norm_le_fpSimple C (fun j => σ (χ j)) i₀
  · exact (map_ne_zero σ).2 hχ
  · intro j k
    simpa using congrArg σ (hchar j k)

end PropertyF.Ground.Dimensions
