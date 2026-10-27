module
public import PropertyF.Ground.Integrate.ConjugateBound
public import PropertyF.Ground.Fusion.Agreement

/-! The FP fusion character is self-dual, so all its conjugates are real
and bounded. This gives global FP conjugate bounds without any spherical or
pseudo-unitary assumptions. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
open scoped BigOperators
namespace PropertyF.Ground
universe v u

/-- Every Galois conjugate of an actual simple FP dimension is real. -/
theorem fp_simple_galois_real (C : BraidedFusionCategory.{v,u})
    (σ : ℂ ≃+* ℂ) (i : Fin (rank C)) :
    (((σ (fpSimple C i : ℂ)).re : ℝ) : ℂ) = σ (fpSimple C i : ℂ) := by
  let χ : Fin (rank C) → ℂ := fun i => (fpSimple C i : ℂ)
  have hχ : χ (unitIndex C) ≠ 0 := by simp [χ, fpSimple_unit]
  have hchar : ∀ i j, χ i * χ j = ∑ k, (fusionCoeff C i j k : ℂ) * χ k := by
    intro i j
    dsimp [χ]
    exact_mod_cast fpSimple_mul C i j
  have hdual : ∀ i, χ (dualIndex C i) = χ i := by intro i; simp [χ, fpSimple_dual]
  apply Complex.conj_eq_iff_re.mp
  simpa only [← Complex.star_def] using selfDual_character_galois_real C χ (unitIndex C)
    hχ hchar hdual σ i

/-- Global FP dimension has positive, FP-bounded real conjugates. -/
theorem positive_bounded_conjugates_of_fp (C : BraidedFusionCategory.{v,u})
    (σ : ℂ ≃+* ℂ) : ∃ a : ℝ, 0 < a ∧ a ≤ globalFPDimension C ∧
      σ (globalFPDimension C : ℂ) = (a : ℂ) := by
  let χ : Fin (rank C) → ℂ := fun i => (fpSimple C i : ℂ)
  have hχ : χ (unitIndex C) ≠ 0 := by simp [χ, fpSimple_unit]
  have hchar : ∀ i j, χ i * χ j = ∑ k, (fusionCoeff C i j k : ℂ) * χ k := by
    intro i j
    dsimp [χ]
    exact_mod_cast fpSimple_mul C i j
  let d : Fin (rank C) → ℝ := fun i => (σ (χ i)).re
  have hbound (i : Fin (rank C)) : |d i| ≤ fpSimple C i := by
    have h := Dimensions.galois_character_norm_le_fpSimple C χ (unitIndex C) hχ hchar σ i
    rw [← fp_simple_galois_real C σ i] at h
    simpa [d, χ, Complex.norm_real, Real.norm_eq_abs] using h
  have hone : d (unitIndex C) = 1 := by simp [d, χ, fpSimple_unit]
  refine ⟨∑ i, (d i) ^ 2, ?_, ?_, ?_⟩
  · exact lt_of_lt_of_le zero_lt_one
      (Dimensions.global_sum_squares_one_le d ⟨unitIndex C, hone⟩)
  · exact Dimensions.target_globalDimension_le_of_simple_bounds C d hbound
  · have hglobal : (globalFPDimension C : ℂ) = ∑ i, (χ i) ^ 2 := by
      simp [globalFPDimension, χ, Complex.ofReal_sum, Complex.ofReal_pow]
    rw [hglobal, map_sum, Complex.ofReal_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [map_pow, ← fp_simple_galois_real C σ i]
    norm_cast

end PropertyF.Ground
