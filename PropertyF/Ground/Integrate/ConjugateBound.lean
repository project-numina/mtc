module
public import PropertyF.Ground.Integrate.CharacterReality
public import PropertyF.Ground.Dimensions.DimensionCharacter
public import PropertyF.Ground.Dimensions.GlobalInequality

/-! Real conjugate bounds from an actual self-dual spherical character. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
open scoped BigOperators
namespace PropertyF.Ground
universe v u

/-- A spherical pivotal structure whose simple dimensions are dual-invariant
provides all positive real conjugate bounds needed in the target reduction.
Existence of such a structure remains a categorical obligation. -/
theorem positive_bounded_conjugates_of_spherical (C : BraidedFusionCategory.{v,u})
    (hPU : PseudoUnitary C) (p : Dimensions.PivotalStructure (C := C.Obj))
    (hp : p.IsSpherical)
    (hdual : ∀ i, Dimensions.pivotalDimension C p (simples C (dualIndex C i)) =
      Dimensions.pivotalDimension C p (simples C i))
    (σ : ℂ ≃+* ℂ) : ∃ a : ℝ, 0 < a ∧ a ≤ globalFPDimension C ∧
      σ (globalFPDimension C : ℂ) = (a : ℂ) := by
  let χ : Fin (rank C) → ℂ := fun i => Dimensions.pivotalDimension C p (simples C i)
  have hunit : χ (unitIndex C) = 1 := by
    obtain ⟨e⟩ := unitIndex_iso C
    dsimp [χ]
    rw [Dimensions.pivotalDimension_iso C p e, Dimensions.pivotalDimension_unit]
  have hchar : ∀ i j, χ i * χ j = ∑ k, (fusionCoeff C i j k : ℂ) * χ k :=
    Dimensions.pivotalDimension_character C p
  have hreal (i : Fin (rank C)) : (((σ (χ i)).re : ℝ) : ℂ) = σ (χ i) := by
    apply Complex.conj_eq_iff_re.mp
    simpa only [← Complex.star_def] using
      selfDual_character_galois_real C χ (unitIndex C) (by rw [hunit]; exact one_ne_zero)
        hchar hdual σ i
  let d : Fin (rank C) → ℝ := fun i => (σ (χ i)).re
  have hbound (i : Fin (rank C)) : |d i| ≤ fpSimple C i := by
    have h := Dimensions.galois_pivotalDimension_norm_le_fpSimple C p σ i
    change ‖σ (χ i)‖ ≤ fpSimple C i at h
    rw [← hreal i] at h
    simpa [d, Complex.norm_real, Real.norm_eq_abs] using h
  have hone : d (unitIndex C) = 1 := by simp [d, hunit]
  refine ⟨∑ i, (d i) ^ 2, ?_, ?_, ?_⟩
  · exact lt_of_lt_of_le zero_lt_one
      (Dimensions.global_sum_squares_one_le d ⟨unitIndex C, hone⟩)
  · exact Dimensions.target_globalDimension_le_of_simple_bounds C d hbound
  · have hglobal : (globalFPDimension C : ℂ) = ∑ i, (χ i) ^ 2 := by
      rw [← hPU, Dimensions.target_globalDimension_eq_sum_squares C p hp]
      simp [χ, Dimensions.pivotalDimension, Dimensions.rightTrace_id]
    rw [hglobal, map_sum, Complex.ofReal_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [map_pow, ← hreal i]
    norm_cast

end PropertyF.Ground
