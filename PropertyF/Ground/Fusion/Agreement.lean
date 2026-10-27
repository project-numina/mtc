module
public import PropertyF.Ground.Fusion.Character
public import PropertyF.Ground.Fusion.SpectralBound
public import PropertyF.Ground.Dimensions.CharacterBound
public import Mathlib.LinearAlgebra.Eigenspace.Matrix

/-! Agreement of the positive character with the target's spectral radius. -/

@[expose] public noncomputable section
open scoped BigOperators Matrix Matrix.Norms.Operator

namespace PropertyF.Ground

theorem fpCharacter_le_fpSimple (D : BraidedFusionCategory) (i : Fin (rank D)) :
    fpCharacter D i ≤ fpSimple D i := by
  let χ : Fin (rank D) → ℂ := fun j => fpCharacter D j
  have hχ : χ (unitIndex D) ≠ 0 := by simp [χ, fpCharacter_unit]
  have hchar : ∀ j k, χ j * χ k = ∑ l, (fusionCoeff D j k l : ℂ) * χ l := by
    intro j k
    dsimp [χ]
    exact_mod_cast fpCharacter_mul D j k
  have h := Dimensions.character_norm_le_fpSimple D χ (unitIndex D) hχ hchar i
  simpa [χ, Complex.norm_real, abs_of_pos (fpCharacter_pos D i)] using h

theorem fpSimple_le_fpCharacter (D : BraidedFusionCategory) (i : Fin (rank D)) :
    fpSimple D i ≤ fpCharacter D i := by
  classical
  letI : Nonempty (Fin (rank D)) := ⟨unitIndex D⟩
  let A := characterMatrix D i
  let B := A.map Complex.ofRealHom
  have hB : B = (fusionMatrix D i)ᵀ := by
    ext j k
    change (((fusionCoeff D i j k : ℝ) : ℂ)) = _
    simp [fusionMatrix, fusionCoeff]
  have hwe : A *ᵥ fpCharacter D = fpCharacter D i • fpCharacter D := by
    ext j
    change (∑ k, (fusionCoeff D i j k : ℝ) * fpCharacter D k) = _
    exact (fpCharacter_mul D i j).symm
  obtain ⟨z, hz, hzmax⟩ := spectrum.exists_nnnorm_eq_spectralRadius B
  have hz' : z ∈ spectrum ℂ B.toLin' := by simpa using hz
  obtain ⟨v, hv⟩ := (Module.End.hasEigenvalue_iff_mem_spectrum.mpr hz').exists_hasEigenvector
  have hve : A.map Complex.ofRealHom *ᵥ v = z • v := by
    simpa [B, Matrix.toLin'_apply] using hv.apply_eq_smul
  have hbound := complex_eigenvalue_le_positive_eigenvalue A
    (fun j k => Nat.cast_nonneg _) (fpCharacter D) (fpCharacter_pos D)
    (fpCharacter D i) hwe z v hv.2 hve
  have hrad : fpSimple D i = ‖z‖ := by
    unfold fpSimple
    rw [← Matrix.spectralRadius_transpose (fusionMatrix D i), ← hB, ← hzmax]
    simp
  rw [hrad]
  exact hbound

/-- The target spectral-radius FP dimension is the unique positive character. -/
theorem fpSimple_eq_fpCharacter (D : BraidedFusionCategory) (i : Fin (rank D)) :
    fpSimple D i = fpCharacter D i :=
  le_antisymm (fpSimple_le_fpCharacter D i) (fpCharacter_le_fpSimple D i)

theorem fpSimple_pos (D : BraidedFusionCategory) (i : Fin (rank D)) :
    0 < fpSimple D i := by rw [fpSimple_eq_fpCharacter]; exact fpCharacter_pos D i

theorem fpSimple_mul (D : BraidedFusionCategory) (i j : Fin (rank D)) :
    fpSimple D i * fpSimple D j =
      ∑ k, (fusionCoeff D i j k : ℝ) * fpSimple D k := by
  simp only [fpSimple_eq_fpCharacter, fpCharacter_mul]

/-- The fusion matrix of a dual is the transpose of the original one. -/
theorem fusionMatrix_dual (D : BraidedFusionCategory) (i : Fin (rank D)) :
    fusionMatrix D (dualIndex D i) = (fusionMatrix D i)ᵀ := by
  ext j k
  change (fusionCoeff D (dualIndex D i) k j : ℂ) = (fusionCoeff D i j k : ℂ)
  rw [fusionCoeff_comm D (dualIndex D i) k, fusionCoeff_reciprocity_labels,
    dualIndex_involutive, fusionCoeff_comm D j i]

/-- Dual simple objects have the same FP dimension. -/
theorem fpSimple_dual (D : BraidedFusionCategory) (i : Fin (rank D)) :
    fpSimple D (dualIndex D i) = fpSimple D i := by
  simp [fpSimple, fusionMatrix_dual, Matrix.spectralRadius_transpose]

theorem fusionCoeff_dual_unit (D : BraidedFusionCategory) (i : Fin (rank D)) :
    fusionCoeff D i (dualIndex D i) (unitIndex D) = 1 := by
  rw [fusionCoeff_comm D i (dualIndex D i), fusionCoeff_reciprocity_labels,
    fusionCoeff_unit]
  simp

/-- Every simple has FP dimension at least one. -/
theorem one_le_fpSimple (D : BraidedFusionCategory) (i : Fin (rank D)) :
    1 ≤ fpSimple D i := by
  classical
  have hsum : 1 ≤ ∑ k, (fusionCoeff D i (dualIndex D i) k : ℝ) * fpSimple D k := by
    have h := Finset.single_le_sum
      (f := fun k => (fusionCoeff D i (dualIndex D i) k : ℝ) * fpSimple D k)
      (fun k _ => mul_nonneg (Nat.cast_nonneg _) (fpSimple_pos D k).le)
      (Finset.mem_univ (unitIndex D))
    simpa [fusionCoeff_dual_unit, fpSimple_unit] using h
  rw [← fpSimple_mul, fpSimple_dual] at hsum
  nlinarith [fpSimple_pos D i]

end PropertyF.Ground
