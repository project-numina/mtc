module
public import PropertyF.Ground.Fusion.TotalMatrix
public import PropertyF.Ground.Fusion.Perron

/-! Constructing the positive fusion character from the total matrix. -/

@[expose] public noncomputable section
open scoped BigOperators Matrix

namespace PropertyF.Ground

/-- The transpose convention: its rows encode the fusion equations. -/
def characterMatrix (D : BraidedFusionCategory) (i : Fin (rank D)) :
    Matrix (Fin (rank D)) (Fin (rank D)) ℝ :=
  fun j k => fusionCoeff D i j k

theorem characterMatrix_commute (D : BraidedFusionCategory) (i j : Fin (rank D)) :
    Commute (characterMatrix D i) (characterMatrix D j) := by
  classical
  apply Matrix.ext
  intro a b
  simp only [Matrix.mul_apply, characterMatrix]
  have hn : (∑ k, fusionCoeff D i a k * fusionCoeff D j k b) =
      ∑ k, fusionCoeff D j a k * fusionCoeff D i k b := by
    calc
      _ = ∑ k, fusionCoeff D j i k * fusionCoeff D k a b :=
        fusionCoeff_assoc D j i a b
      _ = ∑ k, fusionCoeff D i j k * fusionCoeff D k a b := by
        simp only [fusionCoeff_comm D j i]
      _ = _ := (fusionCoeff_assoc D i j a b).symm
  exact_mod_cast hn

theorem totalFusionMatrix_eq_sum_characterMatrix (D : BraidedFusionCategory) :
    totalFusionMatrix D = ∑ i, characterMatrix D i := by
  classical
  apply Matrix.ext
  intro j k
  simpa [totalFusionMatrix, characterMatrix, Matrix.sum_apply] using totalFusionMatrix_symmetric D j k

theorem total_commutes_characterMatrix (D : BraidedFusionCategory) (i : Fin (rank D)) :
    Commute (totalFusionMatrix D) (characterMatrix D i) := by
  classical
  rw [totalFusionMatrix_eq_sum_characterMatrix]
  change (∑ j, characterMatrix D j) * characterMatrix D i =
    characterMatrix D i * (∑ j, characterMatrix D j)
  rw [Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  exact characterMatrix_commute D j i

/-- The total matrix has a strictly positive common eigenvector for all
fusion matrices. -/
theorem exists_positive_common_eigenvector (D : BraidedFusionCategory) :
    ∃ (v : Fin (rank D) → ℝ), (∀ j, 0 < v j) ∧
      ∀ i, ∃ d : ℝ, characterMatrix D i *ᵥ v = d • v := by
  classical
  letI : Nonempty (Fin (rank D)) := ⟨unitIndex D⟩
  have hs : (totalFusionMatrix D).IsHermitian := by
    rw [Matrix.isHermitian_iff_isSymm]
    exact Matrix.IsSymm.ext (fun j k => totalFusionMatrix_symmetric D k j)
  obtain ⟨a, v, hvpos, hve⟩ := positive_symmetric_matrix_has_positive_eigenvector
    (totalFusionMatrix D) hs (totalFusionMatrix_pos D)
  refine ⟨v, hvpos, ?_⟩
  intro i
  have hcomm := total_commutes_characterMatrix D i
  have hve' : totalFusionMatrix D *ᵥ (characterMatrix D i *ᵥ v) =
      a • (characterMatrix D i *ᵥ v) := by
    rw [Matrix.mulVec_mulVec, hcomm.eq, ← Matrix.mulVec_mulVec, hve]
    rw [Matrix.mulVec_smul]
  obtain ⟨d, hd⟩ := positive_matrix_eigenspace_unique (totalFusionMatrix D)
    (totalFusionMatrix_pos D) v (characterMatrix D i *ᵥ v) hvpos a hve hve'
  exact ⟨d, hd⟩

/-- A positive normalized character exists for the actual fusion rules. -/
theorem exists_positive_character (D : BraidedFusionCategory) :
    ∃ f : Fin (rank D) → ℝ,
      (∀ i, 0 < f i) ∧ f (unitIndex D) = 1 ∧
      ∀ i j, f i * f j = ∑ k, (fusionCoeff D i j k : ℝ) * f k := by
  classical
  obtain ⟨v, hvpos, hve⟩ := exists_positive_common_eigenvector D
  let f : Fin (rank D) → ℝ := fun i => v i / v (unitIndex D)
  have hunit : v (unitIndex D) ≠ 0 := ne_of_gt (hvpos _)
  refine ⟨f, fun i => div_pos (hvpos i) (hvpos _), ?_, ?_⟩
  · simp [f, hunit]
  · intro i j
    obtain ⟨d, hd⟩ := hve i
    have hscalar : d = f i := by
      have h := congrFun hd (unitIndex D)
      simp only [Matrix.mulVec, dotProduct, characterMatrix, Pi.smul_apply, smul_eq_mul] at h
      simp only [fusionCoeff_comm D i (unitIndex D), fusionCoeff_unit] at h
      simp at h
      dsimp [f]
      exact (eq_div_iff hunit).mpr (by linarith)
    have hrow := congrFun hd j
    simp only [Matrix.mulVec, dotProduct, characterMatrix, Pi.smul_apply, smul_eq_mul] at hrow
    rw [hscalar] at hrow
    calc
      f i * f j = (∑ k, (fusionCoeff D i j k : ℝ) * v k) / v (unitIndex D) := by
        rw [hrow]
        dsimp [f]
        ring
      _ = ∑ k, (fusionCoeff D i j k : ℝ) * f k := by
        simp [f, Finset.sum_div, mul_div_assoc]

theorem character_total_eigenvector (D : BraidedFusionCategory)
    (f : Fin (rank D) → ℝ)
    (hf : ∀ i j, f i * f j = ∑ k, (fusionCoeff D i j k : ℝ) * f k) :
    totalFusionMatrix D *ᵥ f = (∑ i, f i) • f := by
  classical
  rw [totalFusionMatrix_eq_sum_characterMatrix, Matrix.sum_mulVec]
  ext j
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  change (∑ k, (fusionCoeff D i j k : ℝ) * f k) = f i * f j
  exact (hf i j).symm

/-- The positive normalized fusion character is unique. -/
theorem positive_character_unique (D : BraidedFusionCategory)
    (f g : Fin (rank D) → ℝ) (hfpos : ∀ i, 0 < f i) (hgpos : ∀ i, 0 < g i)
    (hfunit : f (unitIndex D) = 1) (hgunit : g (unitIndex D) = 1)
    (hf : ∀ i j, f i * f j = ∑ k, (fusionCoeff D i j k : ℝ) * f k)
    (hg : ∀ i j, g i * g j = ∑ k, (fusionCoeff D i j k : ℝ) * g k) : f = g := by
  classical
  letI : Nonempty (Fin (rank D)) := ⟨unitIndex D⟩
  have hfe := character_total_eigenvector D f hf
  have hge := character_total_eigenvector D g hg
  have hsym : (totalFusionMatrix D)ᵀ = totalFusionMatrix D := by
    apply Matrix.ext
    intro i j
    exact totalFusionMatrix_symmetric D j i
  have hdot : f ⬝ᵥ totalFusionMatrix D *ᵥ g = g ⬝ᵥ totalFusionMatrix D *ᵥ f := by
    simpa [hsym] using Matrix.dotProduct_transpose_mulVec (totalFusionMatrix D) f g
  rw [hfe, hge, dotProduct_smul, dotProduct_smul, dotProduct_comm g f] at hdot
  have hdotpos : 0 < f ⬝ᵥ g := by
    apply Finset.sum_pos
    · intro i _
      exact mul_pos (hfpos i) (hgpos i)
    · exact Finset.univ_nonempty
  have heq : (∑ i, f i) = ∑ i, g i := by
    have := mul_right_cancel₀ (ne_of_gt hdotpos) hdot.symm
    exact this
  rw [← heq] at hge
  obtain ⟨c, hc⟩ := positive_matrix_eigenspace_unique (totalFusionMatrix D)
    (totalFusionMatrix_pos D) f g hfpos _ hfe hge
  have hc1 : c = 1 := by
    have h := congrFun hc (unitIndex D)
    simpa [hfunit, hgunit] using h.symm
  rw [hc, hc1, one_smul]

/-- The unique positive normalized character of the fusion rules. -/
def fpCharacter (D : BraidedFusionCategory) : Fin (rank D) → ℝ :=
  Classical.choose (exists_positive_character D)

theorem fpCharacter_pos (D : BraidedFusionCategory) (i : Fin (rank D)) :
    0 < fpCharacter D i := (Classical.choose_spec (exists_positive_character D)).1 i

theorem fpCharacter_unit (D : BraidedFusionCategory) : fpCharacter D (unitIndex D) = 1 :=
  (Classical.choose_spec (exists_positive_character D)).2.1

theorem fpCharacter_mul (D : BraidedFusionCategory) (i j : Fin (rank D)) :
    fpCharacter D i * fpCharacter D j =
      ∑ k, (fusionCoeff D i j k : ℝ) * fpCharacter D k :=
  (Classical.choose_spec (exists_positive_character D)).2.2 i j

end PropertyF.Ground
