module
public import MTC.Center.Normalization.MugerAdjointNormalization

open MTC.Fusion MTC.Braided MTC.Center.Braid MTC.CategoryTheory.Dimensions
open MTC.Center.Induction

/-! # Positive pivotal dimensions on a fusion subring -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
open scoped BigOperators
namespace MTC.Center.Normalization
universe v u
variable (C : BraidedFusionCategory.{v,u})

/-- If a pivotal dimension character is positive on every simple of a fusion
subring, it agrees there with the ambient Frobenius–Perron character. -/
theorem pivotalDimension_eq_fp_of_positive_fusionSubring
    (A : Finset (Fin (rank C))) (hA : IsFusionSubring C A)
    (p : PivotalStructure (C := C.Obj))
    (hpositive : ∀ i ∈ A, ∃ r : ℝ, 0 < r ∧ pivotalDimension C p (simples C i) = r) :
    ∀ i ∈ A, pivotalDimension C p (simples C i) = (fpSimple C i : ℂ) := by
  classical
  let d (i : Fin (rank C)) : ℝ := (pivotalDimension C p (simples C i)).re
  let t (i : Fin (rank C)) : ℝ := d i / fpSimple C i
  obtain ⟨a, ha, hmin⟩ := Finset.exists_min_image A t ⟨unitIndex C, hA.unit⟩
  obtain ⟨r, hr, hra⟩ := hpositive a ha
  have hd : d a = r := by simp [d, hra]
  have htpos : 0 < t a := by simp only [t, hd]; exact div_pos hr (fpSimple_pos C a)
  have hda : dualIndex C a ∈ A := hA.dual a ha
  have hdual : pivotalDimension C p (simples C (dualIndex C a)) = (r : ℂ) := by
    rw [← pivotalDimension_iso p (rightDualLabelIso C a),
      pivotalDimension_simple_dual_conj p a, hra]
    simp
  have hdim : r ^ 2 = ∑ k, (fusionCoeff C a (dualIndex C a) k : ℝ) * d k := by
    have h := pivotalDimension_character C p a (dualIndex C a)
    dsimp only at h
    rw [hra, hdual] at h
    have h' := congrArg Complex.re h
    simpa [d, Complex.mul_re, pow_two] using h'
  have hfp : fpSimple C a ^ 2 =
      ∑ k, (fusionCoeff C a (dualIndex C a) k : ℝ) * fpSimple C k := by
    have h := fpSimple_mul C a (dualIndex C a)
    rw [fpSimple_dual] at h
    simpa [pow_two] using h
  have hsum : (∑ k, (fusionCoeff C a (dualIndex C a) k : ℝ) * (t a * fpSimple C k)) ≤
      ∑ k, (fusionCoeff C a (dualIndex C a) k : ℝ) * d k := by
    apply Finset.sum_le_sum
    intro k hk
    by_cases hz : fusionCoeff C a (dualIndex C a) k = 0
    · simp [hz]
    · have hkA := hA.fusion a ha (dualIndex C a) hda k (Nat.pos_of_ne_zero hz)
      have hkmin : t a * fpSimple C k ≤ d k :=
        (le_div_iff₀ (fpSimple_pos C k)).mp (hmin k hkA)
      exact mul_le_mul_of_nonneg_left hkmin (Nat.cast_nonneg _)
  have hleft : (∑ k, (fusionCoeff C a (dualIndex C a) k : ℝ) * (t a * fpSimple C k)) =
      t a * fpSimple C a ^ 2 := by
    simp_rw [mul_left_comm (fusionCoeff C a (dualIndex C a) _ : ℝ), ← Finset.mul_sum, ← hfp]
  have hratio : r = t a * fpSimple C a := by
    dsimp [t]
    rw [hd, div_mul_cancel₀ _ (ne_of_gt (fpSimple_pos C a))]
  rw [hleft, ← hdim, hratio] at hsum
  have hsq : t a * fpSimple C a ^ 2 ≤ (t a) ^ 2 * fpSimple C a ^ 2 := by
    nlinarith [hsum]
  have hone : 1 ≤ t a := by
    have hm : t a ≤ (t a) ^ 2 :=
      le_of_mul_le_mul_right hsq (sq_pos_of_pos (fpSimple_pos C a))
    nlinarith
  intro i hi
  obtain ⟨s, hs, hsi⟩ := hpositive i hi
  have hnorm := character_norm_le_fpSimple (C := C) (i₀ := unitIndex C)
    ((pivotalDimension_unitIndex C p).symm ▸ one_ne_zero)
    (pivotalDimension_character C p) i
  rw [hsi] at hnorm
  have hupper : s ≤ fpSimple C i := by simpa [Complex.norm_real, abs_of_pos hs] using hnorm
  have hti : 1 ≤ t i := hone.trans (hmin i hi)
  have hlower : fpSimple C i ≤ s := by
    have := (le_div_iff₀ (fpSimple_pos C i)).mp hti
    simpa [t, d, hsi] using this
  have heq := le_antisymm hupper hlower
  simpa [heq] using hsi

/-- The intersection of the actual transparent and ambient-neutral labels. -/
def mugerNeutralLabels : Finset (Fin (rank C)) :=
  mugerLabels C ∩ neutralDegreeLabels C

/-- Transparent ambient-neutral labels form a fusion subring. -/
theorem mugerNeutralLabels_fusionSubring : IsFusionSubring C (mugerNeutralLabels C) := by
  classical
  let M := mugerLabels_fusionSubring C
  let N := neutralDegreeLabels_fusionSubring C
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro i hi
    rcases Finset.mem_inter.mp hi with ⟨hiM, hiN⟩
    exact Finset.mem_inter.mpr ⟨M.dual i hiM, N.dual i hiN⟩
  · intro i hi j hj k hk
    rcases Finset.mem_inter.mp hi with ⟨hiM, hiN⟩
    rcases Finset.mem_inter.mp hj with ⟨hjM, hjN⟩
    exact Finset.mem_inter.mpr ⟨M.fusion i hiM j hjM k hk, N.fusion i hiN j hjN k hk⟩
  · exact Finset.mem_inter.mpr ⟨M.unit, N.unit⟩

/-- Positivity on transparent adjoint simples already forces FP-norm
saturation on every transparent simple. No pseudo-unitarity or S-matrix
invertibility assumption is needed. -/
theorem transparent_norm_saturation_of_adjoint_positivity
    (p : PivotalStructure (C := C.Obj))
    (hpositive : ∀ i, MTC.Center.Transparent (simples C i) → IsAdjointLabel C i →
      ∃ r : ℝ, 0 < r ∧ pivotalDimension C p (simples C i) = r)
    (i : Fin (rank C)) (hi : MTC.Center.Transparent (simples C i)) :
    ‖pivotalDimension C p (simples C i)‖ = fpSimple C i := by
  classical
  let A := mugerNeutralLabels C
  have hA : IsFusionSubring C A := mugerNeutralLabels_fusionSubring C
  have hpos : ∀ k ∈ A, ∃ r : ℝ, 0 < r ∧ pivotalDimension C p (simples C k) = r := by
    intro k hk
    rcases Finset.mem_inter.mp hk with ⟨hkM, hkN⟩
    have ht : MTC.Center.Transparent (simples C k) := (mem_mugerLabels C k).mp hkM
    have hneutral : fusionDegree C k = 0 := by simpa [neutralDegreeLabels] using hkN
    exact hpositive k ht ((fusionDegree_zero_iff_adjointLabel C k).mp hneutral)
  have heq := pivotalDimension_eq_fp_of_positive_fusionSubring C A hA p hpos
  have hiM : i ∈ mugerLabels C := (mem_mugerLabels C i).mpr hi
  have hdualM : dualIndex C i ∈ mugerLabels C := (mugerLabels_fusionSubring C).dual i hiM
  have hconst (k : Fin (rank C)) (hk : 0 < fusionCoeff C i (dualIndex C i) k) :
      k ∈ A := by
    apply Finset.mem_inter.mpr
    refine ⟨(mugerLabels_fusionSubring C).fusion i hiM (dualIndex C i) hdualM k hk, ?_⟩
    simp only [neutralDegreeLabels, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [fusionDegree_tensor C hk, fusionDegree_dual, add_neg_cancel]
  have hdual : pivotalDimension C p (simples C (dualIndex C i)) =
      star (pivotalDimension C p (simples C i)) := by
    rw [← pivotalDimension_iso p (rightDualLabelIso C i), pivotalDimension_simple_dual_conj]
  have hchar := pivotalDimension_character C p i (dualIndex C i)
  dsimp only at hchar
  rw [hdual] at hchar
  have hsum : (∑ k, (fusionCoeff C i (dualIndex C i) k : ℂ) *
      pivotalDimension C p (simples C k)) =
      ∑ k, (fusionCoeff C i (dualIndex C i) k : ℂ) * (fpSimple C k : ℂ) := by
    apply Finset.sum_congr rfl
    intro k hk
    by_cases hz : fusionCoeff C i (dualIndex C i) k = 0
    · simp [hz]
    · rw [heq k (hconst k (Nat.pos_of_ne_zero hz))]
  have hfp : (∑ k, (fusionCoeff C i (dualIndex C i) k : ℂ) * (fpSimple C k : ℂ)) =
      ((fpSimple C i ^ 2 : ℝ) : ℂ) := by
    have h := fpSimple_mul C i (dualIndex C i)
    rw [fpSimple_dual] at h
    exact_mod_cast h.symm.trans (by ring)
  have hsq : ‖pivotalDimension C p (simples C i)‖ ^ 2 = fpSimple C i ^ 2 := by
    have h := (Complex.mul_conj' (pivotalDimension C p (simples C i))).symm.trans
      (hchar.trans (hsum.trans hfp))
    exact_mod_cast h
  nlinarith [norm_nonneg (pivotalDimension C p (simples C i)), fpSimple_pos C i]

/-- Manuscript normalization: adjoint positivity alone gives a pivotal
structure whose dimensions equal FP dimensions on every transparent simple. -/
theorem normalize_pivotal_on_muger_of_adjoint_positivity_unconditional
    (p : PivotalStructure (C := C.Obj))
    (hpositive : ∀ i, MTC.Center.Transparent (simples C i) → IsAdjointLabel C i →
      ∃ r : ℝ, 0 < r ∧ pivotalDimension C p (simples C i) = r) :
    ∃ q : PivotalStructure (C := C.Obj), ∀ i,
      MTC.Center.Transparent (simples C i) →
      pivotalDimension C q (simples C i) = (fpSimple C i : ℂ) :=
  normalize_pivotal_on_muger_of_adjoint_positivity C p
    (transparent_norm_saturation_of_adjoint_positivity C p hpositive) hpositive

end MTC.Center.Normalization
end
