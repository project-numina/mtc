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
  let χ (i : Fin (rank C)) := pivotalDimension C p (simples C i)
  let T := ∑ i, χ i * regularVector C A i
  have hT : T ≠ 0 := by
    apply Complex.ne_zero_of_re_pos
    dsimp only [T]
    rw [Complex.re_sum]
    refine Finset.sum_pos' ?_ ⟨unitIndex C, Finset.mem_univ _, ?_⟩
    · intro i _
      by_cases hi : i ∈ A
      · obtain ⟨r, hr, hri⟩ := hpositive i hi
        simpa [χ, regularVector, hi, hri] using
          mul_nonneg (le_of_lt hr) (le_of_lt (fpSimple_pos C i))
      · simp [regularVector, hi]
    · simp [χ, regularVector, hA.unit, pivotalDimension_unitIndex, fpSimple_pos C]
  intro a ha
  have heq := sum_mul_eigenvalue (fun i k ↦ (fusionCoeff C a i k : ℂ)) χ
    (regularVector C A) (fun i ↦ pivotalDimension_character C p a i)
    (regular_vector_fusion_eigenvector hA.toIsDualFusionClosed (a := ⟨a, ha⟩))
  exact mul_right_cancel₀ hT heq

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

/-- If pivotal dimensions agree with FP dimensions on the simple constituents
of a simple tensored with its dual, that simple has saturated pivotal norm. -/
theorem pivotalDimension_norm_eq_fp_of_dual_tensor_constituents
    (p : PivotalStructure (C := C.Obj)) (i : Fin (rank C))
    (hconst : ∀ k, 0 < fusionCoeff C i (dualIndex C i) k →
      pivotalDimension C p (simples C k) = (fpSimple C k : ℂ)) :
    ‖pivotalDimension C p (simples C i)‖ = fpSimple C i := by
  classical
  have hdual : pivotalDimension C p (simples C (dualIndex C i)) =
      star (pivotalDimension C p (simples C i)) := simpleDimension_dual_eq_star i
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
    · rw [hconst k (Nat.pos_of_ne_zero hz)]
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
    simpa [neutralDegreeLabels] using adjointSeed_neutral C ⟨i, hk⟩
  apply pivotalDimension_norm_eq_fp_of_dual_tensor_constituents C p i
  intro k hk
  exact heq k (hconst k hk)

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
