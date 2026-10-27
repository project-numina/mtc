module
public import PropertyF.Ground.CentreModular.RegularSupport

@[expose] public noncomputable section
open scoped BigOperators
namespace PropertyF.Ground.CentreModular
universe u v w

/-- The FP regular-element cancellation at the heart of the determinant
argument: every additive fusion-bicharacter vanishes in characteristic zero. -/
theorem regular_fusion_derivation_vanishes
    (C : BraidedFusionCategory.{v,u})
    (M : Type w) [AddCommGroup M] [Module ℝ M]
    (B : Fin (rank C) → Fin (rank C) → M)
    (hhex : ∀ i j z,
      (∑ k, (fusionCoeff C i j k : ℝ) • B k z) =
        fpSimple C j • B i z + fpSimple C i • B j z) :
    ∀ i z, B i z = 0 := by
  classical
  intro i z
  let R : M := ∑ j, fpSimple C j • B j z
  let D : ℝ := ∑ j, fpSimple C j ^ 2
  have hreg (k : Fin (rank C)) :
      (∑ j, fpSimple C j * (fusionCoeff C i j k : ℝ)) = fpSimple C i * fpSimple C k := by
    have h := regular_coeff_eigenvector C Finset.univ
      (fun _ _ => Finset.mem_univ _) (fun _ _ _ _ _ _ => Finset.mem_univ _)
      i (Finset.mem_univ _) k (Finset.mem_univ _)
    simpa only [mul_comm] using h
  have hsum : (∑ j, fpSimple C j • ∑ k, (fusionCoeff C i j k : ℝ) • B k z) =
      fpSimple C i • R := by
    simp only [Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_smul, hreg, mul_smul]
    dsimp [R]
    rw [Finset.smul_sum]
  have hsum' : (∑ j, fpSimple C j • ∑ k, (fusionCoeff C i j k : ℝ) • B k z) =
      D • B i z + fpSimple C i • R := by
    simp_rw [hhex, smul_add, smul_smul]
    rw [Finset.sum_add_distrib]
    congr 1
    · rw [← Finset.sum_smul]
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      ring
    · dsimp [R]
      simp only [Finset.smul_sum, smul_smul]
      apply Finset.sum_congr rfl
      intro j _
      congr 1
      ring
  have hzero : D • B i z = 0 := by
    have h := hsum'.symm.trans hsum
    exact add_right_cancel (h.trans (zero_add (fpSimple C i • R)).symm)
  have hpos : 0 < D := by
    change 0 < globalFPDimension C
    exact lt_of_lt_of_le zero_lt_one (one_le_globalFPDimension C)
  exact (smul_eq_zero.mp hzero).resolve_left (ne_of_gt hpos)

end PropertyF.Ground.CentreModular
