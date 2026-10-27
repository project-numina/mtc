module
public import PropertyF.Ground.CentreModular.VafaDetTensor

@[expose] public noncomputable section
open scoped BigOperators
namespace PropertyF.Ground.CentreModular
universe v u

/-- The FP-weighted twist-balance relation forces all twist scalars to have
finite order. This is a numerical consequence; the categorical balance
relation is not assumed proved here. -/
theorem finite_order_of_fp_twist_balance (C : BraidedFusionCategory.{v,u})
    (t : Fin (rank C) → ℂˣ)
    (hbalance : ∀ i j,
      (∑ k, (fusionCoeff C i j k : ℝ) • (fpSimple C k • vafaUnitClass (t k))) =
        (fpSimple C i * fpSimple C j) • (vafaUnitClass (t i) + vafaUnitClass (t j))) :
    ∀ i, IsOfFinOrder (t i) := by
  let B : Fin (rank C) → Fin (rank C) → vafaUnitSpace :=
    fun i _ => fpSimple C i • vafaUnitClass (t i)
  have hhex : ∀ i j z, (∑ k, (fusionCoeff C i j k : ℝ) • B k z) =
      fpSimple C j • B i z + fpSimple C i • B j z := by
    intro i j z
    dsimp [B]
    rw [hbalance]
    simp only [smul_add, smul_smul]
    rw [mul_comm (fpSimple C j) (fpSimple C i)]
  have hzero := regular_fusion_derivation_vanishes C vafaUnitSpace B hhex
  intro i
  have hi := hzero i (unitIndex C)
  change fpSimple C i • vafaUnitClass (t i) = 0 at hi
  have hc := (smul_eq_zero.mp hi).resolve_left (ne_of_gt (fpSimple_pos C i))
  exact (vafaUnitClass_eq_zero_iff _).mp hc

end PropertyF.Ground.CentreModular
