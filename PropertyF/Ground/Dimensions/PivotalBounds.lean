module
public import PropertyF.Ground.Dimensions.SphericalReal

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.Dimensions
universe v u
set_option backward.isDefEq.respectTransparency false in
/-- The intrinsic norm is the product of the pivotal dimensions of a simple and its dual. -/
theorem squaredNorm_eq_pivotal_dimension_product (C : Ground.BraidedFusionCategory.{v,u})
    (p : PivotalStructure (C := C.Obj)) (i : Fin (Ground.rank C)) :
    Ground.squaredNorm C (Ground.simples C i) = pivotalDimension C p (Ground.simples C i) *
      pivotalDimension C p (Ground.simples C (Ground.dualIndex C i)) := by
  let X := Ground.simples C i
  let : Simple X := Ground.simples_simple C i
  rw [target_squaredNorm_choice_independent C X (p.iso X), leftQuantumTrace_eq_rightDual]
  rw [← pivotal_dual p X, ← rightTrace_id, ← rightTrace_id]
  change pivotalDimension C p X * pivotalDimension C p (Xᘁ) = _
  rw [pivotalDimension_iso C p (rightDualLabelIso C i)]

/-- Each Galois-conjugate intrinsic norm is the squared norm of the corresponding conjugate pivotal dimension. -/
theorem galois_squaredNorm_eq_pivotalDimension_norm_sq (C : Ground.BraidedFusionCategory.{v,u})
    (p : PivotalStructure (C := C.Obj)) (σ : ℂ ≃+* ℂ) (i : Fin (Ground.rank C)) :
    σ (Ground.squaredNorm C (Ground.simples C i)) =
      ((‖σ (pivotalDimension C p (Ground.simples C i))‖ ^ 2 : ℝ) : ℂ) := by
  rw [squaredNorm_eq_pivotal_dimension_product C p i, map_mul, galois_pivotalDimension_dual_eq_conj]
  simpa using Complex.mul_conj' (σ (pivotalDimension C p (Ground.simples C i)))

/-- Any pivotal structure gives total positivity and the FP-square bound for intrinsic norms. -/
theorem pivotal_squaredNorm_galois_bounds (C : Ground.BraidedFusionCategory.{v,u})
    (p : PivotalStructure (C := C.Obj)) (σ : ℂ ≃+* ℂ) (i : Fin (Ground.rank C)) :
    ∃ r : ℝ, 0 < r ∧ r ≤ Ground.fpSimple C i ^ 2 ∧
      σ (Ground.squaredNorm C (Ground.simples C i)) = (r : ℂ) := by
  let d := ‖σ (pivotalDimension C p (Ground.simples C i))‖
  have hb : d ≤ Ground.fpSimple C i := galois_pivotalDimension_norm_le_fpSimple C p σ i
  refine ⟨d ^ 2, ?_, ?_, galois_squaredNorm_eq_pivotalDimension_norm_sq C p σ i⟩
  · exact sq_pos_of_pos (norm_pos_iff.mpr ((map_ne_zero σ).2 (pivotalDimension_simple_ne_zero C p i)))
  · have hn : 0 ≤ d := norm_nonneg _
    nlinarith

/-- Any pivotal structure gives the global Galois lower and FP upper bounds. -/
theorem pivotal_globalDimension_galois_bounds (C : Ground.BraidedFusionCategory.{v,u})
    (p : PivotalStructure (C := C.Obj)) (σ : ℂ ≃+* ℂ) :
    ∃ D : ℝ, 1 ≤ D ∧ D ≤ Ground.globalFPDimension C ∧ σ (Ground.globalDimension C) = (D : ℂ) := by
  let d : Fin (Ground.rank C) → ℝ := fun i => ‖σ (pivotalDimension C p (Ground.simples C i))‖
  have hb : ∀ i, |d i| ≤ Ground.fpSimple C i := by
    intro i
    rw [abs_of_nonneg (norm_nonneg _)]
    exact galois_pivotalDimension_norm_le_fpSimple C p σ i
  have hunit : ∃ i, d i = 1 := by
    refine ⟨Ground.unitIndex C, ?_⟩
    obtain ⟨e⟩ := Ground.unitIndex_iso C
    dsimp [d]
    rw [pivotalDimension_iso C p e, pivotalDimension_unit, map_one, norm_one]
  have hg : σ (Ground.globalDimension C) = ((∑ i, d i ^ 2 : ℝ) : ℂ) := by
    unfold Ground.globalDimension
    rw [map_sum, Complex.ofReal_sum]
    apply Finset.sum_congr rfl
    intro i _
    exact galois_squaredNorm_eq_pivotalDimension_norm_sq C p σ i
  exact ⟨∑ i, d i ^ 2, global_sum_squares_one_le d hunit,
    target_globalDimension_le_of_simple_bounds C d hb, hg⟩
/-- Any pivotal structure gives integrality of each simple intrinsic norm. -/
theorem pivotal_squaredNorm_isIntegral (C : Ground.BraidedFusionCategory.{v,u})
    (p : PivotalStructure (C := C.Obj)) (i : Fin (Ground.rank C)) :
    IsIntegral ℤ (Ground.squaredNorm C (Ground.simples C i)) := by
  rw [squaredNorm_eq_pivotal_dimension_product C p i]
  exact (pivotalDimension_isIntegral C p _).mul (pivotalDimension_isIntegral C p _)

/-- Any pivotal structure gives integrality of the intrinsic global dimension. -/
theorem pivotal_globalDimension_isIntegral (C : Ground.BraidedFusionCategory.{v,u})
    (p : PivotalStructure (C := C.Obj)) : IsIntegral ℤ (Ground.globalDimension C) := by
  unfold Ground.globalDimension
  apply IsIntegral.sum
  intro i _
  exact pivotal_squaredNorm_isIntegral C p i

/-- A pivotal pseudo-unitary category has the required Galois bounds on global FP dimension. -/
theorem pseudoUnitary_galois_fp_bounds_of_pivotal (C : Ground.BraidedFusionCategory.{v,u})
    (p : PivotalStructure (C := C.Obj)) (hpu : Ground.PseudoUnitary C) (σ : ℂ ≃+* ℂ) :
    ∃ D : ℝ, 0 < D ∧ D ≤ Ground.globalFPDimension C ∧
      σ (Ground.globalFPDimension C : ℂ) = (D : ℂ) := by
  obtain ⟨D, hD, hle, heq⟩ := pivotal_globalDimension_galois_bounds C p σ
  exact ⟨D, lt_of_lt_of_le (by norm_num) hD, hle, hpu ▸ heq⟩
end PropertyF.Ground.Dimensions
