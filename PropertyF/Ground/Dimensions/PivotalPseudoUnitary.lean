module
public import PropertyF.Ground.Dimensions.PivotalBounds
public import PropertyF.Ground.Dimensions.ComplexSaturation
public import PropertyF.Ground.Dimensions.PivotalTwist

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.Dimensions
universe v u
set_option backward.isDefEq.respectTransparency false in
/-- Pseudo-unitarity saturates every pivotal simple-dimension FP bound. -/
theorem pseudoUnitary_saturation_of_pivotal (C : Ground.BraidedFusionCategory.{v,u})
    (p : PivotalStructure (C := C.Obj)) (hpu : Ground.PseudoUnitary C) :
    ∀ i, ‖pivotalDimension C p (Ground.simples C i)‖ = Ground.fpSimple C i := by
  let d : Fin (Ground.rank C) → ℝ := fun i => ‖pivotalDimension C p (Ground.simples C i)‖
  have hb : ∀ i, |d i| ≤ Ground.fpSimple C i := by
    intro i
    rw [abs_of_nonneg (norm_nonneg _)]
    exact galois_pivotalDimension_norm_le_fpSimple C p (RingEquiv.refl ℂ) i
  have hg : Ground.globalDimension C = ((∑ i, d i ^ 2 : ℝ) : ℂ) := by
    unfold Ground.globalDimension
    rw [Complex.ofReal_sum]
    apply Finset.sum_congr rfl
    intro i _
    exact galois_squaredNorm_eq_pivotalDimension_norm_sq C p (RingEquiv.refl ℂ) i
  have heq : ∑ i, d i ^ 2 = Ground.globalFPDimension C := by
    apply Complex.ofReal_injective
    rw [← hg]
    exact hpu
  have hs := (global_sum_squares_eq_iff C d hb).mp heq
  intro i
  simpa [d, abs_of_nonneg (norm_nonneg _)] using hs i

set_option backward.isDefEq.respectTransparency false in
/-- Twisting any pivotal structure by its saturated phases constructs the canonical positive spherical structure. -/
theorem positive_spherical_of_pivotal_pseudoUnitary (C : Ground.BraidedFusionCategory.{v,u})
    (p : PivotalStructure (C := C.Obj)) (hpu : Ground.PseudoUnitary C) :
    ∃ q : PivotalStructure (C := C.Obj), q.IsSpherical ∧ ∀ i,
      pivotalDimension C q (Ground.simples C i) = (Ground.fpSimple C i : ℂ) := by
  let z : Fin (Ground.rank C) → ℂ := fun i => pivotalDimension C p (Ground.simples C i)
  let f := Ground.fpSimple C
  let q : Fin (Ground.rank C) → ℂ := fun i => z i / (f i : ℂ)
  let c : Fin (Ground.rank C) → ℂ := fun i => (q i)⁻¹
  have hf (i) : (f i : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt (Ground.fpSimple_pos C i))
  have hz (i) : z i ≠ 0 := pivotalDimension_simple_ne_zero C p i
  have hq (i) : q i ≠ 0 := div_ne_zero (hz i) (hf i)
  have hc (i) : c i ≠ 0 := inv_ne_zero (hq i)
  have hunit : c (Ground.unitIndex C) = 1 := by
    obtain ⟨e⟩ := Ground.unitIndex_iso C
    dsimp [c, q, z, f]
    rw [pivotalDimension_iso C p e, pivotalDimension_unit, Ground.fpSimple_unit]
    norm_num
  have hsat : ∀ i, ‖z i‖ = f i := pseudoUnitary_saturation_of_pivotal C p hpu
  have hphase := fusion_complex_eigenvalue_saturation C
    (fun i j k => (Ground.fusionCoeff C i j k : ℂ)) z hsat
    (by intro i j k; simp)
    (by intro i j; simpa [z] using (pivotalDimension_character C p i j).symm)
  have hmul : ∀ i j k, Ground.fusionCoeff C i j k ≠ 0 → c k = c i * c j := by
    intro i j k hN
    have hn : (Ground.fusionCoeff C i j k : ℂ) ≠ 0 := by exact_mod_cast hN
    have h := hphase i j k
    change (Ground.fusionCoeff C i j k : ℂ) * q k / (q i * q j) = _ at h
    have hqmul : q k = q i * q j := by
      have h' : (Ground.fusionCoeff C i j k : ℂ) * q k =
          (Ground.fusionCoeff C i j k : ℂ) * (q i * q j) := by
        exact (div_eq_iff (mul_ne_zero (hq i) (hq j))).mp h
      exact mul_left_cancel₀ hn h'
    dsimp [c]
    rw [hqmul, mul_inv_rev]
    ring
  let P := pivotalScalarTwist C p c hc hunit hmul
  have hvalue (i) : pivotalDimension C P (Ground.simples C i) = (f i : ℂ) := by
    rw [pivotalDimension_scalarTwist_simple]
    change (q i)⁻¹ * z i = (f i : ℂ)
    dsimp [q]
    field_simp [hz i, hf i]
  refine ⟨P, ?_, hvalue⟩
  apply (pivotal_spherical_iff_simple_dimensions_real C P).2
  intro i
  rw [hvalue]
  simp
/-- A pseudo-unitary pivotal category has the unique canonical positive spherical structure. -/
theorem existsUnique_positive_spherical_of_pivotal_pseudoUnitary
    (C : Ground.BraidedFusionCategory.{v,u}) (p : PivotalStructure (C := C.Obj))
    (hpu : Ground.PseudoUnitary C) :
    ∃! q : PivotalStructure (C := C.Obj), q.IsSpherical ∧
      ∀ i, pivotalDimension C q (Ground.simples C i) = (Ground.fpSimple C i : ℂ) := by
  obtain ⟨q, hq, hd⟩ := positive_spherical_of_pivotal_pseudoUnitary C p hpu
  refine ⟨q, ⟨hq, hd⟩, ?_⟩
  intro r hr
  apply pivotalStructure_unique_of_simple_dimensions C r q
  intro i
  rw [hr.2 i, hd i]
/-- In a pivotal category, pseudo-unitarity is precisely saturation of each pivotal FP bound. -/
theorem pseudoUnitary_iff_pivotal_saturation (C : Ground.BraidedFusionCategory.{v,u})
    (p : PivotalStructure (C := C.Obj)) :
    Ground.PseudoUnitary C ↔ ∀ i, ‖pivotalDimension C p (Ground.simples C i)‖ = Ground.fpSimple C i := by
  constructor
  · exact pseudoUnitary_saturation_of_pivotal C p
  · intro h
    unfold Ground.PseudoUnitary Ground.globalDimension Ground.globalFPDimension
    rw [Complex.ofReal_sum]
    apply Finset.sum_congr rfl
    intro i _
    have hnorm := galois_squaredNorm_eq_pivotalDimension_norm_sq C p (RingEquiv.refl ℂ) i
    simpa only [RingEquiv.refl_apply, h i] using hnorm

/-- Pseudo-unitarity is equivalent to saturation of every intrinsic simple-norm bound. -/
theorem pseudoUnitary_iff_squaredNorm_saturation_of_pivotal (C : Ground.BraidedFusionCategory.{v,u})
    (p : PivotalStructure (C := C.Obj)) :
    Ground.PseudoUnitary C ↔ ∀ i, Ground.squaredNorm C (Ground.simples C i) =
      ((Ground.fpSimple C i ^ 2 : ℝ) : ℂ) := by
  constructor
  · intro h i
    have hn := galois_squaredNorm_eq_pivotalDimension_norm_sq C p (RingEquiv.refl ℂ) i
    simpa only [RingEquiv.refl_apply, pseudoUnitary_saturation_of_pivotal C p h i] using hn
  · intro h
    unfold Ground.PseudoUnitary Ground.globalDimension Ground.globalFPDimension
    rw [Complex.ofReal_sum]
    exact Finset.sum_congr rfl (fun i _ => h i)
end PropertyF.Ground.Dimensions
