module
public import PropertyF.Ground.Dimensions.TensorExtension
public import PropertyF.Ground.Dimensions.SphericalCriterion

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
open scoped BigOperators
namespace PropertyF.Ground.Dimensions
universe v u

/-- A pivotal structure whose simple dimensions and intrinsic norms are the
FP values is spherical. -/
theorem spherical_of_fp_dimensions_and_squaredNorms (C : Ground.BraidedFusionCategory.{v,u})
    (p : PivotalStructure (C := C.Obj))
    (hdim : ∀ i, pivotalDimension C p (Ground.simples C i) = (Ground.fpSimple C i : ℂ))
    (hnorm : ∀ i, Ground.squaredNorm C (Ground.simples C i) =
      ((Ground.fpSimple C i ^ 2 : ℝ) : ℂ)) : p.IsSpherical := by
  apply (isSpherical_iff_simple_dimensions C p).2
  intro i
  let X := Ground.simples C i
  letI : Simple X := Ground.simples_simple C i
  have hh := target_squaredNorm_choice_independent C X (p.iso X)
  rw [← rightTrace_id, ← leftTrace_id] at hh
  have hr : Ground.unitScalar C (p.rightTrace (𝟙 X)) = (Ground.fpSimple C i : ℂ) := hdim i
  rw [hr, hnorm i, Complex.ofReal_pow] at hh
  have hf : (Ground.fpSimple C i : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt (Ground.fpSimple_pos C i)
  have hl : Ground.unitScalar C (p.leftTrace (𝟙 X)) = (Ground.fpSimple C i : ℂ) := by
    apply mul_left_cancel₀ hf
    simpa [pow_two] using hh.symm
  apply (groundUnitScalarEquiv C).injective
  simpa only [groundUnitScalarEquiv_apply] using hl.trans hr.symm

/-- ENO's trace-matrix bound and the root-norm identity turn global
pseudo-unitarity into pointwise FP saturation. -/
theorem eno_root_norm_saturation_of_pseudoUnitary
    (C : Ground.BraidedFusionCategory.{v,u})
    (hinv : ∀ i j k, (multiplicityDefect C i j k).toLinearMap *
      (multiplicityDefect C i j k).toLinearMap = 1)
    (heig : ∀ i j, ∑ k, enoTraceMatrix C i j k * rootDimension C k =
      rootDimension C i * rootDimension C j)
    (hnorm : ∀ i, Ground.squaredNorm C (Ground.simples C i) =
      ((‖rootDimension C i‖ ^ 2 : ℝ) : ℂ)) (hpu : Ground.PseudoUnitary C) :
    ∀ i, ‖rootDimension C i‖ = Ground.fpSimple C i := by
  let d : Fin (Ground.rank C) → ℝ := fun i => ‖rootDimension C i‖
  have hb : ∀ i, |d i| ≤ Ground.fpSimple C i := by
    intro i
    rw [abs_of_nonneg (norm_nonneg _)]
    exact rootDimension_norm_le_fp_of_trace_matrix C i (hinv i) (heig i)
  have hg : (∑ i, d i ^ 2) = Ground.globalFPDimension C := by
    have h := hpu
    change Ground.globalDimension C = (Ground.globalFPDimension C : ℂ) at h
    unfold Ground.globalDimension at h
    simp only [hnorm, ← Complex.ofReal_sum] at h
    exact Complex.ofReal_injective h
  have h := (global_sum_squares_eq_iff C d hb).1 hg
  intro i
  simpa [d, abs_of_nonneg (norm_nonneg _)] using h i

end PropertyF.Ground.Dimensions
