module
public import PropertyF.Ground.Dimensions.PseudoUnitary
public import PropertyF.Ground.Integrate.CharacterReality
public import PropertyF.Ground.Modular.DimensionNonzero
open scoped BigOperators

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.Dimensions

/-- Simple pivotal dimensions are nonzero, by rigidity, semisimplicity and Schur. -/
theorem pivotalDimension_simple_ne_zero (C : Ground.BraidedFusionCategory)
    (p : PivotalStructure (C := C.Obj)) (i : Fin (Ground.rank C)) :
    pivotalDimension C p (Ground.simples C i) ≠ 0 := by
  have h := Ground.Modular.simpleDimension_ne_zero C p i
  simpa [Ground.Modular.simpleDimension, pivotalDimension, Ground.unitScalar_eq_equiv] using h

/-- Simple intrinsic norms are nonzero whenever a spherical structure exists. -/
theorem spherical_squaredNorm_ne_zero (C : Ground.BraidedFusionCategory)
    (p : PivotalStructure (C := C.Obj)) (hp : p.IsSpherical)
    (i : Fin (Ground.rank C)) : Ground.squaredNorm C (Ground.simples C i) ≠ 0 := by
  let : Simple (Ground.simples C i) := Ground.simples_simple C i
  rw [target_squaredNorm_eq_dimension_sq C p hp]
  have h := pivotalDimension_simple_ne_zero C p i
  simp only [pivotalDimension, rightTrace_id] at h
  exact pow_ne_zero 2 h

/-- Every Galois conjugate of a self-dual pivotal dimension is real. The
categorical equality on dual labels is an explicit remaining input. -/
theorem galois_pivotalDimension_real_of_dual (C : Ground.BraidedFusionCategory)
    (p : PivotalStructure (C := C.Obj))
    (hdual : ∀ i, pivotalDimension C p (Ground.simples C (Ground.dualIndex C i)) =
      pivotalDimension C p (Ground.simples C i)) (σ : ℂ ≃+* ℂ) (i : Fin (Ground.rank C)) :
    ((σ (pivotalDimension C p (Ground.simples C i))).re : ℂ) =
      σ (pivotalDimension C p (Ground.simples C i)) := by
  apply Complex.conj_eq_iff_re.mp
  apply Ground.selfDual_character_galois_real C
    (fun j => pivotalDimension C p (Ground.simples C j)) (Ground.unitIndex C)
  · obtain ⟨e⟩ := Ground.unitIndex_iso C
    rw [pivotalDimension_iso C p e, pivotalDimension_unit]
    exact one_ne_zero
  · exact pivotalDimension_character C p
  · exact hdual

/-- If the pivotal simple dimensions are dual invariant, every field conjugate
of a spherical simple squared norm is strictly positive and real. -/
theorem spherical_squaredNorm_totallyPositive_of_dual (C : Ground.BraidedFusionCategory)
    (p : PivotalStructure (C := C.Obj)) (hp : p.IsSpherical)
    (hdual : ∀ i, pivotalDimension C p (Ground.simples C (Ground.dualIndex C i)) =
      pivotalDimension C p (Ground.simples C i)) (σ : ℂ ≃+* ℂ) (i : Fin (Ground.rank C)) :
    ∃ r : ℝ, 0 < r ∧ σ (Ground.squaredNorm C (Ground.simples C i)) = (r : ℂ) := by
  let : Simple (Ground.simples C i) := Ground.simples_simple C i
  let z := σ (pivotalDimension C p (Ground.simples C i))
  have hz : (z.re : ℂ) = z := galois_pivotalDimension_real_of_dual C p hdual σ i
  have hn : z ≠ 0 := (map_ne_zero σ).2 (pivotalDimension_simple_ne_zero C p i)
  have hre : z.re ≠ 0 := by
    intro he
    apply hn
    rw [← hz, he]
    simp
  refine ⟨z.re ^ 2, sq_pos_of_ne_zero hre, ?_⟩
  rw [target_squaredNorm_eq_dimension_sq C p hp, ← rightTrace_id]
  change σ (pivotalDimension C p (Ground.simples C i) ^ 2) = ((z.re ^ 2 : ℝ) : ℂ)
  rw [map_pow]
  change z ^ 2 = ((z.re ^ 2 : ℝ) : ℂ)
  rw [Complex.ofReal_pow, hz]

/-- Dual invariance of spherical dimensions implies that every Galois
conjugate of the global dimension is real, at least one, and at most the
fusion category's global FP dimension. -/
theorem spherical_globalDimension_galois_bounds_of_dual (C : Ground.BraidedFusionCategory)
    (p : PivotalStructure (C := C.Obj)) (hp : p.IsSpherical)
    (hdual : ∀ i, pivotalDimension C p (Ground.simples C (Ground.dualIndex C i)) =
      pivotalDimension C p (Ground.simples C i)) (σ : ℂ ≃+* ℂ) :
    ∃ D : ℝ, 1 ≤ D ∧ D ≤ Ground.globalFPDimension C ∧ σ (Ground.globalDimension C) = (D : ℂ) := by
  let d : Fin (Ground.rank C) → ℝ := fun i => (σ (pivotalDimension C p (Ground.simples C i))).re
  have hreal : ∀ i, (d i : ℂ) = σ (pivotalDimension C p (Ground.simples C i)) :=
    fun i => galois_pivotalDimension_real_of_dual C p hdual σ i
  have hbound : ∀ i, |d i| ≤ Ground.fpSimple C i := by
    intro i
    have h := galois_pivotalDimension_norm_le_fpSimple C p σ i
    rw [← hreal i, Complex.norm_real] at h
    exact h
  have hunit : ∃ i, d i = 1 := by
    refine ⟨Ground.unitIndex C, ?_⟩
    obtain ⟨e⟩ := Ground.unitIndex_iso C
    apply Complex.ofReal_injective
    rw [hreal, pivotalDimension_iso C p e, pivotalDimension_unit, map_one]
    norm_num
  have hglobal : σ (Ground.globalDimension C) = ((∑ i, (d i) ^ 2 : ℝ) : ℂ) := by
    rw [target_globalDimension_eq_sum_squares C p hp, map_sum]
    simp only [map_pow, ← rightTrace_id, Complex.ofReal_pow, Complex.ofReal_sum]
    apply Finset.sum_congr rfl
    intro i _
    change σ (pivotalDimension C p (Ground.simples C i)) ^ 2 = (d i : ℂ) ^ 2
    rw [hreal]
  exact ⟨∑ i, (d i) ^ 2, global_sum_squares_one_le d hunit,
    target_globalDimension_le_of_simple_bounds C d hbound, hglobal⟩

/-- For a pseudo-unitary category, every Galois conjugate of the global FP
dimension is real, positive and at most the original global FP dimension,
provided its spherical simple dimensions are dual invariant. -/
theorem pseudoUnitary_galois_fp_bounds_of_dual (C : Ground.BraidedFusionCategory)
    (p : PivotalStructure (C := C.Obj)) (hp : p.IsSpherical)
    (hdual : ∀ i, pivotalDimension C p (Ground.simples C (Ground.dualIndex C i)) =
      pivotalDimension C p (Ground.simples C i)) (hpu : Ground.PseudoUnitary C)
    (σ : ℂ ≃+* ℂ) :
    ∃ D : ℝ, 0 < D ∧ D ≤ Ground.globalFPDimension C ∧
      σ (Ground.globalFPDimension C : ℂ) = (D : ℂ) := by
  obtain ⟨D, hD, hle, heq⟩ := spherical_globalDimension_galois_bounds_of_dual C p hp hdual σ
  exact ⟨D, lt_of_lt_of_le (by norm_num) hD, hle, hpu ▸ heq⟩

end PropertyF.Ground.Dimensions
