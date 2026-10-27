module
public import PropertyF.Ground.Dimensions.WeightedEigenvalue
public import PropertyF.Ground.Dimensions.MultiplicityDefect
public import PropertyF.Ground.Dimensions.NaturalTrace
public import PropertyF.Ground.Dimensions.IntrinsicNonzero

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
open scoped BigOperators Matrix
namespace PropertyF.Ground.Dimensions
universe v u

/-- The dimension of a simple object with respect to the natural double-dual
square root. -/
def rootDimension (C : Ground.BraidedFusionCategory.{v,u}) (i : Fin (Ground.rank C)) : ℂ :=
  Ground.unitScalar C (rootTrace C (𝟙 (Ground.simples C i)))

set_option backward.isDefEq.respectTransparency false in
/-- All natural-root simple dimensions are nonzero. -/
theorem rootDimension_ne_zero (C : Ground.BraidedFusionCategory.{v,u}) (i : Fin (Ground.rank C)) :
    rootDimension C i ≠ 0 := by
  letI : Simple (Ground.simples C i) := Ground.simples_simple C i
  have h := rightQuantumTrace_simple_ne_zero C (Ground.simples C i)
    ((fourthDualRootNaturalIso C).app (Ground.simples C i))
  intro hz
  apply h
  apply (groundUnitScalarEquiv C).injective
  have hz' : Ground.unitScalar C (rightQuantumTrace
      ((fourthDualRootNaturalIso C).app (Ground.simples C i))) = 0 := by
    simpa [rootDimension, rootTrace, rightTraceWith, rightQuantumTrace, tensorHom_def] using hz
  simpa only [map_zero, groundUnitScalarEquiv_apply] using hz'

/-- The matrix of traces of the actual natural-root multiplicity defects. -/
def enoTraceMatrix (C : Ground.BraidedFusionCategory.{v,u}) (i : Fin (Ground.rank C)) :
    Fin (Ground.rank C) → Fin (Ground.rank C) → ℂ := fun j k =>
  LinearMap.trace ℂ _ (multiplicityDefect C i j k).toLinearMap

/-- Once the categorical multiplicity defects are involutive and their trace
matrix has the natural-root dimension vector as an eigenvector, ENO's FP
bound follows. Both remaining identities are explicit hypotheses. -/
theorem rootDimension_norm_le_fp_of_trace_matrix
    (C : Ground.BraidedFusionCategory.{v,u}) (i : Fin (Ground.rank C))
    (hinv : ∀ j k, (multiplicityDefect C i j k).toLinearMap *
      (multiplicityDefect C i j k).toLinearMap = 1)
    (heig : ∀ j, ∑ k, enoTraceMatrix C i j k * rootDimension C k =
      rootDimension C i * rootDimension C j) :
    ‖rootDimension C i‖ ≤ Ground.fpSimple C i := by
  apply fusion_dominated_eigenvalue_bound C i (enoTraceMatrix C i) (rootDimension C)
    (rootDimension C i) (Ground.unitIndex C) (rootDimension_ne_zero C _)
  · intro j k
    obtain ⟨n, hn, hb⟩ := multiplicityDefect_trace_integer_bound C i j k (hinv j k)
    change ‖LinearMap.trace ℂ _ (multiplicityDefect C i j k).toLinearMap‖ ≤ _
    rw [hn, Complex.norm_intCast, ← Int.cast_abs]
    exact_mod_cast hb
  · exact heig

/-- Under the two remaining ENO trace-matrix identities, each natural-root
simple dimension is an algebraic integer. -/
theorem rootDimension_isIntegral_of_trace_matrix
    (C : Ground.BraidedFusionCategory.{v,u}) (i : Fin (Ground.rank C))
    (hinv : ∀ j k, (multiplicityDefect C i j k).toLinearMap *
      (multiplicityDefect C i j k).toLinearMap = 1)
    (heig : ∀ j, ∑ k, enoTraceMatrix C i j k * rootDimension C k =
      rootDimension C i * rootDimension C j) :
    IsIntegral ℤ (rootDimension C i) := by
  classical
  have hi : ∀ j k, ∃ n : ℤ, enoTraceMatrix C i j k = (n : ℂ) := by
    intro j k
    obtain ⟨n, hn, _⟩ := multiplicityDefect_trace_integer_bound C i j k (hinv j k)
    exact ⟨n, hn⟩
  choose a ha using hi
  let M : Matrix (Fin (Ground.rank C)) (Fin (Ground.rank C)) ℤ := fun j k => a j k
  let A := M.map (Int.castRingHom ℂ)
  have he : A *ᵥ rootDimension C = rootDimension C i • rootDimension C := by
    ext j
    change (∑ k, ((a j k : ℤ) : ℂ) * rootDimension C k) =
      rootDimension C i * rootDimension C j
    simpa only [← ha] using heig j
  have hzero : (Matrix.scalar _ (rootDimension C i) - A) *ᵥ rootDimension C = 0 := by
    rw [Matrix.sub_mulVec, he]
    ext j
    simp [Matrix.scalar_apply]
  have hdet : (Matrix.scalar _ (rootDimension C i) - A).det = 0 :=
    Matrix.det_eq_zero_of_mulVec_eq_zero_of_mem_nonZeroDivisors hzero
      (mem_nonZeroDivisors_of_ne_zero (rootDimension_ne_zero C (Ground.unitIndex C)))
  refine ⟨M.charpoly, M.charpoly_monic, ?_⟩
  change Polynomial.eval₂ (Int.castRingHom ℂ) (rootDimension C i) M.charpoly = 0
  rw [Polynomial.eval₂_eq_eval_map, ← Matrix.charpoly_map, Matrix.eval_charpoly]
  exact hdet

/-- The same trace-matrix hypotheses bound every Galois conjugate of a root
dimension, since the trace-matrix entries are integers. -/
theorem rootDimension_galois_norm_le_fp_of_trace_matrix
    (C : Ground.BraidedFusionCategory.{v,u}) (i : Fin (Ground.rank C))
    (hinv : ∀ j k, (multiplicityDefect C i j k).toLinearMap *
      (multiplicityDefect C i j k).toLinearMap = 1)
    (heig : ∀ j, ∑ k, enoTraceMatrix C i j k * rootDimension C k =
      rootDimension C i * rootDimension C j) (σ : ℂ ≃+* ℂ) :
    ‖σ (rootDimension C i)‖ ≤ Ground.fpSimple C i := by
  have ht : ∀ j k, σ (enoTraceMatrix C i j k) = enoTraceMatrix C i j k := by
    intro j k
    obtain ⟨n, hn, _⟩ := multiplicityDefect_trace_integer_bound C i j k (hinv j k)
    change σ (LinearMap.trace ℂ _ (multiplicityDefect C i j k).toLinearMap) =
      LinearMap.trace ℂ _ (multiplicityDefect C i j k).toLinearMap
    rw [hn, map_intCast]
  apply fusion_dominated_eigenvalue_bound C i (enoTraceMatrix C i)
    (fun j => σ (rootDimension C j)) (σ (rootDimension C i)) (Ground.unitIndex C)
    ((map_ne_zero σ).2 (rootDimension_ne_zero C _))
  · intro j k
    obtain ⟨n, hn, hb⟩ := multiplicityDefect_trace_integer_bound C i j k (hinv j k)
    change ‖LinearMap.trace ℂ _ (multiplicityDefect C i j k).toLinearMap‖ ≤ _
    rw [hn, Complex.norm_intCast, ← Int.cast_abs]
    exact_mod_cast hb
  · intro j
    simpa only [map_sum, map_mul, ht] using congrArg σ (heig j)


/-- Under ENO's real and FP-saturated eigenvector hypotheses, the actual trace
matrix entries saturate their fusion bounds with the forced signs. -/
theorem enoTraceMatrix_saturation_of_real_dimensions
    (C : Ground.BraidedFusionCategory.{v,u}) (d : Fin (Ground.rank C) → ℝ)
    (hreal : ∀ i, rootDimension C i = (d i : ℂ))
    (hd : ∀ i, |d i| = Ground.fpSimple C i)
    (hinv : ∀ i j k, (multiplicityDefect C i j k).toLinearMap *
      (multiplicityDefect C i j k).toLinearMap = 1)
    (heig : ∀ i j, ∑ k, enoTraceMatrix C i j k * rootDimension C k =
      rootDimension C i * rootDimension C j) :
    ∀ i j k, enoTraceMatrix C i j k =
      (((d i / Ground.fpSimple C i) * (d j / Ground.fpSimple C j) *
        (d k / Ground.fpSimple C k) * (Ground.fusionCoeff C i j k : ℝ) : ℝ) : ℂ) := by
  let T : Fin (Ground.rank C) → Fin (Ground.rank C) → Fin (Ground.rank C) → ℝ :=
    fun i j k => (enoTraceMatrix C i j k).re
  have hT : ∀ i j k, (T i j k : ℂ) = enoTraceMatrix C i j k := by
    intro i j k
    obtain ⟨n, hn, _⟩ := multiplicityDefect_trace_integer_bound C i j k (hinv i j k)
    change ((LinearMap.trace ℂ _ (multiplicityDefect C i j k).toLinearMap).re : ℂ) =
      LinearMap.trace ℂ _ (multiplicityDefect C i j k).toLinearMap
    rw [hn]
    simp
  have hdom : ∀ i j k, |T i j k| ≤ (Ground.fusionCoeff C i j k : ℝ) := by
    intro i j k
    obtain ⟨n, hn, hb⟩ := multiplicityDefect_trace_integer_bound C i j k (hinv i j k)
    change |(LinearMap.trace ℂ _ (multiplicityDefect C i j k).toLinearMap).re| ≤ _
    rw [hn, Complex.intCast_re, ← Int.cast_abs]
    exact_mod_cast hb
  have he : ∀ i j, ∑ k, T i j k * d k = d i * d j := by
    intro i j
    have h := congrArg Complex.re (heig i j)
    simp only [hreal, Complex.re_sum, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, sub_zero] at h
    exact h
  have hs := fusion_signed_eigenvalue_saturation C T d hd hdom he
  intro i j k
  rw [← hT i j k, hs i j k]


end PropertyF.Ground.Dimensions
