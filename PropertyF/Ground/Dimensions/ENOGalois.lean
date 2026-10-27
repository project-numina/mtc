module
public import PropertyF.Ground.Dimensions.ENOReciprocity

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
open scoped BigOperators Matrix ComplexOrder
namespace PropertyF.Ground.Dimensions
universe v u

/-- Trace reciprocity makes the Galois-conjugate dual root dimension the
signed complex conjugate of the original Galois-conjugate dimension. -/
theorem galois_rootDimension_dual_conjugate_of_trace_reciprocity
    (C : Ground.BraidedFusionCategory.{v,u})
    (hinv : ∀ i j k, (multiplicityDefect C i j k).toLinearMap *
      (multiplicityDefect C i j k).toLinearMap = 1)
    (htranspose : ∀ i j k, enoTraceMatrix C (Ground.dualIndex C i) j k =
      rootDualSign C i * enoTraceMatrix C i k j)
    (σ : ℂ ≃+* ℂ) (i : Fin (Ground.rank C)) :
    σ (rootDimension C (Ground.dualIndex C i)) = rootDualSign C i * star (σ (rootDimension C i)) := by
  classical
  let A : Matrix (Fin (Ground.rank C)) (Fin (Ground.rank C)) ℂ := enoTraceMatrix C i
  let d : Fin (Ground.rank C) → ℂ := fun j => σ (rootDimension C j)
  let ε := rootDualSign C i
  have hε : ε * ε = 1 := rootDualSign_sq C i
  have hεstar : star ε = ε := by
    rcases mul_self_eq_one_iff.mp hε with h | h <;> simp [h]
  have hfixed : ∀ a j k, σ (enoTraceMatrix C a j k) = enoTraceMatrix C a j k := by
    intro a j k
    obtain ⟨n, hn, _⟩ := multiplicityDefect_trace_integer_bound C a j k (hinv a j k)
    change σ (LinearMap.trace ℂ _ (multiplicityDefect C a j k).toLinearMap) =
      LinearMap.trace ℂ _ (multiplicityDefect C a j k).toLinearMap
    rw [hn, map_intCast]
  have hA : ∀ j k, star (A j k) = A j k := by
    intro j k
    obtain ⟨n, hn, _⟩ := multiplicityDefect_trace_integer_bound C i j k (hinv i j k)
    change star (LinearMap.trace ℂ _ (multiplicityDefect C i j k).toLinearMap) =
      LinearMap.trace ℂ _ (multiplicityDefect C i j k).toLinearMap
    rw [hn]
    simp
  have hv : d ≠ 0 := by
    intro hz
    have h0 := congrFun hz (Ground.unitIndex C)
    exact (map_ne_zero σ).2 (rootDimension_ne_zero C (Ground.unitIndex C)) h0
  have heig : ∀ a j, ∑ k, enoTraceMatrix C a j k * d k = d a * d j := by
    intro a j
    have h := congrArg σ (enoTraceMatrix_eigenvector_of_involutions C a j (hinv a j))
    simpa only [map_sum, map_mul, hfixed, d] using h
  have h : A *ᵥ d = d i • d := by
    ext j
    exact heig i j
  have ht : Aᵀ *ᵥ d = (ε * d (Ground.dualIndex C i)) • d := by
    ext j
    change (∑ k, enoTraceMatrix C i k j * d k) = (ε * d (Ground.dualIndex C i)) * d j
    have he := heig (Ground.dualIndex C i) j
    simp_rw [htranspose] at he
    calc
      _ = ε * ∑ k, ((ε * enoTraceMatrix C i k j) * d k) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _
        calc
          _ = (ε * ε) * (enoTraceMatrix C i k j * d k) := by rw [hε, one_mul]
          _ = _ := by ring
      _ = ε * (d (Ground.dualIndex C i) * d j) := by rw [he]
      _ = _ := by ring
  have hc := conjugate_of_transpose_eigenvector A hA d hv (d i) (ε * d (Ground.dualIndex C i)) h ht
  have hc' := congrArg star hc
  simp only [star_mul, star_star, hεstar] at hc'
  calc
    d (Ground.dualIndex C i) = (ε * ε) * d (Ground.dualIndex C i) := by rw [hε, one_mul]
    _ = ε * (ε * d (Ground.dualIndex C i)) := by ring
    _ = ε * star (d i) := by rw [hc']

/-- Under trace reciprocity, every Galois conjugate of an intrinsic simple
squared norm is the squared norm of the corresponding root dimension. -/
theorem galois_squaredNorm_eq_rootDimension_norm_sq_of_reciprocity
    (C : Ground.BraidedFusionCategory.{v,u})
    (hinv : ∀ i j k, (multiplicityDefect C i j k).toLinearMap *
      (multiplicityDefect C i j k).toLinearMap = 1)
    (htranspose : ∀ i j k, enoTraceMatrix C (Ground.dualIndex C i) j k =
      rootDualSign C i * enoTraceMatrix C i k j)
    (σ : ℂ ≃+* ℂ) (i : Fin (Ground.rank C)) :
    σ (Ground.squaredNorm C (Ground.simples C i)) = ((‖σ (rootDimension C i)‖ ^ 2 : ℝ) : ℂ) := by
  have hs : σ (rootDualSign C i) = rootDualSign C i := by
    rcases mul_self_eq_one_iff.mp (rootDualSign_sq C i) with h | h <;> simp [h]
  rw [squaredNorm_eq_rootDualSign_mul C i, map_mul, map_mul, hs,
    galois_rootDimension_dual_conjugate_of_trace_reciprocity C hinv htranspose σ i]
  calc
    _ = σ (rootDimension C i) * star (σ (rootDimension C i)) := by
      calc
        _ = (rootDualSign C i * rootDualSign C i) *
          (σ (rootDimension C i) * star (σ (rootDimension C i))) := by ring
        _ = _ := by rw [rootDualSign_sq, one_mul]
    _ = _ := by simpa using Complex.mul_conj' (σ (rootDimension C i))

/-- Involutivity alone makes every intrinsic simple squared norm an algebraic
integer, using the signed product and the trace-matrix eigenvector identity. -/
theorem squaredNorm_isIntegral_of_involutions
    (C : Ground.BraidedFusionCategory.{v,u})
    (hinv : ∀ i j k, (multiplicityDefect C i j k).toLinearMap *
      (multiplicityDefect C i j k).toLinearMap = 1) (i : Fin (Ground.rank C)) :
    IsIntegral ℤ (Ground.squaredNorm C (Ground.simples C i)) := by
  have hs : IsIntegral ℤ (rootDualSign C i) := by
    rcases mul_self_eq_one_iff.mp (rootDualSign_sq C i) with h | h
    · rw [h]
      exact isIntegral_one
    · rw [h]
      exact isIntegral_one.neg
  have hd (j : Fin (Ground.rank C)) : IsIntegral ℤ (rootDimension C j) :=
    rootDimension_isIntegral_of_trace_matrix C j (hinv j)
      (fun k => enoTraceMatrix_eigenvector_of_involutions C j k (hinv j k))
  rw [squaredNorm_eq_rootDualSign_mul]
  exact (hs.mul (hd i)).mul (hd (Ground.dualIndex C i))

/-- Trace reciprocity gives the ENO global lower and FP upper bounds for every
Galois conjugate, without assuming sphericality. -/
theorem globalDimension_galois_bounds_of_trace_reciprocity
    (C : Ground.BraidedFusionCategory.{v,u})
    (hinv : ∀ i j k, (multiplicityDefect C i j k).toLinearMap *
      (multiplicityDefect C i j k).toLinearMap = 1)
    (htranspose : ∀ i j k, enoTraceMatrix C (Ground.dualIndex C i) j k =
      rootDualSign C i * enoTraceMatrix C i k j) (σ : ℂ ≃+* ℂ) :
    ∃ D : ℝ, 1 ≤ D ∧ D ≤ Ground.globalFPDimension C ∧ σ (Ground.globalDimension C) = (D : ℂ) := by
  let d : Fin (Ground.rank C) → ℝ := fun i => ‖σ (rootDimension C i)‖
  have hb : ∀ i, |d i| ≤ Ground.fpSimple C i := by
    intro i
    rw [abs_of_nonneg (norm_nonneg _)]
    exact rootDimension_galois_norm_le_fp_of_trace_matrix C i (hinv i)
      (fun j => enoTraceMatrix_eigenvector_of_involutions C i j (hinv i j)) σ
  have hunit : ∃ i, d i = 1 := by
    refine ⟨Ground.unitIndex C, ?_⟩
    letI : Simple (Ground.simples C (Ground.unitIndex C)) := Ground.simples_simple C _
    letI : Simple (𝟙_ C.Obj) := Ground.IsFusionCategory.unit_simple
    obtain ⟨e⟩ := Ground.unitIndex_iso C
    have hu : Ground.squaredNorm C (Ground.simples C (Ground.unitIndex C)) = 1 := by
      rw [target_squaredNorm_iso C e, target_squaredNorm_unit]
    have h := galois_squaredNorm_eq_rootDimension_norm_sq_of_reciprocity C hinv htranspose σ (Ground.unitIndex C)
    rw [hu, map_one] at h
    have hs : d (Ground.unitIndex C) ^ 2 = 1 := by exact_mod_cast h.symm
    have hn : 0 ≤ d (Ground.unitIndex C) := norm_nonneg _
    nlinarith
  have hg : σ (Ground.globalDimension C) = ((∑ i, d i ^ 2 : ℝ) : ℂ) := by
    unfold Ground.globalDimension
    rw [map_sum, Complex.ofReal_sum]
    apply Finset.sum_congr rfl
    intro i _
    exact galois_squaredNorm_eq_rootDimension_norm_sq_of_reciprocity C hinv htranspose σ i
  exact ⟨∑ i, d i ^ 2, global_sum_squares_one_le d hunit,
    target_globalDimension_le_of_simple_bounds C d hb, hg⟩

/-- Trace reciprocity gives the simple FP-square bound for every Galois
conjugate, with strict positivity. -/
theorem squaredNorm_galois_bounds_of_trace_reciprocity
    (C : Ground.BraidedFusionCategory.{v,u})
    (hinv : ∀ i j k, (multiplicityDefect C i j k).toLinearMap *
      (multiplicityDefect C i j k).toLinearMap = 1)
    (htranspose : ∀ i j k, enoTraceMatrix C (Ground.dualIndex C i) j k =
      rootDualSign C i * enoTraceMatrix C i k j)
    (σ : ℂ ≃+* ℂ) (i : Fin (Ground.rank C)) :
    ∃ r : ℝ, 0 < r ∧ r ≤ Ground.fpSimple C i ^ 2 ∧
      σ (Ground.squaredNorm C (Ground.simples C i)) = (r : ℂ) := by
  let d := ‖σ (rootDimension C i)‖
  have hb : d ≤ Ground.fpSimple C i :=
    rootDimension_galois_norm_le_fp_of_trace_matrix C i (hinv i)
      (fun j => enoTraceMatrix_eigenvector_of_involutions C i j (hinv i j)) σ
  refine ⟨d ^ 2, ?_, ?_, galois_squaredNorm_eq_rootDimension_norm_sq_of_reciprocity C hinv htranspose σ i⟩
  · exact sq_pos_of_pos (norm_pos_iff.mpr ((map_ne_zero σ).2 (rootDimension_ne_zero C i)))
  · have hn : 0 ≤ d := norm_nonneg _
    nlinarith

/-- Involutivity of the actual multiplicity defects makes the intrinsic
categorical global dimension an algebraic integer. -/
theorem globalDimension_isIntegral_of_involutions
    (C : Ground.BraidedFusionCategory.{v,u})
    (hinv : ∀ i j k, (multiplicityDefect C i j k).toLinearMap *
      (multiplicityDefect C i j k).toLinearMap = 1) :
    IsIntegral ℤ (Ground.globalDimension C) := by
  unfold Ground.globalDimension
  apply IsIntegral.sum
  intro i _
  exact squaredNorm_isIntegral_of_involutions C hinv i

end PropertyF.Ground.Dimensions
