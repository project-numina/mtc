module
public import PropertyF.Ground.Dimensions.CharacterBound
public import PropertyF.Ground.Fusion.Agreement

@[expose] public noncomputable section
open scoped BigOperators
namespace PropertyF.Ground.Dimensions

/-- A matrix dominated entrywise by a nonnegative matrix cannot have an
eigenvalue larger than the latter's positive eigenvalue. -/
theorem weighted_eigenvalue_bound {ι : Type*} [Fintype ι] (N : ι → ι → ℝ)
    (T : ι → ι → ℂ) (f : ι → ℝ) (F : ℝ) (v : ι → ℂ) (z : ℂ)
    (i₀ : ι) (hv : v i₀ ≠ 0) (hf : ∀ i, 0 < f i)
    (hN : ∀ i j, 0 ≤ N i j) (hdom : ∀ i j, ‖T i j‖ ≤ N i j)
    (hfp : ∀ i, ∑ j, N i j * f j = F * f i)
    (heig : ∀ i, ∑ j, T i j * v j = z * v i) :
    ‖z‖ ≤ F := by
  classical
  obtain ⟨i, _, hmax⟩ := Finset.exists_max_image Finset.univ
    (fun j => ‖v j‖ / f j) ⟨i₀, Finset.mem_univ _⟩
  let r := ‖v i‖ / f i
  have hr0 : 0 ≤ r := div_nonneg (norm_nonneg _) (le_of_lt (hf i))
  have hvi : 0 < ‖v i‖ := by
    have h0 : 0 < ‖v i₀‖ / f i₀ := div_pos (norm_pos_iff.mpr hv) (hf i₀)
    have hm : ‖v i₀‖ / f i₀ ≤ r := hmax i₀ (Finset.mem_univ _)
    have hr : 0 < r := lt_of_lt_of_le h0 hm
    exact (div_pos_iff_of_pos_right (hf i)).1 hr
  have hvbound (j : ι) : ‖v j‖ ≤ r * f j := by
    apply (div_le_iff₀ (hf j)).1
    exact hmax j (Finset.mem_univ _)
  have hbound : ‖z‖ * ‖v i‖ ≤ F * ‖v i‖ := by
    calc
      _ = ‖∑ j, T i j * v j‖ := by rw [heig i, norm_mul]
      _ ≤ ∑ j, ‖T i j * v j‖ := by simpa using norm_sum_le Finset.univ (fun j => T i j * v j)
      _ ≤ ∑ j, N i j * (r * f j) := by
        apply Finset.sum_le_sum
        intro j _
        rw [norm_mul]
        exact mul_le_mul (hdom i j) (hvbound j) (norm_nonneg _) (hN i j)
      _ = r * (∑ j, N i j * f j) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = F * ‖v i‖ := by
        rw [hfp i]
        dsimp [r]
        field_simp [ne_of_gt (hf i)]
  exact le_of_mul_le_mul_right hbound hvi

/-- ENO's trace-matrix eigenvalues are bounded by the FP dimension whenever
their entries are dominated by fusion multiplicities. -/
theorem fusion_dominated_eigenvalue_bound (C : Ground.BraidedFusionCategory)
    (i : Fin (Ground.rank C)) (T : Fin (Ground.rank C) → Fin (Ground.rank C) → ℂ)
    (v : Fin (Ground.rank C) → ℂ) (z : ℂ) (i₀ : Fin (Ground.rank C))
    (hv : v i₀ ≠ 0) (hdom : ∀ j k, ‖T j k‖ ≤ Ground.fusionCoeff C i j k)
    (heig : ∀ j, ∑ k, T j k * v k = z * v j) : ‖z‖ ≤ Ground.fpSimple C i := by
  apply weighted_eigenvalue_bound (fun j k => Ground.fusionCoeff C i j k) T
    (Ground.fpSimple C) (Ground.fpSimple C i) v z i₀ hv (Ground.fpSimple_pos C)
  · intro j k
    exact Nat.cast_nonneg _
  · exact hdom
  · intro j
    exact (Ground.fpSimple_mul C i j).symm
  · exact heig

end PropertyF.Ground.Dimensions
