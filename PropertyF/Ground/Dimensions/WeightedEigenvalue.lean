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

/-- If a signed weighted sum reaches its upper bound, every positive-weight
summand reaches the corresponding pointwise bound. -/
theorem weighted_sign_saturation {ι : Type*} [Fintype ι]
    (N T f s : ι → ℝ) (t : ℝ)
    (hf : ∀ k, 0 < f k) (hs : ∀ k, s k * s k = 1) (ht : t * t = 1)
    (hdom : ∀ k, |T k| ≤ N k)
    (heq : ∑ k, T k * s k * f k = t * ∑ k, N k * f k) :
    ∀ k, T k = t * s k * N k := by
  classical
  have hsign (k : ι) : t * s k = 1 ∨ t * s k = -1 := by
    have hsq : (t * s k) * (t * s k) = 1 := by
      rw [show (t * s k) * (t * s k) = (t * t) * (s k * s k) by ring, ht, hs k]
      norm_num
    exact mul_self_eq_one_iff.mp hsq
  have hn (k : ι) : 0 ≤ (N k - t * s k * T k) * f k := by
    apply mul_nonneg _ (le_of_lt (hf k))
    have h := (abs_le.mp (hdom k))
    rcases hsign k with hsgn | hsgn <;> rw [hsgn] <;> nlinarith
  have hsum : ∑ k, (N k - t * s k * T k) * f k = 0 := by
    calc
      _ = (∑ k, N k * f k) - t * (∑ k, T k * s k * f k) := by
        simp only [sub_mul, Finset.sum_sub_distrib, Finset.mul_sum]
        congr 1
        apply Finset.sum_congr rfl
        intro k _
        ring
      _ = 0 := by rw [heq, ← mul_assoc, ht, one_mul, sub_self]
  intro k
  have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hn j)).1 hsum k (Finset.mem_univ k)
  have hzero : N k - t * s k * T k = 0 := (mul_eq_zero.mp hz).resolve_right (ne_of_gt (hf k))
  rcases hsign k with hsgn | hsgn <;> rw [hsgn] at hzero ⊢ <;> nlinarith

/-- If a real signed eigenvector saturates all FP bounds, every entry of a
fusion-dominated trace matrix saturates its own bound with the forced sign. -/
theorem fusion_signed_eigenvalue_saturation (C : Ground.BraidedFusionCategory)
    (T : Fin (Ground.rank C) → Fin (Ground.rank C) → Fin (Ground.rank C) → ℝ)
    (d : Fin (Ground.rank C) → ℝ)
    (hd : ∀ i, |d i| = Ground.fpSimple C i)
    (hdom : ∀ i j k, |T i j k| ≤ (Ground.fusionCoeff C i j k : ℝ))
    (heig : ∀ i j, ∑ k, T i j k * d k = d i * d j) :
    ∀ i j k, T i j k =
      (d i / Ground.fpSimple C i) * (d j / Ground.fpSimple C j) *
      (d k / Ground.fpSimple C k) * (Ground.fusionCoeff C i j k : ℝ) := by
  classical
  let f := Ground.fpSimple C
  let s : Fin (Ground.rank C) → ℝ := fun i => d i / f i
  have hf : ∀ i, 0 < f i := Ground.fpSimple_pos C
  have hs : ∀ i, s i * s i = 1 := by
    intro i
    have hsq : d i * d i = f i * f i := by
      have h := congrArg (fun x : ℝ => x * x) (hd i)
      simpa only [abs_mul_abs_self] using h
    dsimp [s]
    field_simp [ne_of_gt (hf i)]
    nlinarith [hsq]
  intro i j k
  have ht : (s i * s j) * (s i * s j) = 1 := by
    rw [show (s i * s j) * (s i * s j) = (s i * s i) * (s j * s j) by ring, hs i, hs j]
    norm_num
  have heq : ∑ l, T i j l * s l * f l = (s i * s j) *
      ∑ l, (Ground.fusionCoeff C i j l : ℝ) * f l := by
    calc
      _ = ∑ l, T i j l * d l := by
        apply Finset.sum_congr rfl
        intro l _
        dsimp [s]
        field_simp [ne_of_gt (hf l)]
      _ = d i * d j := heig i j
      _ = (s i * s j) * (f i * f j) := by
        dsimp [s]
        field_simp [ne_of_gt (hf i), ne_of_gt (hf j)]
      _ = _ := by rw [Ground.fpSimple_mul]
  exact weighted_sign_saturation (fun l => Ground.fusionCoeff C i j l) (T i j)
    f s (s i * s j) hf hs ht (hdom i j) heq k

end PropertyF.Ground.Dimensions
