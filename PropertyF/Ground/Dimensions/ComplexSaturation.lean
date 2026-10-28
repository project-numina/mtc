module
public import PropertyF.Ground.Dimensions.ENOMatrices

/-! # Saturation of complex eigenvalue bounds

Equality in weighted complex bounds determines the phases of eigenvectors.
-/

@[expose] public noncomputable section
open scoped BigOperators
namespace PropertyF.Ground.Dimensions

/-- If a complex weighted sum reaches its nonnegative termwise norm bound,
all its positive-weight terms equal their respective bounds. -/
theorem complex_weighted_saturation {ι : Type*} [Fintype ι]
    (N f : ι → ℝ) (x : ι → ℂ) (hf : ∀ k, 0 < f k)
    (hdom : ∀ k, ‖x k‖ ≤ N k)
    (heq : ∑ k, x k * (f k : ℂ) = ((∑ k, N k * f k : ℝ) : ℂ)) :
    ∀ k, x k = (N k : ℂ) := by
  classical
  have hN (k : ι) : 0 ≤ N k := le_trans (norm_nonneg _) (hdom k)
  have hnonneg (k : ι) : 0 ≤ (N k - (x k).re) * f k :=
    mul_nonneg (sub_nonneg.mpr (le_trans (Complex.re_le_norm _) (hdom k))) (le_of_lt (hf k))
  have hsum : ∑ k, (N k - (x k).re) * f k = 0 := by
    have hr := congrArg Complex.re heq
    simp only [Complex.re_sum, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, sub_zero] at hr
    simp only [sub_mul, Finset.sum_sub_distrib]
    linarith
  intro k
  have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hnonneg j)).1 hsum k (Finset.mem_univ k)
  have hre : (x k).re = N k := by
    have hh := (mul_eq_zero.mp hz).resolve_right (ne_of_gt (hf k))
    linarith
  have hsq : ‖x k‖ ^ 2 ≤ N k ^ 2 := by nlinarith [norm_nonneg (x k), hdom k, hN k]
  rw [Complex.sq_norm, Complex.normSq_apply, hre] at hsq
  have him : (x k).im = 0 := by nlinarith [sq_nonneg ((x k).im)]
  apply Complex.ext <;> simp [hre, him]

/-- Saturation of a complex fusion-matrix eigenvector forces every term to
have the common phase of the product of the two eigenvector values. -/
theorem fusion_complex_eigenvalue_saturation (C : PropertyF.Ground.BraidedFusionCategory)
    (T : Fin (PropertyF.Ground.rank C) → Fin (PropertyF.Ground.rank C) →
      Fin (PropertyF.Ground.rank C) → ℂ)
    (d : Fin (PropertyF.Ground.rank C) → ℂ)
    (hd : ∀ i, ‖d i‖ = PropertyF.Ground.fpSimple C i)
    (hdom : ∀ i j k, ‖T i j k‖ ≤ (PropertyF.Ground.fusionCoeff C i j k : ℝ))
    (heig : ∀ i j, ∑ k, T i j k * d k = d i * d j) :
    ∀ i j k,
      T i j k * (d k / (PropertyF.Ground.fpSimple C k : ℂ)) /
        ((d i / (PropertyF.Ground.fpSimple C i : ℂ)) *
          (d j / (PropertyF.Ground.fpSimple C j : ℂ))) =
        (PropertyF.Ground.fusionCoeff C i j k : ℂ) := by
  classical
  let f := PropertyF.Ground.fpSimple C
  let q : Fin (PropertyF.Ground.rank C) → ℂ := fun i => d i / (f i : ℂ)
  have hf : ∀ i, 0 < f i := PropertyF.Ground.fpSimple_pos C
  have hq : ∀ i, ‖q i‖ = 1 := by
    intro i
    dsimp [q]
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hf i), hd i]
    exact div_self (ne_of_gt (hf i))
  have hqn : ∀ i, q i ≠ 0 := fun i => norm_pos_iff.mp (by rw [hq]; norm_num)
  have hrepr : ∀ i, q i * (f i : ℂ) = d i := by
    intro i
    dsimp [q]
    field_simp [show (f i : ℂ) ≠ 0 by exact_mod_cast (ne_of_gt (hf i))]
  intro i j k
  let x : Fin (PropertyF.Ground.rank C) → ℂ := fun l => T i j l * q l / (q i * q j)
  have hx : ∀ l, ‖x l‖ ≤ (PropertyF.Ground.fusionCoeff C i j l : ℝ) := by
    intro l
    dsimp [x]
    rw [norm_div, norm_mul, norm_mul, hq l, hq i, hq j]
    simpa using hdom i j l
  have heq : ∑ l, x l * (f l : ℂ) =
      ((∑ l, (PropertyF.Ground.fusionCoeff C i j l : ℝ) * f l : ℝ) : ℂ) := by
    calc
      _ = (∑ l, T i j l * d l) / (q i * q j) := by
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro l _
        rw [← hrepr l]
        dsimp [x]
        ring
      _ = (d i * d j) / (q i * q j) := by rw [heig]
      _ = ((f i * f j : ℝ) : ℂ) := by
        rw [← hrepr i, ← hrepr j, Complex.ofReal_mul]
        field_simp [hqn i, hqn j]
      _ = _ := by rw [PropertyF.Ground.fpSimple_mul]
  exact complex_weighted_saturation (fun l => PropertyF.Ground.fusionCoeff C i j l) f x
    hf hx heq k

end PropertyF.Ground.Dimensions
