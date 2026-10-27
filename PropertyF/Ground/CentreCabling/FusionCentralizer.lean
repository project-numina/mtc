module
public import PropertyF.Ground.Modular.CharacterStar
public import PropertyF.Ground.Dimensions.CharacterBound
public import PropertyF.Ground.Fusion.Agreement

/-! The equality locus of a fusion character is closed under constituents. -/

@[expose] public noncomputable section
open scoped BigOperators
namespace PropertyF.Ground.CentreCabling
universe v u

/-- If a fusion character takes its FP value on two simples, then it takes
its FP value on every simple constituent of their tensor product. -/
theorem character_fp_eq_of_constituent (D : Ground.BraidedFusionCategory.{v,u})
    (χ : Fin (rank D) → ℂ) (hunit : χ (unitIndex D) = 1)
    (hchar : ∀ i j, χ i * χ j = ∑ k, (fusionCoeff D i j k : ℂ) * χ k)
    (i j k : Fin (rank D))
    (hi : χ i = (fpSimple D i : ℂ)) (hj : χ j = (fpSimple D j : ℂ))
    (hk : 0 < fusionCoeff D i j k) : χ k = (fpSimple D k : ℂ) := by
  classical
  have hbound (a : Fin (rank D)) : ‖χ a‖ ≤ fpSimple D a :=
    Dimensions.character_norm_le_fpSimple D χ (unitIndex D) (by rw [hunit]; norm_num) hchar a
  have hre (a : Fin (rank D)) : (χ a).re ≤ fpSimple D a :=
    le_trans (Complex.re_le_norm _) (hbound a)
  have hsum : ∑ a, (fusionCoeff D i j a : ℝ) * (fpSimple D a - (χ a).re) = 0 := by
    have hh := congrArg Complex.re (hchar i j)
    simp only [hi, hj, Complex.ofReal_re, Complex.ofReal_im, Complex.re_sum,
      Complex.mul_re, Complex.natCast_re, Complex.natCast_im, zero_mul, sub_zero] at hh
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, ← fpSimple_mul D i j]
    linarith
  have hz : (fusionCoeff D i j k : ℝ) * (fpSimple D k - (χ k).re) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun a _ => mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr (hre a)))).mp hsum k (Finset.mem_univ _)
  have hcoeff : (0 : ℝ) < fusionCoeff D i j k := by exact_mod_cast hk
  have hreal : (χ k).re = fpSimple D k := by nlinarith
  have hnorm : (χ k).re ^ 2 + (χ k).im ^ 2 ≤ fpSimple D k ^ 2 := by
    have hs := sq_le_sq₀ (norm_nonneg (χ k)) (fpSimple_pos D k).le |>.2 (hbound k)
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply] at hs
    simpa [pow_two] using hs
  have him : (χ k).im = 0 := by
    rw [hreal] at hnorm
    nlinarith [sq_nonneg (χ k).im]
  apply Complex.ext <;> simp [hreal, him]

/-- In a positive spherical realization, the S-centralizer of any label is
closed under simple tensor-product constituents. Neither S invertibility nor
finite braid images are needed. -/
theorem sCentralizer_closed_under_constituents
    (D : Ground.BraidedFusionCategory.{v,u})
    (p : Dimensions.PivotalStructure (C := D.Obj))
    (hdim : ∀ a, Modular.simpleDimension D p a = (fpSimple D a : ℂ))
    (i j k y : Fin (rank D))
    (hi : Modular.categoricalS D p i y = Modular.simpleDimension D p i * Modular.simpleDimension D p y)
    (hj : Modular.categoricalS D p j y = Modular.simpleDimension D p j * Modular.simpleDimension D p y)
    (hk : 0 < fusionCoeff D i j k) :
    Modular.categoricalS D p k y = Modular.simpleDimension D p k * Modular.simpleDimension D p y := by
  let χ : Fin (rank D) → ℂ := fun a => Modular.categoricalS D p a y / Modular.simpleDimension D p y
  have hd : Modular.simpleDimension D p y ≠ 0 := Modular.simpleDimension_ne_zero D p y
  have hunit : χ (unitIndex D) = 1 := by
    dsimp [χ]
    rw [Modular.categoricalS_symmetric, Modular.categoricalS_unit]
    exact div_self hd
  have hc : ∀ a b, χ a * χ b = ∑ t, (fusionCoeff D a b t : ℂ) * χ t :=
    fun a b => Modular.categoricalS_verlinde D p a b y
  have hχi : χ i = (fpSimple D i : ℂ) := by
    dsimp [χ]
    rw [hi, mul_div_cancel_right₀ _ hd, hdim]
  have hχj : χ j = (fpSimple D j : ℂ) := by
    dsimp [χ]
    rw [hj, mul_div_cancel_right₀ _ hd, hdim]
  have hχk := character_fp_eq_of_constituent D χ hunit hc i j k hχi hχj hk
  change Modular.categoricalS D p k y / Modular.simpleDimension D p y = _ at hχk
  rw [← hdim k] at hχk
  exact (div_eq_iff hd).mp hχk

/-- The numerical S-centralizer is closed under dual labels when dimensions
are the positive FP dimensions. -/
theorem sCentralizer_closed_under_dual
    (D : Ground.BraidedFusionCategory.{v,u})
    (p : Dimensions.PivotalStructure (C := D.Obj))
    (hdim : ∀ a, Modular.simpleDimension D p a = (fpSimple D a : ℂ))
    (i y : Fin (rank D))
    (hi : Modular.categoricalS D p i y = Modular.simpleDimension D p i * Modular.simpleDimension D p y) :
    Modular.categoricalS D p (dualIndex D i) y =
      Modular.simpleDimension D p (dualIndex D i) * Modular.simpleDimension D p y := by
  have hreal (a) : starRingEnd ℂ (Modular.simpleDimension D p a) = Modular.simpleDimension D p a := by
    rw [hdim]
    simp
  rw [Modular.categoricalS_dual_conj D p hreal i y, hi, map_mul, hreal, hreal]
  rw [hdim (dualIndex D i), fpSimple_dual, ← hdim i]

end PropertyF.Ground.CentreCabling
