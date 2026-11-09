module
public import MTC.Center.Normalization.SubringCharacter

open MTC.Fusion MTC.Braided MTC.Center.Braid MTC.CategoryTheory.Dimensions

/-! # Saturated fusion characters

These lemmas analyze fusion-character scalar ratios and the normalization
of a fusion subring whose simple dimensions attain their FP bounds.
`transparent_norm_saturation_of_adjoint_positivity` later proves the needed
saturation for the transparent labels.
-/

@[expose] public noncomputable section
open scoped BigOperators
namespace MTC.Center.Normalization

/-- A weighted average of closed-unit-disc elements can equal one only when
all entries of positive weight are one. -/
theorem eq_one_of_weighted_unit_disc {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (z : ι → ℂ) (hw : ∀ i, 0 ≤ w i) (hz : ∀ i, ‖z i‖ ≤ 1)
    (hsum : (∑ i, (w i : ℂ) * z i) = ((∑ i, w i : ℝ) : ℂ))
    (i : ι) (hi : 0 < w i) : z i = 1 := by
  have h := complex_weighted_saturation (f := fun _ ↦ 1) (N := w)
    (x := fun j ↦ (w j : ℂ) * z j) (fun _ ↦ zero_lt_one)
    (fun j ↦ by simpa [norm_mul, Real.norm_eq_abs, abs_of_nonneg (hw j)] using
      mul_le_mul_of_nonneg_left (hz j) (hw j)) (by simpa using hsum) i
  have hwi : (w i : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hi)
  apply mul_left_cancel₀ hwi
  simpa using h



universe v u
variable {C : BraidedFusionCategory.{v,u}}

/-- Pivotal dimension divided by the positive FP dimension of a simple. -/
def dimensionRatio (p : PivotalStructure (C := C.Obj)) (i : Fin (rank C)) : ℂ :=
  pivotalDimension C p (simples C i) / (fpSimple C i : ℂ)

/-- Every pivotal simple-dimension ratio lies in the closed unit disc. -/
theorem dimensionRatio_norm_le_one (p : PivotalStructure (C := C.Obj))
    (i : Fin (rank C)) : ‖dimensionRatio p i‖ ≤ 1 := by
  have h := character_norm_le_fpSimple (C := C) (i₀ := unitIndex C)
    ((pivotalDimension_unitIndex C p).symm ▸ one_ne_zero)
    (pivotalDimension_character C p) i
  rw [dimensionRatio, norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (fpSimple_pos C i), div_le_one (fpSimple_pos C i)]
  exact h

/-- If the pivotal dimension attains its FP bound on a simple, its ratio is
on the unit circle. -/
theorem dimensionRatio_norm_eq_one (p : PivotalStructure (C := C.Obj))
    (i : Fin (rank C)) (h : ‖pivotalDimension C p (simples C i)‖ = fpSimple C i) :
    ‖dimensionRatio p i‖ = 1 := by
  simp [dimensionRatio, h, abs_of_pos (fpSimple_pos C i),
    ne_of_gt (fpSimple_pos C i)]


/-- If two simple pivotal dimensions attain their FP bounds, every simple
constituent of their tensor product has the product of their dimension ratios.
This uses only the actual fusion character and its general FP bound. -/
theorem dimensionRatio_tensor_constituent
    (p : PivotalStructure (C := C.Obj)) (i j k : Fin (rank C))
    (hi : ‖pivotalDimension C p (simples C i)‖ = fpSimple C i)
    (hj : ‖pivotalDimension C p (simples C j)‖ = fpSimple C j)
    (hk : 0 < fusionCoeff C i j k) :
    dimensionRatio p k = dimensionRatio p i * dimensionRatio p j := by
  classical
  let u := dimensionRatio p i * dimensionRatio p j
  let w (a : Fin (rank C)) : ℝ := (fusionCoeff C i j a : ℝ) * fpSimple C a
  let z (a : Fin (rank C)) : ℂ := star u * dimensionRatio p a
  have hu : ‖u‖ = 1 := by
    simp [u, dimensionRatio_norm_eq_one p i hi, dimensionRatio_norm_eq_one p j hj]
  have huone : star u * u = 1 := by
    simpa only [Complex.star_def, hu, one_pow, Complex.ofReal_one] using Complex.conj_mul' u
  have hw (a : Fin (rank C)) : 0 ≤ w a := by
    exact mul_nonneg (Nat.cast_nonneg _) (le_of_lt (fpSimple_pos C a))
  have hz (a : Fin (rank C)) : ‖z a‖ ≤ 1 := by
    simpa [z, norm_mul, hu] using dimensionRatio_norm_le_one p a
  have hsum : (∑ a, (w a : ℂ) * z a) = ((∑ a, w a : ℝ) : ℂ) := by
    have hfp : (∑ a, (fusionCoeff C i j a : ℂ) * (fpSimple C a : ℂ)) =
        (fpSimple C i : ℂ) * (fpSimple C j : ℂ) := by
      exact_mod_cast (fpSimple_mul C i j).symm
    have hd (a : Fin (rank C)) : (fpSimple C a : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (ne_of_gt (fpSimple_pos C a))
    calc
      _ = star u * ∑ a, (fusionCoeff C i j a : ℂ) * pivotalDimension C p (simples C a) := by
        simp only [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro a ha
        dsimp [w, z, dimensionRatio]
        push_cast
        field_simp [hd a]
      _ = star u * (pivotalDimension C p (simples C i) * pivotalDimension C p (simples C j)) := by
        rw [← pivotalDimension_character C p i j]
      _ = (star u * u) * ((fpSimple C i : ℂ) * (fpSimple C j : ℂ)) := by
        dsimp [u, dimensionRatio]
        field_simp [hd i, hd j]
      _ = ((∑ a, w a : ℝ) : ℂ) := by
        rw [huone, one_mul]
        simpa only [w, Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_natCast] using hfp.symm
  have hwk : 0 < w k := mul_pos (Nat.cast_pos.mpr hk) (fpSimple_pos C k)
  have heq := eq_one_of_weighted_unit_disc w z hw hz hsum k hwk
  have hu0 : u ≠ 0 := by
    intro h
    simp [h] at hu
  apply mul_left_cancel₀ (star_ne_zero.mpr hu0)
  change z k = star u * u
  exact heq.trans huone.symm


/-- The pivotal-to-FP dimension ratio of a simple is a complex unit. -/
def dimensionRatioUnit (p : PivotalStructure (C := C.Obj)) (i : Fin (rank C)) : ℂˣ :=
  Units.mk0 (dimensionRatio p i) <| div_ne_zero
    (MTC.Modular.simpleDimension_ne_zero C p i)
    (Complex.ofReal_ne_zero.mpr (ne_of_gt (fpSimple_pos C i)))

/-- The ratio on the unit simple is one. -/
theorem dimensionRatioUnit_unit (p : PivotalStructure (C := C.Obj)) :
    dimensionRatioUnit p (unitIndex C) = 1 := by
  apply Units.ext
  simp [dimensionRatioUnit, dimensionRatio, pivotalDimension_unitIndex, fpSimple_unit]

/-- Ratios on saturated simple dimensions form a fusion-compatible scalar
assignment on any fusion subring. -/
theorem dimensionRatioUnit_tensor
    (p : PivotalStructure (C := C.Obj)) (i j k : Fin (rank C))
    (hi : ‖pivotalDimension C p (simples C i)‖ = fpSimple C i)
    (hj : ‖pivotalDimension C p (simples C j)‖ = fpSimple C j)
    (hk : 0 < fusionCoeff C i j k) :
    dimensionRatioUnit p k = dimensionRatioUnit p i * dimensionRatioUnit p j := by
  apply Units.ext
  exact dimensionRatio_tensor_constituent p i j k hi hj hk

/-- If the simple pivotal dimensions of a fusion subring attain their FP
bounds and its ambient-neutral simple dimensions are positive, a pivotal
twist normalizes all dimensions on that subring. -/
theorem normalize_pivotal_of_subring_norm_saturation
    {A : Finset (Fin (rank C))} (hA : IsFusionSubring C A)
    (p : PivotalStructure (C := C.Obj))
    (hsat : ∀ i : A, ‖pivotalDimension C p (simples C i)‖ = fpSimple C i)
    (hpositive : ∀ i : A, fusionDegree C i = 0 → ∃ r : ℝ,
      0 < r ∧ pivotalDimension C p (simples C i) = r) :
    ∃ q : PivotalStructure (C := C.Obj), ∀ i : A,
      pivotalDimension C q (simples C i) = (fpSimple C i : ℂ) := by
  apply normalize_pivotal_of_fusion_scalar_ratios hA p
    (fun i ↦ dimensionRatioUnit p i)
  · exact dimensionRatioUnit_unit p
  · intro i j k hk
    exact dimensionRatioUnit_tensor p i j k (hsat i) (hsat j) hk
  · exact hpositive
  · intro i
    change pivotalDimension C p (simples C i) = dimensionRatio p i * (fpSimple C i : ℂ)
    rw [dimensionRatio, div_mul_cancel₀ _
      (Complex.ofReal_ne_zero.mpr (ne_of_gt (fpSimple_pos C i)))]

end MTC.Center.Normalization
end
