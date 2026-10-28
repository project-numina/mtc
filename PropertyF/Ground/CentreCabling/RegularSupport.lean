module
public import PropertyF.Ground.Modular.CharacterStar
public import PropertyF.Ground.Fusion.Agreement
public import PropertyF.Ground.Fusion.Agreement
public import PropertyF.Ground.Modular.SSquare
public import PropertyF.Ground.Fusion.Reciprocity

/-!
# Fusion centralizers and Fourier support

The equality locus of a fusion character is closed under constituents.
Fourier inversion and the FP-weighted regular eigenvector then give the
numerical double-centralizer inclusion.
-/
@[expose] public noncomputable section
open scoped BigOperators
namespace PropertyF.Ground.CentreCabling
universe v u
variable (D : Ground.BraidedFusionCategory.{v,u})
  (p : Dimensions.PivotalStructure (C := D.Obj))

/-- The numerical S-centralizer is closed under dual labels when dimensions
are the positive FP dimensions. -/
theorem sCentralizer_closed_under_dual
    (hdim : Modular.HasFPSimpleDimensions D p)
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

open scoped BigOperators
namespace PropertyF.Ground.CentreCabling
universe v u
variable (D : Ground.BraidedFusionCategory.{v,u})
  (p : Dimensions.PivotalStructure (C := D.Obj))

/-- The S-transform of a vector, inverted using the categorical S-square identity. -/
theorem categoricalS_fourier_inversion
    (hp : p.IsSpherical)
    (hdet : (Modular.categoricalS D p).det ≠ 0)
    (hreal : ∀ j, starRingEnd ℂ (Modular.simpleDimension D p j) = Modular.simpleDimension D p j)
    (f : Fin (rank D) → ℂ) (x : Fin (rank D)) :
    (∑ y, Modular.categoricalS D p x y *
      (∑ i, Modular.categoricalS D p y i * f i)) =
      globalDimension D * f (dualIndex D x) := by
  classical
  calc
    _ = ∑ i, (∑ y, Modular.categoricalS D p x y * Modular.categoricalS D p y i) * f i := by
      simp only [Finset.mul_sum, Finset.sum_mul, mul_assoc]
      rw [Finset.sum_comm]
    _ = ∑ i, (if x = dualIndex D i then globalDimension D else 0) * f i := by
      simp_rw [Modular.categoricalS_square D p hp hdet hreal]
    _ = globalDimension D * f (dualIndex D x) := by
      rw [Finset.sum_eq_single (dualIndex D x)]
      · rw [dualIndex_involutive D x]
        simp
      · intro b _ hb
        have hx : x ≠ dualIndex D b := by
          intro h
          apply hb
          have hh := congrArg (dualIndex D) h
          rw [dualIndex_involutive D b] at hh
          exact hh.symm
        simp [hx]
      · intro h
        exact (h (Finset.mem_univ _)).elim

/-- If the S-transform of a vector is supported on a set of labels and its
unit coefficient is nonzero, any label centralizing that support has a
nonzero dual coefficient in the original vector. -/
theorem nonzero_dual_coefficient_of_sCentralizer
    (hp : p.IsSpherical)
    (hdet : (Modular.categoricalS D p).det ≠ 0)
    (hreal : ∀ j, starRingEnd ℂ (Modular.simpleDimension D p j) = Modular.simpleDimension D p j)
    (f : Fin (rank D) → ℂ) (core : Set (Fin (rank D)))
    (hunit : f (unitIndex D) ≠ 0)
    (hsupport : ∀ y, y ∉ core → ∑ i, Modular.categoricalS D p y i * f i = 0)
    (x : Fin (rank D))
    (hx : ∀ y ∈ core, Modular.categoricalS D p x y =
      Modular.simpleDimension D p x * Modular.simpleDimension D p y) :
    f (dualIndex D x) ≠ 0 := by
  classical
  let T (y : Fin (rank D)) := ∑ i, Modular.categoricalS D p y i * f i
  have heq : (∑ y, Modular.categoricalS D p x y * T y) =
      Modular.simpleDimension D p x *
        (∑ y, Modular.categoricalS D p (unitIndex D) y * T y) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y _
    by_cases hy : y ∈ core
    · rw [hx y hy, Modular.categoricalS_symmetric D p (unitIndex D) y,
        Modular.categoricalS_unit]
      ring
    · have hz : T y = 0 := hsupport y hy
      simp [hz]
  have hxinv := categoricalS_fourier_inversion D p hp hdet hreal f x
  have huinv := categoricalS_fourier_inversion D p hp hdet hreal f (unitIndex D)
  change (∑ y, Modular.categoricalS D p x y * T y) = _ at hxinv
  change (∑ y, Modular.categoricalS D p (unitIndex D) y * T y) = _ at huinv
  rw [hxinv, huinv, Ground.dualIndex_unit D] at heq
  have hn := mul_ne_zero (Modular.simpleDimension_ne_zero D p x)
    (mul_ne_zero (Modular.globalDimension_ne_zero_of_invertibleS D p hp hdet hreal) hunit)
  intro hz
  rw [hz, mul_zero] at heq
  exact hn heq.symm

/-- A vector supported on generated labels proves the exact double-centralizer
inclusion once its S-transform is supported on the chosen core. The support
hypotheses are explicit: this theorem does not establish the required
regular-vector identity. -/
theorem doubleCentralizer_of_fourier_support
    (hp : p.IsSpherical)
    (hdet : (Modular.categoricalS D p).det ≠ 0)
    (hdim : Modular.HasFPSimpleDimensions D p)
    (f : Fin (rank D) → ℂ) (core generated : Set (Fin (rank D)))
    (hunit : f (unitIndex D) ≠ 0)
    (hgenerated : ∀ y, f y ≠ 0 → y ∈ generated)
    (hsupport : ∀ y, y ∉ core → ∑ i, Modular.categoricalS D p y i * f i = 0) :
    ∀ x, (∀ y ∈ core, Modular.categoricalS D p y x =
      Modular.simpleDimension D p y * Modular.simpleDimension D p x) → x ∈ generated := by
  intro x hx
  have hreal (j) : starRingEnd ℂ (Modular.simpleDimension D p j) = Modular.simpleDimension D p j := by
    rw [hdim]
    simp
  have hdual (y) (hy : y ∈ core) :
      Modular.categoricalS D p (dualIndex D x) y =
        Modular.simpleDimension D p (dualIndex D x) * Modular.simpleDimension D p y := by
    apply sCentralizer_closed_under_dual D p hdim x y
    rw [Modular.categoricalS_symmetric]
    simpa [mul_comm] using hx y hy
  have h := nonzero_dual_coefficient_of_sCentralizer D p hp hdet hreal f core
    hunit hsupport (dualIndex D x) hdual
  rw [dualIndex_involutive D x] at h
  exact hgenerated x h

end PropertyF.Ground.CentreCabling

open scoped BigOperators
namespace PropertyF.Ground.CentreCabling
universe v u
variable (D : Ground.BraidedFusionCategory.{v,u})
  (p : Dimensions.PivotalStructure (C := D.Obj))

/-- The S-transform of a common FP eigenvector vanishes at every label whose
normalized S character differs from the FP character on a chosen label. -/
theorem fourier_eq_zero_of_fusion_eigenvector
    (hdim : Modular.HasFPSimpleDimensions D p)
    (f : Fin (rank D) → ℂ) (a y : Fin (rank D))
    (heigen : ∀ k, ∑ i, (fusionCoeff D a i k : ℂ) * f i = (fpSimple D a : ℂ) * f k)
    (hne : Modular.categoricalS D p a y ≠
      Modular.simpleDimension D p a * Modular.simpleDimension D p y) :
    ∑ i, Modular.categoricalS D p y i * f i = 0 := by
  classical
  let χ (i : Fin (rank D)) := Modular.categoricalS D p i y / Modular.simpleDimension D p y
  let T : ℂ := ∑ i, χ i * f i
  have ht : χ a * T = (fpSimple D a : ℂ) * T := by
    calc
      _ = ∑ i, (χ a * χ i) * f i := by simp [T, Finset.mul_sum, mul_assoc]
      _ = ∑ i, ∑ k, (fusionCoeff D a i k : ℂ) * χ k * f i := by
        apply Finset.sum_congr rfl
        intro i _
        rw [Modular.categoricalS_verlinde D p a i y]
        simp only [Finset.sum_mul, χ]
      _ = ∑ k, χ k * (∑ i, (fusionCoeff D a i k : ℂ) * f i) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro k _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = (fpSimple D a : ℂ) * T := by
        simp_rw [heigen]
        simp only [T, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _
        ring
  have hχ : χ a ≠ (fpSimple D a : ℂ) := fun h ↦ hne <| by
    simpa [χ, hdim] using (div_eq_iff (Modular.simpleDimension_ne_zero D p y)).mp h
  have hT : T = 0 := (mul_eq_mul_right_iff.mp ht).resolve_left hχ
  have hs : (∑ i, Modular.categoricalS D p y i * f i) = Modular.simpleDimension D p y * T := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Modular.categoricalS_symmetric D p y i]
    dsimp [χ]
    field_simp [Modular.simpleDimension_ne_zero D p y]
  rw [hs, hT, mul_zero]

/-- The FP-weighted regular vector of a dual- and fusion-closed set of labels
is an eigenvector for multiplication by each label in that set. -/
theorem regular_vector_fusion_eigenvector
    (A : Finset (Fin (rank D)))
    (hdual : ∀ a ∈ A, dualIndex D a ∈ A)
    (hclosed : ∀ a ∈ A, ∀ b ∈ A, ∀ k, 0 < fusionCoeff D a b k → k ∈ A)
    (a : Fin (rank D)) (ha : a ∈ A) (k : Fin (rank D)) :
    (∑ i, (fusionCoeff D a i k : ℂ) * (if i ∈ A then (fpSimple D i : ℂ) else 0)) =
      (fpSimple D a : ℂ) * (if k ∈ A then (fpSimple D k : ℂ) else 0) := by
  classical
  by_cases hk : k ∈ A
  · simp only [hk, ite_true]
    calc
      _ = ∑ i, (fusionCoeff D (dualIndex D a) k i : ℂ) * (fpSimple D i : ℂ) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [Modular.fusionCoeff_dual_adjoint D a i k]
        by_cases hi : i ∈ A
        · simp [hi]
        · have hn : fusionCoeff D (dualIndex D a) k i = 0 := by
            apply Nat.eq_zero_of_not_pos
            intro hp
            exact hi (hclosed (dualIndex D a) (hdual a ha) k hk i hp)
          simp [hi, hn]
      _ = (fpSimple D a : ℂ) * (fpSimple D k : ℂ) := by
        have hh := congrArg (fun z : ℝ => (z : ℂ)) (fpSimple_mul D (dualIndex D a) k)
        simpa [fpSimple_dual] using hh.symm
  · simp only [hk, ite_false, mul_zero]
    apply Finset.sum_eq_zero
    intro i _
    by_cases hi : i ∈ A
    · have hn : fusionCoeff D a i k = 0 := by
        apply Nat.eq_zero_of_not_pos
        intro hp
        exact hk (hclosed a ha i hi k hp)
      simp [hi, hn]
    · simp [hi]

/-- Numerical double-centralizer theorem for a fusion-closed set of simple
labels. The supplied core must contain its numerical S-centralizer. -/
theorem doubleCentralizer_of_fusion_closed
    (hp : p.IsSpherical)
    (hdet : (Modular.categoricalS D p).det ≠ 0)
    (hdim : Modular.HasFPSimpleDimensions D p)
    (A : Finset (Fin (rank D))) (core : Set (Fin (rank D)))
    (hunit : unitIndex D ∈ A)
    (hdual : ∀ a ∈ A, dualIndex D a ∈ A)
    (hclosed : ∀ a ∈ A, ∀ b ∈ A, ∀ k, 0 < fusionCoeff D a b k → k ∈ A)
    (hcore : ∀ y, (∀ a ∈ A, Modular.categoricalS D p a y =
      Modular.simpleDimension D p a * Modular.simpleDimension D p y) → y ∈ core) :
    ∀ x, (∀ y ∈ core, Modular.categoricalS D p y x =
      Modular.simpleDimension D p y * Modular.simpleDimension D p x) → x ∈ A := by
  classical
  let f (i : Fin (rank D)) : ℂ := if i ∈ A then (fpSimple D i : ℂ) else 0
  have hu : f (unitIndex D) ≠ 0 := by
    simp only [f, hunit, ite_true, ne_eq, Complex.ofReal_eq_zero]
    exact ne_of_gt (fpSimple_pos D (unitIndex D))
  have hgen : ∀ i, f i ≠ 0 → i ∈ (↑A : Set (Fin (rank D))) := by
    intro i hi
    by_contra hn
    change i ∉ A at hn
    exact hi (by simp [f, hn])
  have hs : ∀ y, y ∉ core → ∑ i, Modular.categoricalS D p y i * f i = 0 := by
    intro y hy
    have ha : ∃ a ∈ A, Modular.categoricalS D p a y ≠
        Modular.simpleDimension D p a * Modular.simpleDimension D p y := by
      by_contra hn
      apply hy
      apply hcore
      push Not at hn
      exact hn
    obtain ⟨a, ha, hne⟩ := ha
    apply fourier_eq_zero_of_fusion_eigenvector D p hdim f a y
    · exact regular_vector_fusion_eigenvector D A hdual hclosed a ha
    · exact hne
  exact doubleCentralizer_of_fourier_support D p hp hdet hdim f core (↑A : Set _) hu hgen hs

end PropertyF.Ground.CentreCabling
