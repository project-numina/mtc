module
public import PropertyF.Ground.CentreCabling.FusionCentralizer
public import PropertyF.Ground.Modular.Construction

/-! A Fourier-support reduction of the double-centralizer inclusion. -/

@[expose] public noncomputable section
open scoped BigOperators
namespace PropertyF.Ground.CentreCabling
universe v u

/-- The S-transform of a vector, inverted using the categorical S-square identity. -/
theorem categoricalS_fourier_inversion
    (D : Ground.BraidedFusionCategory.{v,u})
    (p : Dimensions.PivotalStructure (C := D.Obj)) (hp : p.IsSpherical)
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
    (D : Ground.BraidedFusionCategory.{v,u})
    (p : Dimensions.PivotalStructure (C := D.Obj)) (hp : p.IsSpherical)
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
  rw [hxinv, huinv, Modular.dualIndex_unit D] at heq
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
    (D : Ground.BraidedFusionCategory.{v,u})
    (p : Dimensions.PivotalStructure (C := D.Obj)) (hp : p.IsSpherical)
    (hdet : (Modular.categoricalS D p).det ≠ 0)
    (hdim : ∀ j, Modular.simpleDimension D p j = (fpSimple D j : ℂ))
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
