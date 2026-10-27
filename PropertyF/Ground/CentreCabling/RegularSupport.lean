module
public import PropertyF.Ground.CentreCabling.FourierCentralizer

/-! The numerical centralizer as the Fourier support of a fusion eigenvector. -/

@[expose] public noncomputable section
open scoped BigOperators
namespace PropertyF.Ground.CentreCabling
universe v u

/-- The S-transform of a common FP eigenvector vanishes at every label whose
normalized S character differs from the FP character on a chosen label. -/
theorem fourier_eq_zero_of_fusion_eigenvector
    (D : Ground.BraidedFusionCategory.{v,u})
    (p : Dimensions.PivotalStructure (C := D.Obj))
    (hdim : ∀ j, Modular.simpleDimension D p j = (fpSimple D j : ℂ))
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
  have hχ : χ a ≠ (fpSimple D a : ℂ) := by
    intro h
    apply hne
    have hd := Modular.simpleDimension_ne_zero D p y
    have hh := (div_eq_iff hd).mp h
    simpa [χ, hdim] using hh
  have hT : T = 0 := by
    apply (mul_eq_zero.mp (show (χ a - (fpSimple D a : ℂ)) * T = 0 by
      rw [sub_mul, ht, sub_self])).resolve_left (sub_ne_zero.mpr hχ)
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
    (D : Ground.BraidedFusionCategory.{v,u}) (A : Finset (Fin (rank D)))
    (hdual : ∀ a ∈ A, dualIndex D a ∈ A)
    (hclosed : ∀ a ∈ A, ∀ b ∈ A, ∀ k, 0 < fusionCoeff D a b k → k ∈ A)
    (a : Fin (rank D)) (ha : a ∈ A) (k : Fin (rank D)) :
    (∑ i, (fusionCoeff D a i k : ℂ) * (if i ∈ A then (fpSimple D i : ℂ) else 0)) =
      (fpSimple D a : ℂ) * (if k ∈ A then (fpSimple D k : ℂ) else 0) := by
  classical
  by_cases hk : k ∈ A
  · simp only [hk, if_true]
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
  · simp only [hk, if_false, mul_zero]
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
    (D : Ground.BraidedFusionCategory.{v,u})
    (p : Dimensions.PivotalStructure (C := D.Obj)) (hp : p.IsSpherical)
    (hdet : (Modular.categoricalS D p).det ≠ 0)
    (hdim : ∀ j, Modular.simpleDimension D p j = (fpSimple D j : ℂ))
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
    simp only [f, hunit, if_true, ne_eq, Complex.ofReal_eq_zero]
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
