module
public import MTC.Center.Braid.RegularSupport
public import MTC.Center.Induction.PivotalFusion

open MTC.Fusion MTC.Braided MTC.CategoryTheory.Dimensions MTC.PropertyF.Reduction

/-! # Regular vectors for arbitrary pivotal structures

The conjugate pivotal-dimension vector of a fusion-closed set has the pivotal
fusion eigenvalues. This supplies Fourier support without FP-valued dimensions.
-/

@[expose] public noncomputable section
open scoped BigOperators
open MTC.Modular (sCentralizes sCentralizer)
namespace MTC.Center.Braid
universe v u
variable {D : BraidedFusionCategory.{v,u}} {p : PivotalStructure (C := D.Obj)}
local notation "S" => MTC.Modular.categoricalS
local notation "dim" => MTC.Modular.simpleDimension

/-- Pivotal dimensions of dual labels are conjugates. -/
theorem simpleDimension_dual_eq_star (i : Fin (rank D)) :
    dim D p (dualIndex D i) = star (dim D p i) :=
  (pivotalDimension_iso p (rightDualLabelIso D i)).symm.trans
    (MTC.Center.Induction.pivotalDimension_simple_dual_conj p i)

/-- The conjugate pivotal dimensions restricted to a set of simple labels. -/
def pivotalRegularVector (D : BraidedFusionCategory.{v,u})
    (p : PivotalStructure (C := D.Obj)) (A : Finset (Fin (rank D)))
    (i : Fin (rank D)) : ℂ :=
  if i ∈ A then star (dim D p i) else 0

/-- Every entry of the pivotal regular vector is nonzero precisely on its set. -/
theorem pivotalRegularVector_ne_zero_iff {A : Finset (Fin (rank D))} {i : Fin (rank D)} :
    pivotalRegularVector D p A i ≠ 0 ↔ i ∈ A := by
  classical
  simp [pivotalRegularVector, MTC.Modular.simpleDimension_ne_zero]

/-- The pivotal regular vector is an eigenvector with the actual pivotal
simple dimension as eigenvalue. -/
theorem pivotal_regular_vector_fusion_eigenvector
    {A : Finset (Fin (rank D))} (hA : IsDualFusionClosed D A)
    (a : A) (k : Fin (rank D)) :
    (∑ i, (fusionCoeff D a i k : ℂ) * pivotalRegularVector D p A i) =
      dim D p a * pivotalRegularVector D p A k := by
  classical
  by_cases hk : k ∈ A
  · have heq :
        (∑ i, (fusionCoeff D a i k : ℂ) * pivotalRegularVector D p A i) =
        ∑ i, (fusionCoeff D (dualIndex D a) k i : ℂ) * star (dim D p i) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [fusionCoeff_dual_symmetry D a k i]
      by_cases hiA : i ∈ A
      · simp [pivotalRegularVector, hiA]
      · simp [pivotalRegularVector, hiA,
          hA.fusion.fusionCoeff_eq_zero (a := ⟨_, hA.dual _ a.2⟩) (b := ⟨k, hk⟩) (k := ⟨i, hiA⟩)]
    rw [heq]
    have hchar := pivotalDimension_character D p (dualIndex D a) k
    have hstar := congrArg (starRingEnd ℂ) hchar
    simpa only [map_sum, map_mul, map_natCast, starRingEnd_apply,
      simpleDimension_dual_eq_star, star_star, pivotalRegularVector, hk, ↓reduceIte] using hstar.symm
  · simpa [pivotalRegularVector, hk] using
      fusionClosed_sum_eq_zero (fun i ↦ star (dim D p i)) hA.fusion (a := a) (k := ⟨k, hk⟩)

/-- A pivotal-eigenvector Fourier transform vanishes where the S-centrality
test fails, with no FP-valued or spherical hypothesis. -/
theorem pivotal_fourier_eq_zero_of_fusion_eigenvector
    {f : Fin (rank D) → ℂ} {a y : Fin (rank D)}
    (heigen : ∀ k, ∑ i, (fusionCoeff D a i k : ℂ) * f i = dim D p a * f k)
    (hne : S D p a y ≠ dim D p a * dim D p y) : sFourier D p f y = 0 := by
  let χ (i : Fin (rank D)) := S D p i y / dim D p y
  let T : ℂ := ∑ i, χ i * f i
  have ht : χ a * T = dim D p a * T :=
    sum_mul_eigenvalue (fun i k ↦ (fusionCoeff D a i k : ℂ)) χ f
      (fun i ↦ MTC.Modular.categoricalS_verlinde D p a i y) heigen
  have hχ : χ a ≠ dim D p a := fun h ↦ hne <| by
    simpa [χ] using (div_eq_iff (MTC.Modular.simpleDimension_ne_zero D p y)).mp h
  apply (div_eq_zero_iff.mp ?_).resolve_right (MTC.Modular.simpleDimension_ne_zero D p y)
  simpa only [sFourier, T, χ, div_mul_eq_mul_div, ← Finset.sum_div,
    MTC.Modular.categoricalS_symmetric D p y] using (mul_eq_mul_right_iff.mp ht).resolve_left hχ

/-- The pivotal regular vector's S-transform is supported on a set containing
the numerical centralizer of its fusion-closed set. -/
theorem pivotalRegularVector_fourier_support
    {A : Finset (Fin (rank D))} {core : Set (Fin (rank D))}
    (hA : IsDualFusionClosed D A) (hcore : sCentralizer D p (↑A : Set _) ⊆ core) :
    FourierSupportedOn D p (pivotalRegularVector D p A) core := fun y hy ↦
  let ⟨a, ha, hne⟩ : ∃ a ∈ A, ¬sCentralizes D p a y := by
    simpa only [sCentralizer, Set.mem_ofPred_eq, Finset.mem_coe, not_forall, exists_prop] using
      (show y ∉ sCentralizer D p (↑A : Set _) from fun h ↦ hy (hcore h))
  pivotal_fourier_eq_zero_of_fusion_eigenvector
    (pivotal_regular_vector_fusion_eigenvector hA ⟨a, ha⟩) hne

/-- Hermitian S-orthogonality inverts the S-transform without assuming that
the pivotal dimensions are real. -/
theorem pivotal_sFourier_inversion
    (horth : ∀ x k : Fin (rank D),
      (∑ y, star (S D p y x) * S D p y k) =
        if x = k then globalDimension D else 0)
    (f : Fin (rank D) → ℂ) (x : Fin (rank D)) :
    (∑ y, star (S D p y x) * sFourier D p f y) = globalDimension D * f x := by
  classical
  simp only [sFourier, Finset.mul_sum, ← mul_assoc]
  rw [Finset.sum_comm]
  simp only [← Finset.sum_mul, horth, ite_mul, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, ↓reduceIte]

/-- General pivotal Fourier support implies the corresponding double
centralizer inclusion when the categorical S-matrix satisfies the displayed
Hermitian orthogonality relation. -/
theorem pivotal_doubleCentralizer_of_fourier_support
    (horth : ∀ x k : Fin (rank D),
      (∑ y, star (S D p y x) * S D p y k) =
        if x = k then globalDimension D else 0)
    {f : Fin (rank D) → ℂ} {core generated : Set (Fin (rank D))}
    (hunit : f (unitIndex D) ≠ 0) (hgenerated : Function.support f ⊆ generated)
    (hsupport : FourierSupportedOn D p f core) : sCentralizer D p core ⊆ generated := by
  intro x hx
  apply hgenerated
  have heq : (∑ y, star (S D p y x) * sFourier D p f y) =
      star (dim D p x) * ∑ y, star (S D p y (unitIndex D)) * sFourier D p f y :=
    sum_mul_eq_mul_sum_of_supported core _ _ _ _ hsupport fun y hy ↦ by
      rw [hx y hy, MTC.Modular.categoricalS_unit, star_mul]
  rw [pivotal_sFourier_inversion horth f x,
    pivotal_sFourier_inversion horth f (unitIndex D)] at heq
  change f x ≠ 0
  intro hz
  rw [hz, mul_zero] at heq
  exact (mul_ne_zero (star_ne_zero.mpr (MTC.Modular.simpleDimension_ne_zero D p x))
    (mul_ne_zero (MTC.Center.Induction.globalDimension_ne_zero_of_pivotal p) hunit)) heq.symm

/-- General pivotal numerical double-centralizer theorem for a fusion
subcategory's label set, conditional only on Hermitian S-orthogonality. -/
theorem pivotal_doubleCentralizer_of_fusion_closed
    (horth : ∀ x k : Fin (rank D),
      (∑ y, star (S D p y x) * S D p y k) =
        if x = k then globalDimension D else 0)
    {A : Finset (Fin (rank D))} {core : Set (Fin (rank D))}
    (hA : IsFusionSubring D A) (hcore : sCentralizer D p (↑A : Set _) ⊆ core) :
    sCentralizer D p core ⊆ (↑A : Set _) := by
  apply pivotal_doubleCentralizer_of_fourier_support horth
    (f := pivotalRegularVector D p A)
  · exact pivotalRegularVector_ne_zero_iff.mpr hA.unit
  · intro x hx
    exact pivotalRegularVector_ne_zero_iff.mp hx
  · exact pivotalRegularVector_fourier_support hA.toIsDualFusionClosed hcore

end MTC.Center.Braid
end
