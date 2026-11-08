module
public import MTC.PropertyF.Pivotal.SOrthogonality
public import MTC.Center.Braid.PivotalRegularSupport

/-! # General pivotal numerical double centralizers

Hermitian orthogonality follows from an invertible categorical S matrix,
without assuming real or FP-valued pivotal dimensions. -/

@[expose] public noncomputable section
open MTC.Fusion MTC.Modular MTC.CategoryTheory.Dimensions
open scoped BigOperators
namespace MTC.PropertyF.Pivotal
universe v u
variable (C : BraidedFusionCategory.{v,u}) (p : PivotalStructure (C := C.Obj))

/-- The intrinsic global dimension is the Hermitian square length of the
pivotal simple-dimension vector. -/
theorem globalDimension_eq_hermitian_sum :
    globalDimension C = ∑ i, star (simpleDimension C p i) * simpleDimension C p i := by
  rw [MTC.Center.Induction.globalDimension_eq_sum_pivotal_norm_sq p]
  simp only [Complex.ofReal_sum, Complex.ofReal_pow]
  apply Finset.sum_congr rfl
  intro i _
  simpa only [simpleDimension, Complex.star_def, mul_comm] using
    (Complex.mul_conj' (simpleDimension C p i)).symm

/-- The actual pivotal S matrix satisfies Hermitian orthogonality whenever it
is invertible. -/
theorem categoricalS_hermitian_orthogonality (hdet : (categoricalS C p).det ≠ 0)
    (x k : Fin (rank C)) :
    (∑ y, star (categoricalS C p y x) * categoricalS C p y k) =
      if x = k then globalDimension C else 0 := by
  by_cases h : x = k
  · subst k
    simp only [ite_true]
    rw [globalDimension_eq_hermitian_sum C p]
    simpa only [starRingEnd_apply] using categoricalS_column_length C p hdet x
  · simp only [h, ite_false]
    simpa only [starRingEnd_apply] using categoricalS_columns_orthogonal C p hdet h

/-- The numerical double-centralizer inclusion follows for any fusion-closed
set of labels in a category with invertible pivotal S matrix. -/
theorem pivotal_doubleCentralizer_of_invertibleS
    (hdet : (categoricalS C p).det ≠ 0)
    {A : Finset (Fin (rank C))} {core : Set (Fin (rank C))}
    (hA : MTC.Center.Braid.IsFusionSubring C A)
    (hcore : sCentralizer C p (↑A : Set _) ⊆ core) :
    sCentralizer C p core ⊆ (↑A : Set _) :=
  MTC.Center.Braid.pivotal_doubleCentralizer_of_fusion_closed
    (categoricalS_hermitian_orthogonality C p hdet) hA hcore

end MTC.PropertyF.Pivotal
