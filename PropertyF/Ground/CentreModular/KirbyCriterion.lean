module
public import PropertyF.Ground.Modular.SSquare

/-! A single Kirby-colour loop identity implies the full S-square identity
and nondegeneracy. The loop identity for the actual centre remains open. -/
@[expose] public noncomputable section
open scoped BigOperators
namespace PropertyF.Ground.CentreModular
open Modular

/-- The vacuum-column Kirby identity propagates to all S-square entries by
the categorical Verlinde identity and fusion reciprocity. -/
theorem categoricalS_square_of_kirby
    (C : BraidedFusionCategory) (p : Dimensions.PivotalStructure (C := C.Obj))
    (D : ℂ)
    (hkirby : ∀ k, (∑ z, simpleDimension C p z * categoricalS C p k z) =
      if k = unitIndex C then D else 0)
    (x y : Fin (rank C)) :
    (∑ z, categoricalS C p x z * categoricalS C p z y) =
      if x = dualIndex C y then D else 0 := by
  classical
  have hprod (z : Fin (rank C)) :
      categoricalS C p x z * categoricalS C p z y =
        ∑ k, (fusionCoeff C x y k : ℂ) *
          (simpleDimension C p z * categoricalS C p k z) := by
    rw [categoricalS_symmetric C p z y]
    have h := categoricalS_verlinde C p x y z
    have hd := simpleDimension_ne_zero C p z
    have h' := congrArg (fun a : ℂ => a * simpleDimension C p z ^ 2) h
    simp only [Finset.sum_mul] at h'
    have ht (k : Fin (rank C)) : (fusionCoeff C x y k : ℂ) *
        (categoricalS C p k z / simpleDimension C p z) * simpleDimension C p z ^ 2 =
        (fusionCoeff C x y k : ℂ) * (simpleDimension C p z * categoricalS C p k z) := by
      field_simp
    simp_rw [ht] at h'
    have hl : categoricalS C p x z / simpleDimension C p z *
        (categoricalS C p y z / simpleDimension C p z) * simpleDimension C p z ^ 2 =
        categoricalS C p x z * categoricalS C p y z := by
      field_simp
    rw [hl] at h'
    exact h'
  simp_rw [hprod]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, hkirby]
  rw [Finset.sum_eq_single (unitIndex C)]
  · simp only [ite_true]
    rw [fusionCoeff_reciprocity_labels, fusionCoeff_unit]
    split_ifs <;> simp_all
  · intro k _ hk
    simp [hk]
  · intro h
    exact (h (Finset.mem_univ _)).elim

/-- A nonzero Kirby vacuum-loop scalar suffices for invertibility of the
actual categorical S matrix. -/
theorem categoricalS_det_ne_zero_of_kirby
    (C : BraidedFusionCategory) (p : Dimensions.PivotalStructure (C := C.Obj))
    (D : ℂ) (hD : D ≠ 0)
    (hkirby : ∀ k, (∑ z, simpleDimension C p z * categoricalS C p k z) =
      if k = unitIndex C then D else 0) :
    (categoricalS C p).det ≠ 0 := by
  classical
  let S := categoricalS C p
  let B : Matrix (Fin (rank C)) (Fin (rank C)) ℂ :=
    fun x y => S x (dualIndex C y) / D
  have hSB : S * B = 1 := by
    ext x y
    rw [Matrix.mul_apply, Matrix.one_apply]
    change (∑ z, S x z * (S z (dualIndex C y) / D)) = _
    simp_rw [← mul_div_assoc]
    rw [← Finset.sum_div, categoricalS_square_of_kirby C p D hkirby,
      dualIndex_involutive C]
    split_ifs <;> simp [*]
  exact Matrix.det_ne_zero_of_right_inverse hSB

end PropertyF.Ground.CentreModular
