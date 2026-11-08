module
public import MTC.PropertyF.Pivotal.SOrthogonality
public import MTC.Center.Induction.PivotalFusion

/-! # Frobenius–Perron column and intrinsic global dimension

For an arbitrary pivotal structure with invertible categorical S matrix, the
unique FP column yields the intrinsic global dimension identity. -/

@[expose] public noncomputable section
open MTC.Fusion MTC.Modular
open scoped BigOperators
namespace MTC.PropertyF.Pivotal
universe v u
variable (C : BraidedFusionCategory.{v,u})
variable (p : MTC.CategoryTheory.Dimensions.PivotalStructure (C := C.Obj))

/-- The FP column and its intrinsic global-dimension identity, for an
arbitrary pivotal structure whose categorical S matrix is invertible. -/
theorem existsUnique_fp_column_globalDimension
    (hdet : (categoricalS C p).det ≠ 0) :
    ∃! j : Fin (rank C),
      (∀ i, categoricalS C p i j = simpleDimension C p j * (fpSimple C i : ℂ)) ∧
      globalDimension C = ((‖simpleDimension C p j‖ ^ 2 : ℝ) : ℂ) *
        (globalFPDimension C : ℂ) := by
  obtain ⟨j, hj, hu⟩ := existsUnique_fp_column C p hdet
  obtain ⟨k, hk, hdim⟩ := fp_column_dimension_identity C p hdet
  have hkj : k = j := hu k hk
  subst k
  have hglobal : globalDimension C =
      ∑ i, starRingEnd ℂ (simpleDimension C p i) * simpleDimension C p i := by
    rw [MTC.Center.Induction.globalDimension_eq_sum_pivotal_norm_sq p]
    simp only [Complex.ofReal_sum, Complex.ofReal_pow]
    apply Finset.sum_congr rfl
    intro i _
    simpa only [simpleDimension, Complex.star_def, mul_comm] using
      (Complex.mul_conj' (simpleDimension C p i)).symm
  refine ⟨j, ⟨hj, ?_⟩, fun k hk ↦ hu k hk.1⟩
  rw [hglobal, hdim]
  congr 1
  simpa only [Complex.ofReal_pow, Complex.star_def, mul_comm] using
    (Complex.mul_conj' (simpleDimension C p j))

end MTC.PropertyF.Pivotal

@[expose] public noncomputable section
open MTC.Fusion MTC.Modular MTC.CategoryTheory.Dimensions
open scoped BigOperators
namespace MTC.PropertyF.Pivotal
universe v u
variable (C : BraidedFusionCategory.{v,u})
variable (p : PivotalStructure (C := C.Obj))

/-- The simple pivotal dimensions are bounded in norm by FP dimensions. -/
theorem simpleDimension_norm_le_fp (i : Fin (rank C)) :
    ‖simpleDimension C p i‖ ≤ fpSimple C i := by
  simpa only [simpleDimension] using character_norm_le_fpSimple
    (i₀ := unitIndex C) ((pivotalDimension_unitIndex C p).symm ▸ one_ne_zero)
    (pivotalDimension_character C p) i

include p in
/-- The global dimension of a pivotal braided fusion category is bounded by
its global FP dimension. -/
theorem globalDimension_re_le_globalFPDimension :
    (globalDimension C).re ≤ globalFPDimension C := by
  rw [MTC.Center.Induction.globalDimension_eq_sum_pivotal_norm_sq p]
  simp only [Complex.ofReal_re, globalFPDimension]
  apply Finset.sum_le_sum
  intro i _
  exact pow_le_pow_left₀ (norm_nonneg _) (simpleDimension_norm_le_fp C p i) 2

/-- The numerical step in the nondegenerate argument: if the pivotal
dimension of the FP label saturates its FP bound, then the category is
pseudo-unitary and that label has FP dimension one. -/
theorem pseudoUnitary_of_fp_column_saturation
    (j : Fin (rank C))
    (hdim : globalDimension C = ((‖simpleDimension C p j‖ ^ 2 : ℝ) : ℂ) *
      (globalFPDimension C : ℂ))
    (hsat : ‖simpleDimension C p j‖ = fpSimple C j) :
    PseudoUnitary C ∧ fpSimple C j = 1 := by
  have hf : 0 < globalFPDimension C :=
    lt_of_lt_of_le zero_lt_one (one_le_globalFPDimension C)
  have hj : 1 ≤ fpSimple C j := one_le_fpSimple j
  have hbound := globalDimension_re_le_globalFPDimension C p
  rw [hdim] at hbound
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero] at hbound
  rw [hsat] at hbound
  have hsq : fpSimple C j ^ 2 ≤ 1 := by nlinarith
  have hjone : fpSimple C j = 1 := by nlinarith
  refine ⟨?_, hjone⟩
  rw [PseudoUnitary, hdim, hsat, hjone]
  norm_num

end MTC.PropertyF.Pivotal
