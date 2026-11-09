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

/-- Any FP column has the intrinsic global-dimension identity. -/
theorem fp_column_globalDimension
    (hdet : (categoricalS C p).det ≠ 0) (j : Fin (rank C))
    (hj : ∀ i, categoricalS C p i j = simpleDimension C p j * (fpSimple C i : ℂ)) :
    globalDimension C = ((‖simpleDimension C p j‖ ^ 2 : ℝ) : ℂ) *
      (globalFPDimension C : ℂ) := by
  have hgram : (∑ i, star (categoricalS C p i j) * categoricalS C p i j) = globalDimension C := by
    change (∑ i, starRingEnd ℂ (categoricalS C p i j) * categoricalS C p i j) = _
    rw [categoricalS_column_length C p hdet j]
    simpa only [simpleDimension, starRingEnd_apply] using
      (MTC.Center.Induction.globalDimension_eq_sum_pivotal_conj_mul p).symm
  exact MTC.Center.Normalization.globalDimension_eq_norm_sq_mul_fp_of_gram_column
    (C := C) (j := j) p hj hgram

/-- The FP column and its intrinsic global-dimension identity, for an
arbitrary pivotal structure whose categorical S matrix is invertible. -/
theorem existsUnique_fp_column_globalDimension
    (hdet : (categoricalS C p).det ≠ 0) :
    ∃! j : Fin (rank C),
      (∀ i, categoricalS C p i j = simpleDimension C p j * (fpSimple C i : ℂ)) ∧
      globalDimension C = ((‖simpleDimension C p j‖ ^ 2 : ℝ) : ℂ) *
        (globalFPDimension C : ℂ) := by
  obtain ⟨j, hj, hu⟩ := existsUnique_fp_column C p hdet
  exact ⟨j, ⟨hj, fp_column_globalDimension C p hdet j hj⟩, fun k hk ↦ hu k hk.1⟩

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
