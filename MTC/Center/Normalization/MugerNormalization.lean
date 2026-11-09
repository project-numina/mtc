module
public import MTC.Center.Normalization.PositiveSubring
public import MTC.Center.Normalization.MugerObjectNormalization

open MTC.Fusion MTC.Braided MTC.CategoryTheory.Dimensions

/-! # Normalization on the whole Müger centre -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace MTC.Center.Normalization
universe v u
variable (C : BraidedFusionCategory.{v,u})

/-- Positivity on transparent adjoint simples yields an ambient pivotal
structure whose dimension agrees with FP dimension on every transparent
object. -/
theorem normalize_pivotal_all_transparent_of_adjoint_positivity
    (p : PivotalStructure (C := C.Obj))
    (hpositive : ∀ i, MTC.Center.Transparent (simples C i) → IsAdjointLabel C i →
      ∃ r : ℝ, 0 < r ∧ pivotalDimension C p (simples C i) = r) :
    ∃ q : PivotalStructure (C := C.Obj), ∀ X : C.Obj,
      MTC.Center.Transparent X → pivotalDimension C q X = (fpDimension C X : ℂ) := by
  obtain ⟨q, hq⟩ := normalize_pivotal_on_muger_of_adjoint_positivity_unconditional C p hpositive
  exact ⟨q, fun X hX => pivotalDimension_eq_fp_of_transparent C q hq X hX⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The actual Müger fusion category is pseudo-unitary whenever the ambient
pivotal structure is positive on transparent adjoint simples. -/
theorem muger_pseudoUnitary_of_adjoint_positivity
    (p : PivotalStructure (C := C.Obj))
    (hpositive : ∀ i, MTC.Center.Transparent (simples C i) → IsAdjointLabel C i →
      ∃ r : ℝ, 0 < r ∧ pivotalDimension C p (simples C i) = r) :
    PseudoUnitary (bundledMuger C) := by
  obtain ⟨q, hq⟩ := normalize_pivotal_all_transparent_of_adjoint_positivity C p hpositive
  let M := bundledMuger C
  let qM := mugerPivotal C q
  have hd (i : Fin (rank M)) : pivotalDimension M qM (simples M i) = (fpSimple M i : ℂ) := by
    let X : MugerCategory C := simples M i
    rw [muger_pivotalDimension_forget, hq X.obj X.property,
      muger_forget_fpDimension C X, fpDimension_simple]
  change globalDimension M = (globalFPDimension M : ℂ)
  rw [MTC.Center.Induction.globalDimension_eq_sum_pivotal_norm_sq qM]
  simp only [hd, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (fpSimple_pos M _), globalFPDimension]


end MTC.Center.Normalization
end
