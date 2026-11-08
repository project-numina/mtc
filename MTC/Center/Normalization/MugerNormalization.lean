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

end MTC.Center.Normalization
end
