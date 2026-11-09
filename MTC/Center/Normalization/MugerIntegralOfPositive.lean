module
public import MTC.Center.Normalization.MugerFPIntegral
public import MTC.Center.Normalization.MugerNormalization

open MTC.Fusion MTC.Braided MTC.CategoryTheory.Dimensions

/-! # Müger FP integrality under transparent-adjoint positivity -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace MTC.Center.Normalization
universe v u
variable (C : BraidedFusionCategory.{v,u})

/-- Every object of the actual Müger fusion category has integer FP dimension
under the manuscript's transparent-adjoint positivity hypothesis. -/
theorem muger_fpDimension_integer_of_adjoint_positivity
    (p : PivotalStructure (C := C.Obj))
    (hpositive : ∀ i, MTC.Center.Transparent (simples C i) → IsAdjointLabel C i →
      ∃ r : ℝ, 0 < r ∧ pivotalDimension C p (simples C i) = r)
    (X : MugerCategory C) : ∃ n : ℕ, fpDimension (bundledMuger C) X = (n : ℝ) :=
  muger_fpDimension_integer_of_pseudoUnitary C
    (muger_pseudoUnitary_of_adjoint_positivity C p hpositive) X

/-- Every transparent ambient object has integer FP dimension under the same
hypothesis. -/
theorem transparent_fpDimension_integer_of_adjoint_positivity
    (p : PivotalStructure (C := C.Obj))
    (hpositive : ∀ i, MTC.Center.Transparent (simples C i) → IsAdjointLabel C i →
      ∃ r : ℝ, 0 < r ∧ pivotalDimension C p (simples C i) = r)
    (X : C.Obj) (hX : MTC.Center.Transparent X) :
    ∃ n : ℕ, fpDimension C X = (n : ℝ) :=
  transparent_fpDimension_integer_of_muger_pseudoUnitary C p
    (muger_pseudoUnitary_of_adjoint_positivity C p hpositive) X hX

end MTC.Center.Normalization
end
