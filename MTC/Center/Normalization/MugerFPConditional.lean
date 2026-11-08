module
public import MTC.Center.Normalization.MugerFPIntegral

open MTC.Fusion MTC.Braided MTC.CategoryTheory.Dimensions
open MTC.Center.Induction MTC.PropertyF.Reduction MTC.Modular

/-! # Conditional FP integrality of the actual Müger category -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace MTC.Center.Normalization
universe v u
set_option backward.isDefEq.respectTransparency false
variable (C : BraidedFusionCategory.{v,u})
variable [RigidCategory (Center (bundledMuger C).Obj)]
variable [IsFusionCategory (Center (bundledMuger C).Obj)]

/-- Invertibility of the actual Drinfeld-centre S matrix implies that every
object of the actual Müger category has integer FP dimension. -/
theorem muger_fpDimension_integer_of_center_S_invertible
    (hdet : (categoricalS (bundledCenter (bundledMuger C))
        (liftedPivotalStructure
          (canonicalSymmetricPivotal (D := (bundledMuger C).Obj) (mugerBraiding_symmetric C))
          (pivotalComponentsCentral_proved
            (canonicalSymmetricPivotal (D := (bundledMuger C).Obj) (mugerBraiding_symmetric C))))).det ≠ 0)
    (X : MugerCategory C) : ∃ n : ℕ, fpDimension (bundledMuger C) X = (n : ℝ) :=
  muger_fpDimension_integer_of_pseudoUnitary C
    (muger_pseudoUnitary_of_center_S_invertible C hdet) X

end MTC.Center.Normalization
end
