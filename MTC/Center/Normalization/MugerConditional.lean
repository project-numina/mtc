module
public import MTC.Center.Normalization.SymmetricConditional

open MTC.Fusion MTC.Braided MTC.CategoryTheory.Dimensions
open MTC.Center.Induction MTC.PropertyF.Reduction MTC.Modular

/-! # Conditional normalization of the actual Müger centre

The explicit assumption is S invertibility for the actual Drinfeld centre of
the actual Müger category. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace MTC.Center.Normalization
universe v u
set_option backward.isDefEq.respectTransparency false
variable (C : BraidedFusionCategory.{v,u})
variable [RigidCategory (Center (bundledMuger C).Obj)]
variable [IsFusionCategory (Center (bundledMuger C).Obj)]

/-- Symmetric Müger pseudo-unitarity follows from invertibility of the actual
Drinfeld-centre categorical S matrix. -/
theorem muger_pseudoUnitary_of_center_S_invertible
    (hdet : (categoricalS (bundledCenter (bundledMuger C))
        (liftedPivotalStructure
          (canonicalSymmetricPivotal (D := (bundledMuger C).Obj) (mugerBraiding_symmetric C))
          (pivotalComponentsCentral_proved
            (canonicalSymmetricPivotal (D := (bundledMuger C).Obj) (mugerBraiding_symmetric C))))).det ≠ 0) :
    PseudoUnitary (bundledMuger C) :=
  symmetric_pseudoUnitary_of_center_S_invertible (bundledMuger C) (mugerBraiding_symmetric C) hdet

/-- Adjoint positivity gives the normalized pivotal structure when the
Drinfeld centre of the actual Müger category has invertible categorical S. -/
theorem normalize_pivotal_of_adjoint_positivity_and_muger_center_S_invertible
    (p : PivotalStructure (C := C.Obj))
    (hpositive : ∀ i, MTC.Center.Transparent (simples C i) → IsAdjointLabel C i →
      ∃ r : ℝ, 0 < r ∧ pivotalDimension C p (simples C i) = r)
    (hdet : (categoricalS (bundledCenter (bundledMuger C))
        (liftedPivotalStructure
          (canonicalSymmetricPivotal (D := (bundledMuger C).Obj) (mugerBraiding_symmetric C))
          (pivotalComponentsCentral_proved
            (canonicalSymmetricPivotal (D := (bundledMuger C).Obj) (mugerBraiding_symmetric C))))).det ≠ 0) :
    ∃ q : PivotalStructure (C := C.Obj), ∀ i,
      MTC.Center.Transparent (simples C i) →
      pivotalDimension C q (simples C i) = (fpSimple C i : ℂ) :=
  normalize_pivotal_of_muger_pseudoUnitary_and_adjoint_positivity C p
    (muger_pseudoUnitary_of_center_S_invertible C hdet) hpositive

end MTC.Center.Normalization
end
