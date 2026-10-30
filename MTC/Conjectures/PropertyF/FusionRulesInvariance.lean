module
public import MTC.PropertyF.FusionRules

/-!
# Property F and fusion rules

Does property F depend only on the based fusion ring? This would allow a
finite-image question to be decided from discrete fusion multiplicities. A
positive answer follows from Naidu–Rowell once FP dimensions and their sums are
shown invariant under fusion-rule isomorphisms. The question is not known in
general; `SameFusionRules` is independent of property F and is reflexive.

Status: open
Source: Naidu–Rowell, arXiv:0903.4157, Question 4.10
Declaration: MTC.Conjectures.PropertyF.propertyF_fusionRules_invariant
-/

@[expose] public noncomputable section
open PropertyF PropertyF.Ground MTC.PropertyF
namespace MTC.Conjectures.PropertyF
universe v u

/-- Property F is invariant under isomorphism of based fusion rings. -/
theorem propertyF_fusionRules_invariant (C D : BraidedFusionCategory.{v,u})
    (h : SameFusionRules C D) : HasPropertyF C.Obj ↔ HasPropertyF D.Obj := by
  sorry

/-- The question has the expected tautological self-comparison. -/
theorem propertyF_fusionRules_self (C : BraidedFusionCategory.{v,u}) :
    HasPropertyF C.Obj ↔ HasPropertyF C.Obj := Iff.rfl

end MTC.Conjectures.PropertyF
