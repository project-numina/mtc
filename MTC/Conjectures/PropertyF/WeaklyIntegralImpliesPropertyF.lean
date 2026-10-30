module
public import MTC.PropertyF.Statement

open MTC.Braided

/-!
# Weak integrality implies property F

All braid group representations arising from a weakly integral braided fusion
category should have finite image. This is the direction relevant to finding a
counterexample on weakly integral Atlas entries. Green–Nikshych establish it
for weakly group-theoretical braided fusion categories (arXiv:1911.02633,
Theorem 7.2). Weak integrality refers to the global FP dimension, not its square.

Status: open
Source: Naidu–Rowell, arXiv:0903.4157, Conjecture 2.3
Declaration: MTC.Conjectures.PropertyF.weaklyIntegral_implies_propertyF
-/

@[expose] public noncomputable section
open MTC MTC
namespace MTC.Conjectures.PropertyF
universe v u

/-- The weak-integrality-to-property-F direction. -/
theorem weaklyIntegral_implies_propertyF (C : BraidedFusionCategory.{v,u})
    (h : WeaklyIntegral (globalFPDimension C)) : HasPropertyF C.Obj := by
  sorry

end MTC.Conjectures.PropertyF
