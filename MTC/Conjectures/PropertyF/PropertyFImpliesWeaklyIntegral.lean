module
public import PropertyF.Ground.Final

/-!
# Property F implies weak integrality

The global Frobenius–Perron dimension of any braided fusion category with
property F should be an integer, without a pseudo-unitary conjugate assumption.
This is one direction of Naidu–Rowell. It is established by
`PropertyF.Ground.target` when a pseudo-unitary Galois conjugate exists.

Status: open
Source: Naidu–Rowell, arXiv:0903.4157, Conjecture 2.3
Declaration: MTC.Conjectures.PropertyF.propertyF_implies_weaklyIntegral
-/

@[expose] public noncomputable section
open PropertyF PropertyF.Ground
namespace MTC.Conjectures.PropertyF
universe v u

/-- The unrestricted property-F-to-weak-integrality direction. -/
theorem propertyF_implies_weaklyIntegral (C : BraidedFusionCategory.{v,u})
    (h : HasPropertyF C.Obj) : WeaklyIntegral (globalFPDimension C) := by
  sorry

/-- The established case, for comparison with the unrestricted statement. -/
theorem propertyF_implies_weaklyIntegral_of_conjugate (C : BraidedFusionCategory.{v,u})
    (h : HasPseudoUnitaryGaloisConjugate C) (hF : HasPropertyF C.Obj) :
    WeaklyIntegral (globalFPDimension C) :=
  PropertyF.Ground.target C h hF

end MTC.Conjectures.PropertyF
