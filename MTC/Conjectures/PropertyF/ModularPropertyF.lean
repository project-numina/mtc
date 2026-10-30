module
public import MTC.Modular.SMatrix
public import MTC.PropertyF.Theorem

open MTC.PropertyF.Reduction

open MTC.Fusion

open MTC.Braided

/-!
# Property F for modular fusion categories

A nondegenerate spherical braided fusion category is conjectured to have
property F exactly when its global Frobenius–Perron dimension is integral.
This restriction of the Naidu–Rowell conjecture is relevant to modular
categories; it concerns actual categorical braiding, not merely numerical
modular data. The forward implication is proved when a pseudo-unitary Galois
conjugate exists. The bridge from numerical modular data to this categorical
predicate is not assumed.

Status: open
Source: Naidu–Rowell, arXiv:0903.4157, Conjecture 2.3
Declaration: MTC.Conjectures.PropertyF.modular_propertyF
-/

@[expose] public noncomputable section
open MTC MTC.Modular MTC.PropertyF
namespace MTC.Conjectures.PropertyF
universe v u

/-- Naidu–Rowell for categories with nondegenerate spherical structure. -/
theorem modular_propertyF (C : BraidedFusionCategory.{v,u})
    (h : HasNondegenerateSphericalStructure C) :
    HasPropertyF C.Obj ↔ WeaklyIntegral (globalFPDimension C) := by
  sorry

/-- In the presence of a pseudo-unitary conjugate the forward implication holds. -/
theorem modular_propertyF_forward_of_conjugate (C : BraidedFusionCategory.{v,u})
    (h : HasPseudoUnitaryGaloisConjugate C) (hF : HasPropertyF C.Obj) :
    WeaklyIntegral (globalFPDimension C) :=
  MTC.PropertyF.weaklyIntegral_of_propertyF C h hF

end MTC.Conjectures.PropertyF
