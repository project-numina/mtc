module
public import MTC.PropertyF.Statement

/-!
# Naidu–Rowell property F conjecture

A braided fusion category has finite braid group images on every tensor power
of every object exactly when its global Frobenius–Perron dimension is integral.
This would connect braid group representations to a numerical invariant.
The direction from property F is known when a pseudo-unitary Galois conjugate
exists; the converse holds for weakly group-theoretical categories by
Green–Nikshych, arXiv:1911.02633, Theorem 7.2.

Status: open
Source: Naidu–Rowell, arXiv:0903.4157, Conjecture 2.3
Declaration: MTC.Conjectures.PropertyF.naiduRowell
-/

@[expose] public noncomputable section
open MTC MTC
namespace MTC.Conjectures.PropertyF
universe v u

/-- The full Naidu–Rowell conjecture. -/
theorem naiduRowell (C : BraidedFusionCategory.{v,u}) :
    HasPropertyF C.Obj ↔ WeaklyIntegral (globalFPDimension C) := by
  sorry

end MTC.Conjectures.PropertyF
