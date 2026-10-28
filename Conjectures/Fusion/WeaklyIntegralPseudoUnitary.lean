module
public import PropertyF.Ground.Target

/-!
# Weak integrality implies pseudo-unitarity

Status: solved
Source: Drinfeld–Gelaki–Nikshych–Ostrik, arXiv:0906.0620, Proposition 2.18(i).
Declaration: MTC.Conjectures.Fusion.weaklyIntegral_pseudoUnitary

A weakly integral fusion category is pseudo-unitary. This is a fundamental
bridge between arithmetic and categorical dimensions. The source applies to
all fusion categories; the present target only covers braided ones.

The ground interface computes squared norms using a specific double-dual
isomorphism and an inverse scalar map. Its documented identification with the
standard dimension remains to be proved; the literature result alone does not
establish this exact Lean encoding.
-/

@[expose] public noncomputable section
namespace MTC.Conjectures.Fusion
open PropertyF PropertyF.Ground
universe v u

/-- Weak integrality implies pseudo-unitarity in the ground interface. -/
theorem weaklyIntegral_pseudoUnitary (C : BraidedFusionCategory.{v,u})
    (h : WeaklyIntegral (globalFPDimension C)) : PseudoUnitary C := by
  sorry

end MTC.Conjectures.Fusion
