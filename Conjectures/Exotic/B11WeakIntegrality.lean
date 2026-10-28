module
public import MTC.FRSymbols.B11Dimension
public import MTC.PropertyF.PseudoUnitary

/-!
# The rank-11 Atlas example is not weakly integral

The global Frobenius–Perron dimension of the unitary categorification of
B11-00119 is not an integer. Thus this particular example cannot falsify the
weakly-integral-implies-property-F direction. Together with the existing
property-F theorem and pseudo-unitarity, it also rules out property F for a
category whose global FP dimension is this value. It does not settle the
weak integrality or property F status of other exotics or the rank-12 orbit.

Status: solved
Source: The Anyon Atlas, arXiv:2610.25439, Section 5 and equations (5.2)–(5.3); exact corollary verified by scripts/propf/exotic_b11.py.
Declaration: MTC.Conjectures.Exotic.b11_not_weaklyIntegral

For a direct exact proof, the cited script forms the sum of squares from the
paper's vacuum row and reduces it modulo the irreducible polynomial Φ₃₅. The
remainder has degree 23 with leading coefficient -560, so it cannot represent
a rational number. The dimension is approximately 1964.59077737424; this
decimal is illustrative, not the proof. The calculation has not yet been
formalized in Lean.
-/

@[expose] public noncomputable section
namespace MTC.Conjectures.Exotic

universe v u

/-- The exact B11-00119 dimension is not an integer. -/
theorem b11_not_weaklyIntegral :
    ¬ PropertyF.WeaklyIntegral MTC.FRSymbols.AtlasB11.globalDimension := by
  sorry

/-- The stated dimension is strictly positive, independently of the conjecture. -/
theorem b11_dimension_pos : 0 < MTC.FRSymbols.AtlasB11.globalDimension := by
  linarith [MTC.FRSymbols.AtlasB11.one_le_globalDimension]

/-- Conditional categorical consequence, independent of the unproved Lean
statement above: a pseudo-unitary category with this nonintegral global
FP dimension cannot have property F. -/
theorem b11_not_propertyF_of_nonintegral
    (C : PropertyF.Ground.BraidedFusionCategory.{v, u})
    (hpu : PropertyF.Ground.PseudoUnitary C)
    (hdim : PropertyF.Ground.globalFPDimension C = MTC.FRSymbols.AtlasB11.globalDimension)
    (hni : ¬ PropertyF.WeaklyIntegral MTC.FRSymbols.AtlasB11.globalDimension) :
    ¬ PropertyF.HasPropertyF C.Obj := by
  intro hF
  apply hni
  rw [← hdim]
  exact MTC.PropertyF.weaklyIntegral_of_propertyF_of_pseudoUnitary C hpu hF

end MTC.Conjectures.Exotic
