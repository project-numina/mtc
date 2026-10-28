module
public import PropertyF.Ground.Target

/-!
# Global FP dimension is an algebraic integer

Status: solved
Source: Drinfeld–Gelaki–Nikshych–Ostrik, arXiv:0906.0620, Section 2.4.1.
Declaration: MTC.Conjectures.Fusion.globalDimension_algebraicInteger

The global Frobenius–Perron dimension is an algebraic integer. It is the sum
of the squares of the simple FP dimensions. This supplies the arithmetic
setting for comparing dimensions and for interpreting divisibility.
The identification of the frozen spectral-radius definition with the standard
FP dimension is still a separate proof obligation.
-/

@[expose] public noncomputable section
namespace MTC.Conjectures.Fusion
open PropertyF.Ground
universe v u

/-- The global FP dimension is integral over the integers. -/
theorem globalDimension_algebraicInteger (C : BraidedFusionCategory.{v,u}) :
    IsIntegral ℤ (globalFPDimension C) := by
  sorry

example : IsIntegral ℤ (1 : ℝ) := isIntegral_one

end MTC.Conjectures.Fusion
