module
public import PropertyF.Ground.Target

/-!
# Odd weak dimension implies integrality

Status: solved
Source: Drinfeld–Gelaki–Nikshych–Ostrik, arXiv:0906.0620, Corollary 2.22.
Declaration: MTC.Conjectures.Fusion.oddDimension_integral

If the global Frobenius–Perron dimension is an odd integer, every simple
Frobenius–Perron dimension is an integer. The result uses the elementary
2-group grading of weakly integral fusion categories; even-dimensional Ising
categories illustrate why oddness matters. We state the braided special case.

The frozen spectral-radius definition must still be identified with the
standard FP dimension before the source theorem can be applied in Lean.
-/

@[expose] public noncomputable section
namespace MTC.Conjectures.Fusion
open PropertyF.Ground
universe v u

/-- Odd global FP dimension forces integer simple FP dimensions. -/
theorem oddDimension_integral (C : BraidedFusionCategory.{v,u})
    (n : ℤ) (hn : Odd n) (h : globalFPDimension C = (n : ℝ))
    (i : Fin (rank C)) : ∃ m : ℤ, fpSimple C i = (m : ℝ) := by
  sorry

/-- Dimension one satisfies the arithmetic hypothesis. -/
example : Odd (1 : ℤ) := ⟨0, by norm_num⟩

end MTC.Conjectures.Fusion
