module
public import PropertyF.Ground.Target

/-!
# Squared dimensions of a weakly integral fusion category

Status: solved
Source: Drinfeld–Gelaki–Nikshych–Ostrik, arXiv:0906.0620, Proposition 2.18(ii).
Declaration: MTC.Conjectures.Fusion.weaklyIntegral_squares

Every simple object of a weakly integral fusion category has integer squared
Frobenius–Perron dimension. This arithmetic constraint is useful for detecting
possible counterexamples and filtering data. Ising categories show that the
unsquared dimensions need not be integers. The statement is restricted here
to the braided categories represented by the existing ground interface.

The literature theorem uses the standard FP dimension; identifying the frozen
spectral-radius definition with it remains a separate proof obligation.
-/

@[expose] public noncomputable section
namespace MTC.Conjectures.Fusion
open PropertyF PropertyF.Ground
universe v u

/-- Weak integrality forces integral squared simple dimensions. -/
theorem weaklyIntegral_squares (C : BraidedFusionCategory.{v,u})
    (h : WeaklyIntegral (globalFPDimension C)) (i : Fin (rank C)) :
    ∃ n : ℤ, (fpSimple C i) ^ 2 = (n : ℝ) := by
  sorry

/-- Conversely, integral squared simple dimensions give weak integrality. -/
theorem squares_imply_weaklyIntegral (C : BraidedFusionCategory.{v,u})
    (h : ∀ i : Fin (rank C), ∃ n : ℤ, (fpSimple C i) ^ 2 = (n : ℝ)) :
    WeaklyIntegral (globalFPDimension C) := by
  classical
  refine ⟨∑ i, Classical.choose (h i), ?_⟩
  simp only [globalFPDimension, Int.cast_sum]
  exact Finset.sum_congr rfl (fun i _ => Classical.choose_spec (h i))

/-- The Ising dimension list has integer squares and total squared dimension four. -/
example : (1 : ℝ) ^ 2 + 1 ^ 2 + (Real.sqrt 2) ^ 2 = 4 := by
  rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

end MTC.Conjectures.Fusion
