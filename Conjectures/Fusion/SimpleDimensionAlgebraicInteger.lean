module
public import PropertyF.Ground.Target

/-!
# Simple FP dimensions are algebraic integers

Status: solved
Source: Drinfeld–Gelaki–Nikshych–Ostrik, arXiv:0906.0620, Section 2.4.1;
Etingof–Nikshych–Ostrik, arXiv:math/0203060, Section 8.
Declaration: MTC.Conjectures.Fusion.simpleDimension_algebraicInteger

The Frobenius–Perron dimension of each simple object is an algebraic integer.
The fusion matrix has integer entries; identifying its spectral radius with
its Perron eigenvalue is a key step. This gives exact arithmetic constraints
for modular data and is a prerequisite for divisibility statements.
The frozen spectral-radius definition still requires comparison with the
standard construction in the cited literature.
-/

@[expose] public noncomputable section
namespace MTC.Conjectures.Fusion
open PropertyF.Ground
universe v u

/-- Simple FP dimensions are integral over the integers. -/
theorem simpleDimension_algebraicInteger (C : BraidedFusionCategory.{v,u})
    (i : Fin (rank C)) : IsIntegral ℤ (fpSimple C i) := by
  sorry

/-- The numerical dimension of an invertible simple is integral. -/
example : IsIntegral ℤ (1 : ℝ) := isIntegral_one

end MTC.Conjectures.Fusion
