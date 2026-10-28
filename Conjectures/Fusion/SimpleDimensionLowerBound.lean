module
public import PropertyF.Ground.Target

/-!
# Lower bound on simple FP dimensions

Status: solved
Source: Drinfeld–Gelaki–Nikshych–Ostrik, arXiv:0906.0620, Section 2.4.1.
Declaration: MTC.Conjectures.Fusion.simpleDimension_lowerBound

Every simple object has Frobenius–Perron dimension at least one. Equality
holds for invertible objects. The bound is a useful sanity check for candidate
fusion rules and provides a lower bound for global FP dimension in terms of
rank. The statement is restricted to the frozen braided category interface;
the equivalence of its spectral radius with the usual FP dimension is pending.
-/

@[expose] public noncomputable section
namespace MTC.Conjectures.Fusion
open PropertyF.Ground
universe v u

/-- A simple object has FP dimension at least one. -/
theorem simpleDimension_lowerBound (C : BraidedFusionCategory.{v,u})
    (i : Fin (rank C)) : 1 ≤ fpSimple C i := by
  sorry

example : (1 : ℝ) ≤ 1 := le_rfl

end MTC.Conjectures.Fusion
