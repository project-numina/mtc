module
public import PropertyF.Ground.Target

/-!
# Galois divisibility of simple squared norms

Status: solved
Source: Ostrik, arXiv:0810.3242, Theorem 1.8.
Declaration: MTC.Conjectures.Galois.squaredNorm_dNumber

In a braided fusion category the categorical squared norm of every simple is a
`d`-number: its ideal of algebraic integers is stable under Galois
conjugation. This condition restricts categorifications of fusion rings. The
corresponding claim for simple FP dimensions is an open question in the same
paper, while the nonbraided analogue can fail.

The source uses the standard squared norm, which must still be shown to agree
with the frozen `squaredNorm` constructed using `unitScalar` and a double-dual
isomorphism. Standard squared norms are nonzero; Lean's totalized division
means that positivity and nonzero facts must also be established separately.
-/

@[expose] public noncomputable section
namespace MTC.Conjectures.Galois
open PropertyF.Ground
universe v u

/-- Every Galois conjugate of a simple squared norm is divisible by it. -/
theorem squaredNorm_dNumber (C : BraidedFusionCategory.{v,u})
    (i : Fin (rank C)) (σ : ℂ ≃+* ℂ) :
    IsIntegral ℤ (σ (squaredNorm C (simples C i)) / squaredNorm C (simples C i)) := by
  sorry

end MTC.Conjectures.Galois
