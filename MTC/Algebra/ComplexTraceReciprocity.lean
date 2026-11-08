module
public import MTC.Algebra.ComplexBlockTrace

/-! Conjugate reciprocity for complex-weighted traces of unitary blocks. -/

open scoped BigOperators ComplexConjugate

@[expose] public noncomputable section
namespace MTC.Algebra.Blocks

/-- If all weights share a conjugate phase, the weighted trace of the
adjoint has the same phase times the conjugate original trace. -/
theorem complexTrace_star_of_weight_phase (B : Blocks) (w : Fin B.count → ℂ)
    (ξ : ℂ) (hphase : ∀ r, w r = ξ * star (w r)) (u : B.Matrices) :
    B.complexTrace w (star u) = ξ * star (B.complexTrace w u) := by
  simp only [complexTrace, Pi.star_apply, Matrix.star_eq_conjTranspose,
    Matrix.trace_conjTranspose]
  change (∑ r, w r * star (u r).trace) =
    ξ * (starRingEnd ℂ) (∑ r, w r * (u r).trace)
  rw [map_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  simp only [map_mul]
  conv_lhs => rw [hphase r]
  simp only [mul_assoc]
  rfl

/-- A unit-modulus common weight phase gives equal trace norms for a unitary
and its adjoint, with no nonzero-weight assumption. -/
theorem norm_complexTrace_star_of_weight_phase (B : Blocks) (w : Fin B.count → ℂ)
    (ξ : ℂ) (hξ : ‖ξ‖ = 1) (hphase : ∀ r, w r = ξ * star (w r))
    (u : B.Matrices) : ‖B.complexTrace w (star u)‖ = ‖B.complexTrace w u‖ := by
  rw [complexTrace_star_of_weight_phase B w ξ hphase, norm_mul, hξ, norm_star, one_mul]

end MTC.Algebra.Blocks
