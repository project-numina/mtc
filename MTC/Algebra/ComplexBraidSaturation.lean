module
public import MTC.Algebra.ComplexBlockTrace

/-!
# Saturation for complex-weighted three-strand braid blocks
-/

open scoped BigOperators
open MTC.Braided

@[expose] public noncomputable section
namespace MTC.Algebra.Blocks

/-- Saturation of the weighted unitary bound forces the two braid squares to
agree on each block of nonzero weight, even when other weights vanish. -/
theorem braid_squares_equal_on_support (B : Blocks) (w : Fin B.count → ℂ)
    {a b : B.Matricesˣ} (ha : B.IsUnitary (a : B.Matrices))
    (hb : B.IsUnitary (b : B.Matrices)) (hbraid : a * b * a = b * a * b)
    (hsat : ‖B.complexTrace w ((a ^ 2 * b ^ 2 : B.Matricesˣ) : B.Matrices)‖ =
      B.complexMass w) {r : Fin B.count} (hw : w r ≠ 0) :
    ((a ^ 2 : B.Matricesˣ) : B.Matrices) r = ((b ^ 2 : B.Matricesˣ) : B.Matrices) r := by
  let ev := Pi.evalMonoidHom (fun r => Matrix (Fin (B.size r)) (Fin (B.size r)) ℂ) r
  let a' := Units.map ev a
  let b' := Units.map ev b
  have hunit : B.IsUnitary ((a ^ 2 * b ^ 2 : B.Matricesˣ) : B.Matrices) := by
    simpa only [Units.val_mul, Units.val_pow_eq_pow_val] using
      (unitary B.Matrices).mul_mem ((unitary B.Matrices).pow_mem ha 2)
        ((unitary B.Matrices).pow_mem hb 2)
  have hc : Commute (a' ^ 2 * b' ^ 2) b' := by
    apply Units.ext
    change (((a ^ 2 * b ^ 2 : B.Matricesˣ) : B.Matrices) r * (b : B.Matrices) r) =
      ((b : B.Matrices) r * ((a ^ 2 * b ^ 2 : B.Matricesˣ) : B.Matrices) r)
    exact B.complex_block_central_of_saturation w hunit hsat r hw (b : B.Matrices)
  have heq : a' ^ 2 = b' ^ 2 := squares_eq_of_central_product a' b'
    (by simpa only [a', b', map_mul] using congrArg (Units.map ev) hbraid) hc
  exact congrArg (fun z : (Matrix (Fin (B.size r)) (Fin (B.size r)) ℂ)ˣ =>
    (z : Matrix (Fin (B.size r)) (Fin (B.size r)) ℂ)) heq

/-- Under the same hypotheses, the weighted trace of the mixed-sign braid is
exactly the weighted trace of the identity, regardless of zero-weight blocks. -/
theorem mixed_braid_trace_eq_one_of_saturation (B : Blocks) (w : Fin B.count → ℂ)
    {a b : B.Matricesˣ} (ha : B.IsUnitary (a : B.Matrices))
    (hb : B.IsUnitary (b : B.Matrices)) (hbraid : a * b * a = b * a * b)
    (hsat : ‖B.complexTrace w ((a ^ 2 * b ^ 2 : B.Matricesˣ) : B.Matrices)‖ =
      B.complexMass w) :
    B.complexTrace w ((a ^ 2 * (b ^ 2)⁻¹ : B.Matricesˣ) : B.Matrices) =
      B.complexTrace w 1 := by
  apply Finset.sum_congr rfl
  intro r _
  by_cases hw : w r = 0
  · simp [hw]
  · have h : (((a ^ 2 * (b ^ 2)⁻¹ : B.Matricesˣ) : B.Matrices) r) = 1 := by
      change (((a ^ 2 : B.Matricesˣ) : B.Matrices) r) *
        ((((b ^ 2)⁻¹ : B.Matricesˣ) : B.Matrices) r) = 1
      rw [B.braid_squares_equal_on_support w ha hb hbraid hsat hw]
      have hv := congrArg (fun u : B.Matricesˣ => (u : B.Matrices))
        (mul_inv_cancel (b ^ 2))
      simpa only [Units.val_mul, Units.val_one, Pi.mul_apply, Pi.one_apply] using congrFun hv r
    simp only [Pi.one_apply, h]

end MTC.Algebra.Blocks
