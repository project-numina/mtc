module
public import PropertyF.BlockTrace
public import PropertyF.BraidAlgebra

/-! The matrix saturation step of three-strand rigidity, without a model bundle. -/

@[expose] public noncomputable section
open scoped BigOperators
namespace PropertyF.Ground.Calculus

/-- In explicit matrix blocks, a sharp trace bound and a saturating braid
force the squares of the two braid generators to coincide. The trace bound,
nonzero weights, and the trace value are explicit hypotheses, rather than a
hypothesis structure. -/
theorem braid_squares_equal_of_saturation (B : PropertyF.Blocks)
    (w : Fin B.count → ℝ) (a b : B.Algebraˣ) (d f : ℝ)
    (hf : 0 < f) (hw : ∀ r, w r ≠ 0)
    (ha : B.IsUnitary (a : B.Algebra)) (hb : B.IsUnitary (b : B.Algebra))
    (hbraid : a * b * a = b * a * b)
    (hbound : ∀ u : B.Algebra, B.IsUnitary u → ‖B.trace w u‖ ≤ |d| * f ^ 2)
    (htrace : B.trace w ((a ^ 2 * b ^ 2 : B.Algebraˣ) : B.Algebra) = (d : ℂ) * f ^ 2) :
    a ^ 2 = b ^ 2 := by
  have hunit : B.IsUnitary ((a ^ 2 * b ^ 2 : B.Algebraˣ) : B.Algebra) := by
    intro r
    have h := (Matrix.unitaryGroup (Fin (B.size r)) ℂ).mul_mem
      ((Matrix.unitaryGroup (Fin (B.size r)) ℂ).mul_mem (ha r) (ha r))
      ((Matrix.unitaryGroup (Fin (B.size r)) ℂ).mul_mem (hb r) (hb r))
    simpa [pow_two] using h
  have hmass : B.mass w ≤ |d| * f ^ 2 := by
    have h := hbound (B.signElement w) (B.signElement_unitary w)
    rw [B.trace_signElement] at h
    have hm : 0 ≤ B.mass w :=
      Finset.sum_nonneg (fun r _ => mul_nonneg (abs_nonneg _) (Nat.cast_nonneg _))
    simpa [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hm] using h
  have hsaturate : ‖B.trace w ((a ^ 2 * b ^ 2 : B.Algebraˣ) : B.Algebra)‖ = B.mass w := by
    apply le_antisymm (B.norm_trace_le w hunit)
    rw [htrace]
    simpa [norm_pow, abs_of_pos hf] using hmass
  have hc := B.central_of_saturation w hw hunit hsaturate
  apply PropertyF.squares_eq_of_central_product a b hbraid
  apply Units.ext
  exact hc b

end PropertyF.Ground.Calculus
