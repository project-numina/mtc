module
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.Tactic

@[expose] public section
namespace PropertyF

/-- The scalar calculation in the spherical-structure descent remark (page 2).
Algebraicity of `d` and the nonzero quantum trace `q` implies algebraicity of
the pivotal scalar `t`. Neither the equation nor nonvanishing is suppressed. -/
theorem pivotal_scalar_algebraic {d q t : ℂ} (hd : IsAlgebraic ℚ d)
    (hq : IsAlgebraic ℚ q) (hq0 : q ≠ 0) (htrace : d = t * q) : IsAlgebraic ℚ t := by
  have ht : t = d / q := (eq_div_iff hq0).mpr htrace.symm
  rw [ht]
  rw [div_eq_mul_inv]
  exact hd.mul hq.inv

/-- Finitely many algebraic pivotal scalars fit in a finite extension. Combined
with finite number-field descent of the underlying category [ENO 2.30, 2.33],
this justifies transporting the chosen spherical structure. -/
theorem pivotal_scalars_finite_extension {ι : Type*} [Finite ι] (t : ι → ℂ)
    (ht : ∀ i, IsAlgebraic ℚ (t i)) :
    FiniteDimensional ℚ (IntermediateField.adjoin ℚ (Set.range t)) := by
  apply IntermediateField.finiteDimensional_adjoin
  rintro x ⟨i, rfl⟩
  exact (ht i).isIntegral

end PropertyF
