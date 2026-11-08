module
public import Mathlib.Analysis.SpecialFunctions.Log.Summable
public import Mathlib.Analysis.PSeries
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Tactic

/-! # Analytic bounds for paired generalized binomials -/

@[expose] public noncomputable section
open scoped BigOperators
open Filter
namespace MTC.Center.Normalization

/-- The Euler-type product with reciprocal-square factors converges for every
complex parameter. -/
theorem pairedEulerProduct_converges (z : ℂ) :
    ∃ b : ℂ, Tendsto (fun n : ℕ ↦ ∏ k ∈ Finset.range n,
      (1 - z ^ 2 / (((k + 1 : ℕ) : ℂ) ^ 2))) atTop (nhds b) := by
  have hseries : Summable (fun n : ℕ ↦ 1 / ((n : ℝ) ^ 2)) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num)
  have hshift := (summable_nat_add_iff 1).mpr hseries
  have hnorm : Summable (fun n : ℕ ↦ ‖z ^ 2 / (((n + 1 : ℕ) : ℂ) ^ 2)‖) := by
    convert hshift.mul_left ‖z ^ 2‖ using 1
    funext n
    simp only [norm_div, norm_pow, Complex.norm_natCast]
    ring
  have hp := (multipliable_one_sub_of_summable hnorm).hasProd.tendsto_prod_nat
  exact ⟨_, hp⟩

/-- Dividing the convergent product by a quadratic factor tends to zero. -/
theorem pairedEulerProduct_div_sq_tendsto_zero (z : ℂ) :
    Tendsto (fun n : ℕ ↦ z ^ 2 / (((n + 1 : ℕ) : ℂ) ^ 2) *
      ∏ k ∈ Finset.range n, (1 - z ^ 2 / (((k + 1 : ℕ) : ℂ) ^ 2))) atTop (nhds 0) := by
  obtain ⟨b, hb⟩ := pairedEulerProduct_converges z
  have hinv : Tendsto (fun n : ℕ ↦ 1 / ((n : ℂ) + 1)) atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hz := ((tendsto_const_nhds (x := z ^ 2)).mul (hinv.pow 2)).mul hb
  convert hz using 1
  · funext n
    simp only [Nat.cast_add, Nat.cast_one]
    simp [div_eq_mul_inv, inv_pow]
  · simp


/-- The product of the falling and rising generalized binomials. -/
def pairedBinomial (z : ℂ) (n : ℕ) : ℂ :=
  (∏ k ∈ Finset.range n, (z ^ 2 - (k : ℂ) ^ 2)) / ((n.factorial : ℂ) ^ 2)

/-- The paired binomials satisfy their elementary one-step recurrence. -/
theorem pairedBinomial_succ (z : ℂ) (n : ℕ) :
    pairedBinomial z (n + 1) = pairedBinomial z n *
      (z ^ 2 - (n : ℂ) ^ 2) / (((n + 1 : ℕ) : ℂ) ^ 2) := by
  have hf : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  have hn : (((n + 1 : ℕ) : ℂ)) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  simp only [pairedBinomial, Finset.prod_range_succ, Nat.factorial_succ, Nat.cast_mul]
  field_simp [hf, hn]

/-- A paired binomial is a quadratic reciprocal times a convergent Euler product. -/
theorem pairedBinomial_euler (z : ℂ) (n : ℕ) :
    pairedBinomial z (n + 1) = (-1 : ℂ) ^ n *
      (z ^ 2 / (((n + 1 : ℕ) : ℂ) ^ 2) *
        ∏ k ∈ Finset.range n, (1 - z ^ 2 / (((k + 1 : ℕ) : ℂ) ^ 2))) := by
  induction n with
  | zero => simp [pairedBinomial]
  | succ n ih =>
    rw [pairedBinomial_succ, ih, Finset.prod_range_succ, pow_succ]
    have hn : (((n + 1 : ℕ) : ℂ)) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
    have hn2 : (((n + 1 + 1 : ℕ) : ℂ)) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (n + 1)
    field_simp [hn, hn2]
    ring


/-- The paired generalized binomials tend to zero for every complex parameter. -/
theorem pairedBinomial_tendsto_zero (z : ℂ) :
    Tendsto (pairedBinomial z) atTop (nhds 0) := by
  apply (Filter.tendsto_add_atTop_iff_nat 1).mp
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have h := (pairedEulerProduct_div_sq_tendsto_zero z).norm
  simpa only [pairedBinomial_euler, norm_mul, norm_pow, norm_neg, norm_one, one_pow,
    one_mul, norm_zero] using h

end MTC.Center.Normalization
end
