module
public import PropertyF.Ground.CentreIntegrate.CycleColoring
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Data.Nat.Factorial.BigOperators
public import Mathlib.Basic.Complex.Basic
open scoped BigOperators
open Equiv Polynomial
@[expose] public noncomputable section
namespace PropertyF.Ground.CentreIntegrate

/-- The signed cycle-count polynomial. -/
def cyclePoly (n : ℕ) : Polynomial ℂ :=
  ∑ σ : Perm (Fin n), Polynomial.C ((Perm.sign σ : ℤ) : ℂ) * Polynomial.X ^ countCycles σ

/-- The polynomial with roots 0 through n-1. -/
def fallingPoly (n : ℕ) : Polynomial ℂ :=
  ∏ k ∈ Finset.range n, (Polynomial.X - Polynomial.C (k : ℂ))

/-- The signed cycle-count polynomial is the falling factorial polynomial. -/
theorem cyclePoly_eq_fallingPoly (n : ℕ) : cyclePoly n = fallingPoly n := by
  classical
  apply Polynomial.eq_of_infinite_eval_eq
  apply Set.Infinite.mono (s := Set.range (fun k : ℕ => ((n + k : ℕ) : ℂ)))
  · rintro _ ⟨k, rfl⟩
    change Polynomial.eval ((n + k : ℕ) : ℂ) (cyclePoly n) = _
    simp only [cyclePoly, fallingPoly, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
      Polynomial.eval_X, Polynomial.eval_prod, Polynomial.eval_sub]
    have hnat := signed_cycle_count_nat n (n + k)
    have hcast : (∑ σ : Perm (Fin n), ((Perm.sign σ : ℤ) : ℂ) *
        (((n + k : ℕ) : ℂ) ^ countCycles σ)) = ((Nat.descFactorial (n + k) n : ℕ) : ℂ) := by
      exact_mod_cast hnat
    rw [hcast, Nat.descFactorial_eq_prod_range, Nat.cast_prod]
    apply Finset.prod_congr rfl
    intro i hi
    rw [Nat.cast_sub]
    exact Nat.le_trans (Nat.le_of_lt (Finset.mem_range.mp hi)) (Nat.le_add_right n k)
  · apply Set.infinite_range_of_injective
    intro i j h
    have hn : n + i = n + j := Nat.cast_injective h
    exact Nat.add_left_cancel hn

/-- Signed cycle-count identity over ℂ, including fixed points as cycles. -/
theorem signed_cycle_count (n : ℕ) (x : ℂ) :
    (∑ σ : Perm (Fin n), ((Perm.sign σ : ℤ) : ℂ) * x ^ countCycles σ) =
      ∏ k ∈ Finset.range n, (x - (k : ℂ)) := by
  have h := congrArg (Polynomial.eval x) (cyclePoly_eq_fallingPoly n)
  simpa only [cyclePoly, fallingPoly, Polynomial.eval_finsetSum, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_prod,
    Polynomial.eval_sub] using h

end PropertyF.Ground.CentreIntegrate
