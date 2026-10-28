module
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Tactic

/-! Elementary integrality step for the exterior-power approach to symmetric
fusion categories. The categorical construction of exterior powers and their
nonnegative dimensions is not assumed or established in this module. -/
@[expose] public noncomputable section
open scoped BigOperators
namespace PropertyF.Ground.Centre

/-- A nonnegative real number whose falling factorials are all nonnegative is
an integer. In a pseudo-unitary symmetric setting, the intended application is
that these products are factorial multiples of exterior-power dimensions. -/
theorem integral_of_nonnegative_falling_factorials {d : ℝ} (hd : 0 ≤ d)
    (h : ∀ n : ℕ, 0 ≤ ∏ k ∈ Finset.range n, (d - (k : ℝ))) :
    ∃ m : ℕ, d = m := by
  let m := ⌊d⌋₊
  by_cases heq : d = (m : ℝ)
  · exact ⟨m, heq⟩
  · have hm : (m : ℝ) < d := lt_of_le_of_ne (Nat.floor_le hd) (Ne.symm heq)
    have hm' : d < (m : ℝ) + 1 := Nat.lt_floor_add_one d
    have hprod : 0 < ∏ k ∈ Finset.range (m + 1), (d - (k : ℝ)) := by
      apply Finset.prod_pos
      intro k hk
      have hk' : k ≤ m := by simpa using (Finset.mem_range.mp hk)
      have hk'' : (k : ℝ) ≤ (m : ℝ) := by exact_mod_cast hk'
      linarith
    have hneg : d - ((m + 1 : ℕ) : ℝ) < 0 := by push_cast; linarith
    have hn := h (m + 2)
    rw [show m + 2 = (m + 1) + 1 by omega, Finset.prod_range_succ] at hn
    exact False.elim ((not_le_of_gt (mul_neg_of_pos_of_neg hprod hneg)) hn)

end PropertyF.Ground.Centre
