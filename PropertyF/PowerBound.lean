module
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Tactic

@[expose] public section
namespace PropertyF

/-- The elementary unbounded-powers step in Lemma 3.1. No limit of roots is needed. -/
theorem le_of_power_bounds {a b c : ℝ} (ha : 0 < a)
    (h : ∀ k : ℕ, b ^ (k + 1) ≤ a ^ (k + 1) * c) : b ≤ a := by
  by_contra hb
  have hab : a < b := lt_of_not_ge hb
  have hr : 1 < b / a := (lt_div_iff₀ ha).2 (by simpa using hab)
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (max c 1) hr
  have hbound : (b / a) ^ n ≤ max c 1 := by
    cases n with
    | zero => simp
    | succ k =>
      rw [div_pow]
      apply (div_le_iff₀ (pow_pos ha _)).2
      exact (h k).trans (by
        simpa [mul_comm] using mul_le_mul_of_nonneg_left (le_max_left c 1)
          (pow_nonneg ha.le (k + 1)))
  exact (not_lt_of_ge hbound) hn

/-- Numerical conclusion of the overlapping-block argument (paper, Lemma 3.1).
`h` is the inequality obtained after tracing the overlapping product. -/
theorem trace_bound_of_overlap {t d f : ℝ} {m : ℕ}
    (hd : d ≠ 0) (hf : 0 < f)
    (h : ∀ k : ℕ, t ^ (k + 1) ≤ |d| ^ k * f ^ ((k + 1) * (m - 1) + 1)) :
    t ≤ |d| * f ^ (m - 1) := by
  have hd' : 0 < |d| := abs_pos.mpr hd
  apply le_of_power_bounds (mul_pos hd' (pow_pos hf _)) (c := f / |d|)
  intro k
  calc
    t ^ (k + 1) ≤ |d| ^ k * f ^ ((k + 1) * (m - 1) + 1) := h k
    _ = (|d| * f ^ (m - 1)) ^ (k + 1) * (f / |d|) := by
      rw [mul_pow, pow_succ |d|, pow_add, pow_one, mul_comm (k + 1), pow_mul]
      field_simp

end PropertyF
