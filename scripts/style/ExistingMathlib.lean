module
public import PropertyF.BraidAlgebra

-- The project theorem's hypotheses are ordered differently from Mathlib's.
-- This independent check proves the same proposition directly from Mathlib.
example {z : ℂ} {n : ℕ} (hn : n ≠ 0) (h : z ^ n = 1) : ‖z‖ = 1 :=
  Complex.norm_eq_one_of_pow_eq_one h hn
