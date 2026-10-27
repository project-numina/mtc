module
public import PropertyF.BraidAlgebra

-- Check the former project theorem's hypothesis order against Mathlib's lemma.
example {z : ℂ} {n : ℕ} (hn : n ≠ 0) (h : z ^ n = 1) : ‖z‖ = 1 :=
  Complex.norm_eq_one_of_pow_eq_one h hn
