module
public import Mathlib.Tactic
public import Mathlib.Analysis.Complex.Basic

/-!
# Three-strand braid algebra

A central product of squares forces equality of squares under the braid relation.
-/

@[expose] public section
namespace PropertyF

/-- The braid-algebra step on page 4. Centrality is only needed against `a` and
`b`, so the statement applies to the generated subgroup as well as to an algebra. -/
theorem squares_eq_of_central_product {G : Type*} [Group G] (a b : G)
    (hbraid : a * b * a = b * a * b)
    (hb : Commute (a ^ 2 * b ^ 2) b) : a ^ 2 = b ^ 2 := by
  have hAb : Commute (a ^ 2) b := by
    apply mul_right_cancel (b := b ^ 2)
    calc
      a ^ 2 * b * b ^ 2 = (a ^ 2 * b ^ 2) * b := by group
      _ = b * (a ^ 2 * b ^ 2) := hb.eq
      _ = b * a ^ 2 * b ^ 2 := by group
  have hconj : (a * b) * a * (a * b)⁻¹ = b := by
    calc
      _ = (a * b * a) * (b⁻¹ * a⁻¹) := by group
      _ = (b * a * b) * (b⁻¹ * a⁻¹) := by rw [hbraid]
      _ = b := by group
  have hAc : Commute (a ^ 2) (a * b) := (Commute.refl a).pow_left 2 |>.mul_right hAb
  calc
    a ^ 2 = (a * b) * a ^ 2 * (a * b)⁻¹ := by
      rw [← hAc.eq]; group
    _ = ((a * b) * a * (a * b)⁻¹) ^ 2 := by simp only [pow_two]; group
    _ = b ^ 2 := by rw [hconj]

/-- The last scalar calculation of Lemma 3.2, including negative `d`. -/
theorem fp_eq_abs_dim_of_finite_order {d f : ℝ} (hd : d ≠ 0) (hf : 0 < f)
    (h : ∃ n : ℕ, n ≠ 0 ∧ (f / d : ℂ) ^ n = 1) : f = |d| := by
  obtain ⟨n, hn, heq⟩ := h
  have hh := Complex.norm_eq_one_of_pow_eq_one heq hn
  have hdiv : f / |d| = 1 := by simpa [norm_div, abs_of_pos hf] using hh
  exact (div_eq_one_iff_eq (abs_ne_zero.mpr hd)).mp hdiv

end PropertyF
