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
    have h := hb.symm.mul_right ((Commute.refl b).pow_right 2).inv_right
    simpa using h.symm
  have hconj : (a * b) * a * (a * b)⁻¹ = b := by
    rw [mul_inv_rev, hbraid]
    group
  have hAc : Commute (a ^ 2) (a * b) := (Commute.refl a).pow_left 2 |>.mul_right hAb
  calc
    a ^ 2 = (a * b) * a ^ 2 * (a * b)⁻¹ := hAc.symm.mul_inv_cancel.symm
    _ = ((a * b) * a * (a * b)⁻¹) ^ 2 := by simp only [pow_two]; group
    _ = b ^ 2 := by rw [hconj]

/-- The last scalar calculation of Lemma 3.2, including negative `d`. -/
theorem fp_eq_abs_dim_of_finite_order {d f : ℝ} (hd : d ≠ 0) (hf : 0 < f)
    (h : ∃ n : ℕ, n ≠ 0 ∧ (f / d : ℂ) ^ n = 1) : f = |d| :=
  let ⟨_, hn, heq⟩ := h
  (div_eq_one_iff_eq (abs_ne_zero.mpr hd)).mp (by
    simpa [norm_div, abs_of_pos hf] using Complex.norm_eq_one_of_pow_eq_one heq hn)

end PropertyF
