module
public import PropertyF.Axioms

@[expose] public section
open scoped BigOperators
namespace PropertyF
namespace ModularData

/-- Proposition 2.1, equation (1). -/
theorem galois_unit_column (M : ModularData) (τ : ℂ ≃+* ℂ) (X : Fin M.rank) :
    M.S X (M.galoisLabel τ M.unit) =
      M.dimension (M.galoisLabel τ M.unit) * τ (M.dimension X) := by
  have h := M.galois_character τ X M.unit
  rw [M.S_unit, M.unit_dimension, div_one] at h
  exact (div_eq_iff (M.dimension_ne_zero _)).mp h.symm |>.trans (mul_comm _ _)

/-- The sum-of-squares calculation in the proof of Proposition 2.1. -/
lemma galois_unit_square (M : ModularData) (τ : ℂ ≃+* ℂ) :
    M.dimension (M.galoisLabel τ M.unit) ^ 2 * τ M.globalDimension =
      if M.galoisLabel τ M.unit = M.dual (M.galoisLabel τ M.unit)
      then M.globalDimension else 0 := by
  let Y := M.galoisLabel τ M.unit
  calc
    M.dimension Y ^ 2 * τ M.globalDimension =
        ∑ X, (M.dimension Y * τ (M.dimension X)) ^ 2 := by
      rw [M.global_eq, map_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro X _
      rw [map_pow, mul_pow]
    _ = ∑ X, M.S X Y ^ 2 := by
      apply Finset.sum_congr rfl
      intro X _
      rw [M.galois_unit_column τ X]
    _ = ∑ X, M.S Y X * M.S X Y := by
      apply Finset.sum_congr rfl
      intro X _
      rw [M.S_symmetric Y X, pow_two]
    _ = _ := M.S_square Y Y

/-- Proposition 2.1, self-duality. -/
theorem galois_unit_self_dual (M : ModularData) (τ : ℂ ≃+* ℂ) :
    M.galoisLabel τ M.unit = M.dual (M.galoisLabel τ M.unit) := by
  by_contra h
  have hzero := M.galois_unit_square τ
  rw [ite_eq_right h] at hzero
  exact mul_ne_zero (pow_ne_zero 2 (M.dimension_ne_zero _))
    (by simpa using τ.injective.ne M.global_ne_zero) hzero

/-- Avoid square-root/Galois-commutation issues: positivity uniquely selects
`f * τ(δ) = δ` from Proposition 2.1. This is page 5's displayed square-root step. -/
theorem positive_dimension_ratio (M : ModularData) (τ : ℂ ≃+* ℂ)
    {δ δτ f : ℝ} (hδ : 0 < δ) (hδτ : 0 < δτ) (hf : 0 < f)
    (hD : M.globalDimension = (δ : ℂ) ^ 2)
    (hτ : τ (δ : ℂ) = (δτ : ℂ))
    (hY : M.dimension (M.galoisLabel τ M.unit) = (f : ℂ)) : f * δτ = δ := by
  have h := M.galois_unit_square τ
  rw [ite_eq_left (M.galois_unit_self_dual τ), hD, hY, map_pow, hτ] at h
  have hreal : f ^ 2 * δτ ^ 2 = δ ^ 2 := by exact_mod_cast h
  have hprod : 0 < f * δτ := mul_pos hf hδτ
  nlinarith [sq_nonneg (f * δτ - δ)]

end ModularData

/-- The final strict-inequality contradiction, including the inverse Galois
transport of the positive dimension ratio. Lemma 3.2 supplies `hrigidity`.
No assertion about all conjugates is assumed here. -/
theorem galois_dimension_contradiction {δ δσ δτ f d : ℝ}
    (σ : ℂ ≃+* ℂ) (hδ : 0 < δ) (hδσ : 0 < δσ) (hlt : δσ < δ)
    (hδτ : σ (δτ : ℂ) = (δ : ℂ)) (hσδ : σ (δ : ℂ) = (δσ : ℂ))
    (hσf : σ (f : ℂ) = (d : ℂ)) (hratio : f * δτ = δ)
    (hf : 1 ≤ f) (hrigidity : f = |d|) : False := by
  have ht := congrArg σ (show (f : ℂ) * (δτ : ℂ) = (δ : ℂ) by exact_mod_cast hratio)
  rw [map_mul, hδτ, hσδ, hσf] at ht
  have hreal : d * δ = δσ := by exact_mod_cast ht
  have hd : 0 < d := by nlinarith
  have hdlt : d < 1 := by nlinarith
  rw [abs_of_pos hd] at hrigidity
  linarith

end PropertyF
