module
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Tactic
public import PropertyF.Ground.Fusion.SpectralIntegral
public import PropertyF.Ground.Dimensions.DimensionField
public import PropertyF.Arithmetic

/-! # Galois fixedness and integrality

A positive ratio and the centre's rigidity witness rule out smaller Galois
conjugates. A real algebraic integer fixed by every complex automorphism is an
integer, yielding the arithmetic descent used in the final theorem. -/

section

@[expose] public noncomputable section

namespace PropertyF

/-- The final strict-inequality contradiction, including the inverse Galois
transport of the positive dimension ratio. Lemma 3.2 supplies `hrigidity`.
No assertion about all conjugates is assumed here. -/
theorem galois_dimension_contradiction {δ δσ δτ f d : ℝ}
    {σ : ℂ ≃+* ℂ} (hδ : 0 < δ) (hδσ : 0 < δσ) (hlt : δσ < δ)
    (hδτ : σ (δτ : ℂ) = (δ : ℂ)) (hσδ : σ (δ : ℂ) = (δσ : ℂ))
    (hσf : σ (f : ℂ) = (d : ℂ)) (hratio : f * δτ = δ)
    (hf : 1 ≤ f) (hrigidity : f = |d|) : False := by
  have ht := congrArg σ (show (f : ℂ) * (δτ : ℂ) = (δ : ℂ) by exact_mod_cast hratio)
  rw [map_mul, hδτ, hσδ, hσf] at ht
  have hreal : d * δ = δσ := by exact_mod_cast ht
  rw [abs_of_pos (by nlinarith : 0 < d)] at hrigidity
  nlinarith

end PropertyF

namespace PropertyF.Ground

/-- The squared Galois dimension identity gives the positive ratio used by
the paper. No Galois automorphism is assumed to preserve square roots. -/
theorem positive_ratio_of_galois_square {τ : ℂ ≃+* ℂ} {δ b f : ℝ}
    (hδ : 0 < δ) (hb : 0 < b) (hf : 0 < f)
    (hτ : τ (δ : ℂ) = (b : ℂ))
    (hG : τ ((δ : ℂ) ^ 2) = (δ : ℂ) ^ 2 / (f : ℂ) ^ 2) :
    f * b = δ := by
  rw [map_pow, hτ] at hG
  have hR : b ^ 2 = δ ^ 2 / f ^ 2 := by exact_mod_cast hG
  have hR' := (eq_div_iff (pow_ne_zero 2 (ne_of_gt hf))).mp hR
  nlinarith [sq_nonneg (f * b - δ), mul_pos hf hb]

/-- The numerical witness supplied by a Galois-unit column. -/
abbrev HasGaloisDimensionWitness (σ : ℂ ≃+* ℂ) (δ b : ℝ) : Prop :=
  ∃ f d : ℝ, σ (f : ℂ) = (d : ℂ) ∧ f * b = δ ∧ 1 ≤ f ∧ f = |d|

/-- If real conjugates are bounded above by δ and the centre/rigidity witness
exists for each strictly smaller conjugate, every conjugate equals δ. -/
theorem galois_fixed_of_smaller_conjugate_witness (δ : ℝ) (hδ : 0 < δ)
    (hConjugates : ∀ σ : ℂ ≃+* ℂ, ∃ a : ℝ,
      0 < a ∧ a ≤ δ ∧ σ (δ : ℂ) = (a : ℂ))
    (hWitness : ∀ (σ : ℂ ≃+* ℂ) (a b : ℝ),
      0 < a → a < δ → σ (δ : ℂ) = (a : ℂ) →
      σ.symm (δ : ℂ) = (b : ℂ) →
      HasGaloisDimensionWitness σ δ b) :
    ∀ σ : ℂ ≃+* ℂ, σ (δ : ℂ) = (δ : ℂ) := by
  intro σ
  obtain ⟨a, ha, hale, haeq⟩ := hConjugates σ
  obtain ⟨b, _, _, hbeq⟩ := hConjugates σ.symm
  by_cases heq : a = δ
  · simpa [heq] using haeq
  · have halt : a < δ := lt_of_le_of_ne hale heq
    have hback : σ (b : ℂ) = (δ : ℂ) := by
      rw [← hbeq]
      exact σ.apply_symm_apply _
    obtain ⟨f, d, hσf, hratio, hf, hrigidity⟩ := hWitness σ a b ha halt haeq hbeq
    exact (galois_dimension_contradiction (σ := σ) hδ ha halt hback haeq hσf hratio hf hrigidity).elim

end PropertyF.Ground
end
end

/-! The final arithmetic descent for the frozen target, without a dimension
field or standard-input hypothesis. -/

@[expose] public noncomputable section
namespace PropertyF.Ground
universe v u

/-- A real algebraic integer fixed by every complex automorphism is an integer. -/
theorem weaklyIntegral_of_galois_fixed {δ : ℝ} (hδr : IsIntegral ℤ δ)
    (hfixed : ∀ τ : ℂ ≃+* ℂ, τ (δ : ℂ) = (δ : ℂ)) : WeaklyIntegral δ := by
  have hδ := (isIntegral_algebraMap_iff (R := ℤ) (A := ℝ) (B := ℂ)).mpr hδr
  let K := Dimensions.dimensionNormalField (δ : ℂ)
  have h := Dimensions.finite_galois_normal_field (δ : ℂ) (hδ.tower_top (A := ℚ))
  let : FiniteDimensional ℚ K := h.2.1
  let : IsGalois ℚ K := h.2.2
  let x : K := ⟨(δ : ℂ), h.1⟩
  obtain ⟨z, hz⟩ := integer_of_galois_fixed (x := x)
    ((isIntegral_algebraMap_iff (R := ℤ) (A := K) (B := ℂ)).mp (by simpa [x] using hδ)) fun σ ↦ by
      obtain ⟨τ, hτ⟩ := Dimensions.extend_complex_automorphism K.toSubfield σ.toRingEquiv
      exact Subtype.ext ((hτ x).symm.trans (hfixed τ))
  exact ⟨z, by simpa [x] using congrArg Complex.re (congrArg (fun y : K ↦ (y : ℂ)) hz)⟩

end PropertyF.Ground
