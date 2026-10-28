module
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Tactic
public import PropertyF.Ground.Fusion.SpectralIntegral
public import PropertyF.Ground.Dimensions.DimensionField
public import PropertyF.Arithmetic

section
/-! Numerical part of the paper's Galois fixedness argument, independent of
any of the old input structures. The remaining hypotheses describe the real
conjugate bounds and the numerical witness supplied by the centre and rigidity
arguments. -/

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
  have hf0 : (f : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hf)
  rw [map_pow, hτ] at hG
  have hC : (f : ℂ) ^ 2 * (b : ℂ) ^ 2 = (δ : ℂ) ^ 2 := by
    have hh := (eq_div_iff (pow_ne_zero 2 hf0)).mp hG
    simpa only [mul_comm] using hh
  have hR : f ^ 2 * b ^ 2 = δ ^ 2 := by exact_mod_cast hC
  have hpos : 0 < f * b := mul_pos hf hb
  nlinarith [sq_nonneg (f * b - δ)]

/-- Transport the Galois-unit S entry back to the chosen conjugate. -/
theorem galois_unit_self_entry {σ : ℂ ≃+* ℂ} {S : ℂ} {f d : ℝ}
    (hS : S = (f : ℂ) * σ.symm (f : ℂ))
    (hd : σ (f : ℂ) = (d : ℂ)) : σ S = (d : ℂ) * f := by
  rw [hS, map_mul, hd, σ.apply_symm_apply]

/-- The modular global-dimension and unit-column identities, together with the
three-strand rigidity conclusion for the self-entry, give the witness required
by the final contradiction. -/
theorem center_witness_of_modular_and_rigidity {σ : ℂ ≃+* ℂ} {δ b f d : ℝ} {S : ℂ}
    (hδ : 0 < δ) (hb : 0 < b) (hf : 1 ≤ f)
    (hτ : σ.symm (δ : ℂ) = (b : ℂ))
    (hσf : σ (f : ℂ) = (d : ℂ))
    (hG : σ.symm ((δ : ℂ) ^ 2) = (δ : ℂ) ^ 2 / (f : ℂ) ^ 2)
    (hS : S = (f : ℂ) * σ.symm (f : ℂ))
    (hRigid : σ S = (d : ℂ) * f → f = |d|) :
    σ (f : ℂ) = (d : ℂ) ∧ f * b = δ ∧ 1 ≤ f ∧ f = |d| :=
  ⟨hσf, positive_ratio_of_galois_square (τ := σ.symm) hδ hb (lt_of_lt_of_le zero_lt_one hf) hτ hG,
    hf, hRigid (galois_unit_self_entry (σ := σ) hS hσf)⟩

/-- If real conjugates are bounded above by δ and the centre/rigidity witness
exists for each strictly smaller conjugate, every conjugate equals δ. -/
theorem galois_fixed_of_smaller_conjugate_witness (δ : ℝ) (hδ : 0 < δ)
    (hConjugates : ∀ σ : ℂ ≃+* ℂ, ∃ a : ℝ,
      0 < a ∧ a ≤ δ ∧ σ (δ : ℂ) = (a : ℂ))
    (hWitness : ∀ (σ : ℂ ≃+* ℂ) (a b : ℝ),
      0 < a → a < δ → σ (δ : ℂ) = (a : ℂ) →
      σ.symm (δ : ℂ) = (b : ℂ) →
      ∃ f d : ℝ, σ (f : ℂ) = (d : ℂ) ∧ f * b = δ ∧ 1 ≤ f ∧ f = |d|) :
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

/-- Once every complex automorphism fixes the global FP dimension, its
algebraic integrality forces it to be an integer. All normal-field and
extension data are constructed, not assumed. -/
theorem weaklyIntegral_of_globalFPDimension_fixed (C : BraidedFusionCategory.{v,u})
    (hfixed : ∀ τ : ℂ ≃+* ℂ,
      τ (globalFPDimension C : ℂ) = (globalFPDimension C : ℂ)) :
    WeaklyIntegral (globalFPDimension C) := by
  let δ := globalFPDimension C
  have hδ : IsIntegral ℤ (δ : ℂ) :=
    (isIntegral_algebraMap_iff (R := ℤ) (A := ℝ) (B := ℂ)).mpr
      (globalFPDimension_isIntegral C)
  let K := Dimensions.dimensionNormalField (δ : ℂ)
  have h := Dimensions.finite_galois_normal_field (δ : ℂ) (hδ.tower_top (A := ℚ))
  let : FiniteDimensional ℚ K := h.2.1
  let : IsGalois ℚ K := h.2.2
  let x : K := ⟨(δ : ℂ), h.1⟩
  have hx : IsIntegral ℤ x :=
    (isIntegral_algebraMap_iff (R := ℤ) (A := K) (B := ℂ)).mp (by simpa [x] using hδ)
  have hxfix : ∀ σ : K ≃ₐ[ℚ] K, σ x = x := by
    intro σ
    obtain ⟨τ, hτ⟩ := Dimensions.extend_complex_automorphism K.toSubfield σ.toRingEquiv
    apply Subtype.ext
    calc
      (σ x : ℂ) = τ (x : ℂ) := (hτ x).symm
      _ = (x : ℂ) := hfixed τ
  obtain ⟨z, hz⟩ := integer_of_galois_fixed hx hxfix
  refine ⟨z, ?_⟩
  have hz' := congrArg (fun y : K => (y : ℂ)) hz
  simpa [x, δ] using congrArg Complex.re hz'

end PropertyF.Ground
