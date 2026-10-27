module
public import PropertyF.GaloisSymmetry

/-! Numerical part of the paper's Galois fixedness argument, independent of
any of the old input structures. The remaining hypotheses describe the real
conjugate bounds and the numerical witness supplied by the centre and rigidity
arguments. -/

@[expose] public noncomputable section
namespace PropertyF.Ground

/-- The squared Galois dimension identity gives the positive ratio used by
the paper. No Galois automorphism is assumed to preserve square roots. -/
theorem positive_ratio_of_galois_square (τ : ℂ ≃+* ℂ) {δ b f : ℝ}
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
theorem galois_unit_self_entry (σ : ℂ ≃+* ℂ) {S : ℂ} {f d : ℝ}
    (hS : S = (f : ℂ) * σ.symm (f : ℂ))
    (hd : σ (f : ℂ) = (d : ℂ)) : σ S = (d : ℂ) * f := by
  rw [hS, map_mul, hd, σ.apply_symm_apply]

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
    exact (galois_dimension_contradiction σ hδ ha halt hback haeq hσf hratio hf hrigidity).elim

end PropertyF.Ground
