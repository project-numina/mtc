module
public import PropertyF.GaloisSymmetry

/-! Numerical part of the paper's Galois fixedness argument, independent of
any of the old input structures. The remaining hypotheses describe the real
conjugate bounds and the numerical witness supplied by the centre and rigidity
arguments. -/

@[expose] public noncomputable section
namespace PropertyF.Ground

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
