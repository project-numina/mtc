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

variable {R K : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [Field K]

namespace PropertyF

/-- The final strict-inequality contradiction, including the inverse Galois
transport of the positive dimension ratio. Lemma 3.2 supplies `hrigidity`.
No assertion about all conjugates is assumed here. -/
theorem galois_dimension_contradiction {j : R →+* K} {δ δσ δτ f d : R}
    {σ : K ≃+* K} (hδ : 0 < δ) (hδσ : 0 < δσ) (hlt : δσ < δ)
    (hδτ : σ (j δτ) = j δ) (hσδ : σ (j δ) = j δσ) (hσf : σ (j f) = j d)
    (hratio : f * δτ = δ) (hf : 1 ≤ f) (hrigidity : f = |d|) : False := by
  have hreal : d * δ = δσ := j.injective <| by
    simpa only [map_mul, hδτ, hσδ, hσf] using congrArg σ (congrArg j hratio)
  nlinarith [abs_of_pos (show 0 < d by nlinarith)]

end PropertyF

namespace PropertyF.Ground

/-- The squared Galois dimension identity gives the positive ratio used by
the paper. No Galois automorphism is assumed to preserve square roots. -/
theorem positive_ratio_of_galois_square {j : R →+* K} {τ : K ≃+* K} {δ b f : R}
    (hδ : 0 < δ) (hb : 0 < b) (hf : 0 < f)
    (hτ : τ (j δ) = j b) (hG : τ (j δ ^ 2) = j δ ^ 2 / j f ^ 2) : f * b = δ := by
  refine (sq_eq_sq₀ (mul_pos hf hb).le hδ.le).mp (j.injective ?_)
  simpa only [map_pow, map_mul, mul_pow, mul_comm] using
    (eq_div_iff (pow_ne_zero 2 ((map_ne_zero j).2 (ne_of_gt hf)))).mp
      (by simpa only [map_pow, hτ] using hG)

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
  rcases lt_or_eq_of_le hale with halt | heq
  · obtain ⟨f, d, hσf, hratio, hf, hrigidity⟩ := hWitness σ a b ha halt haeq hbeq
    exact (galois_dimension_contradiction (j := algebraMap ℝ ℂ) (σ := σ) hδ ha halt
      (by
        change σ (b : ℂ) = (δ : ℂ)
        rw [← hbeq, σ.apply_symm_apply])
      haeq hσf hratio hf hrigidity).elim
  · simpa [heq] using haeq

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
    (hfixed : ∀ τ : ℂ ≃+* ℂ, τ (δ : ℂ) = (δ : ℂ)) : WeaklyIntegral δ :=
  let hδ := (isIntegral_algebraMap_iff (R := ℤ) (A := ℝ) (B := ℂ)).mpr hδr
  let K := Dimensions.dimensionNormalField (δ : ℂ)
  let ⟨hK, hfin, hgal⟩ := Dimensions.finite_galois_normal_field (δ : ℂ) (hδ.tower_top (A := ℚ))
  letI : FiniteDimensional ℚ K := hfin
  letI : IsGalois ℚ K := hgal
  let x : K := ⟨(δ : ℂ), hK⟩
  let ⟨z, hz⟩ := integer_of_galois_fixed (x := x)
    ((isIntegral_algebraMap_iff (R := ℤ) (A := K) (B := ℂ)).mp (by simpa [x] using hδ)) fun σ ↦ by
      obtain ⟨τ, hτ⟩ := Dimensions.extend_complex_automorphism K.toSubfield σ.toRingEquiv
      exact Subtype.ext ((hτ x).symm.trans (hfixed τ))
  ⟨z, by simpa [x] using congrArg Complex.re (congrArg (fun y : K ↦ (y : ℂ)) hz)⟩

end PropertyF.Ground
