module
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Tactic

/-! Consequences of the categorical multiplicity weights. -/

@[expose] public noncomputable section
open scoped BigOperators
namespace PropertyF.Ground.Calculus

/-- The block trace mass is the constituent multiplicity mass whenever the
actual representation dimensions decompose into braid-block dimensions. -/
theorem multiplicity_mass_eq {ι κ : Type*} [Fintype ι] [Fintype κ]
    (m : ι → ℕ) (d : κ → ℕ) (mult : ι → κ → ℕ) (fp : ι → ℝ)
    (hdim : ∀ i, m i = ∑ j, mult i j * d j) :
    (∑ j, (∑ i, (mult i j : ℝ) * fp i) * (d j : ℝ)) =
      ∑ i, (m i : ℝ) * fp i := by
  calc
    _ = ∑ j, ∑ i, ((mult i j : ℝ) * fp i) * (d j : ℝ) := by
      simp only [Finset.sum_mul]
    _ = ∑ i, ∑ j, ((mult i j : ℝ) * (d j : ℝ)) * fp i := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = ∑ i, (m i : ℝ) * fp i := by
      apply Finset.sum_congr rfl
      intro i _
      rw [← Finset.sum_mul, hdim i]
      simp

/-- The paper's Galois-transported multiplicity weights cannot vanish when
all original constituent dimensions are positive and the block is retained. -/
theorem transported_weight_ne_zero {ι : Type*} [Fintype ι]
    (mult : ι → ℕ) (dim : ι → ℝ) (σ : ℂ ≃+* ℂ)
    (hpos : ∀ i, 0 < dim i) (hret : ∃ i, 0 < mult i) :
    (∑ i, (mult i : ℂ) * σ (dim i : ℂ)) ≠ 0 := by
  have hsum : 0 < ∑ i, (mult i : ℝ) * dim i := by
    obtain ⟨i, hi⟩ := hret
    exact Finset.sum_pos' (fun i _ => mul_nonneg (Nat.cast_nonneg _) (hpos i).le)
      ⟨i, Finset.mem_univ _, mul_pos (by exact_mod_cast hi) (hpos i)⟩
  intro hz
  have hzero : (∑ i, (mult i : ℂ) * (dim i : ℂ)) = 0 := by
    apply σ.injective
    simp [map_sum, map_mul, hz]
  have hr : (∑ i, (mult i : ℝ) * dim i) = 0 := by exact_mod_cast hzero
  linarith

end PropertyF.Ground.Calculus
