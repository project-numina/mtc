module
public import PropertyF.UnitaryTrace

/-!
# Weighted traces on matrix blocks

Unitary trace bounds and the centrality consequence of saturation.
-/

@[expose] public noncomputable section
open scoped BigOperators
namespace PropertyF

/-- Explicit finite Wedderburn blocks, rather than an opaque trace space. -/
structure Blocks where
  /-- Number of matrix blocks. -/
  count : ℕ
  /-- Dimension of each block. -/
  size : Fin count → ℕ

namespace Blocks
/-- Product of the complex matrix algebras in the decomposition. -/
abbrev Algebra (B : Blocks) := ∀ r, Matrix (Fin (B.size r)) (Fin (B.size r)) ℂ

/-- Blockwise unitarity. -/
def IsUnitary (B : Blocks) (u : B.Algebra) : Prop :=
  ∀ r, u r ∈ Matrix.unitaryGroup (Fin (B.size r)) ℂ

/-- Weighted sum of the block traces. -/
def trace (B : Blocks) (w : Fin B.count → ℝ) (u : B.Algebra) : ℂ :=
  ∑ r, (w r : ℂ) * (u r).trace

/-- Weighted sum of the block dimensions. -/
def mass (B : Blocks) (w : Fin B.count → ℝ) : ℝ :=
  ∑ r, |w r| * B.size r

lemma norm_trace_le (B : Blocks) (w : Fin B.count → ℝ) {u : B.Algebra}
    (hu : B.IsUnitary u) : ‖B.trace w u‖ ≤ B.mass w := by
  calc
    ‖B.trace w u‖ ≤ ∑ r, ‖(w r : ℂ) * (u r).trace‖ := norm_sum_le _ _
    _ = ∑ r, |w r| * ‖(u r).trace‖ := by simp
    _ ≤ B.mass w := Finset.sum_le_sum fun r _ =>
      mul_le_mul_of_nonneg_left
        (by simpa using norm_trace_le_card (columnUnitary_of_unitary (hu r))) (abs_nonneg _)

/-- The sign element used on page 4, equation (3). -/
def signElement (B : Blocks) (w : Fin B.count → ℝ) : B.Algebra :=
  fun r => (if 0 ≤ w r then (1 : ℂ) else -1) • 1

lemma signElement_unitary (B : Blocks) (w : Fin B.count → ℝ) :
    B.IsUnitary (B.signElement w) := by
  intro r
  by_cases h : 0 ≤ w r <;>
    simp [signElement, h, Matrix.mem_unitaryGroup_iff]

lemma trace_signElement (B : Blocks) (w : Fin B.count → ℝ) :
    B.trace w (B.signElement w) = (B.mass w : ℂ) := by
  simp only [trace, mass, signElement, Matrix.trace_smul, Matrix.trace_one,
    Fintype.card_fin, Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_natCast]
  apply Finset.sum_congr rfl
  intro r _
  by_cases h : 0 ≤ w r
  · simp [h, abs_of_nonneg h]
  · simp [h, abs_of_neg (lt_of_not_ge h)]

/-- Equality in the weighted bound implies centrality when no weight vanishes.
This is the equality argument in Lemma 3.2, proved using actual complex matrices. -/
theorem central_of_saturation (B : Blocks) (w : Fin B.count → ℝ)
    (hw : ∀ r, w r ≠ 0) {g : B.Algebra} (hg : B.IsUnitary g)
    (hsat : ‖B.trace w g‖ = B.mass w) : ∀ T : B.Algebra, g * T = T * g := by
  have hle : ∀ r, |w r| * ‖(g r).trace‖ ≤ |w r| * B.size r := fun r =>
    mul_le_mul_of_nonneg_left
      (by simpa using norm_trace_le_card (columnUnitary_of_unitary (hg r))) (abs_nonneg _)
  have heq : ∑ r, |w r| * ‖(g r).trace‖ = ∑ r, |w r| * B.size r := by
    apply le_antisymm (Finset.sum_le_sum fun r _ => hle r)
    calc
      _ = ‖B.trace w g‖ := hsat.symm
      _ ≤ ∑ r, ‖(w r : ℂ) * (g r).trace‖ := norm_sum_le _ _
      _ = _ := by simp
  have hblock : ∀ r, ‖(g r).trace‖ = B.size r := by
    intro r
    have h := (Finset.sum_eq_sum_iff_of_le (fun r _ => hle r)).mp heq r (Finset.mem_univ r)
    exact (mul_left_cancel₀ (abs_ne_zero.mpr (hw r))) h
  intro T
  funext r
  obtain ⟨z, hz⟩ := scalar_of_norm_trace_eq_card (columnUnitary_of_unitary (hg r))
    (by simpa using hblock r)
  change g r * T r = T r * g r
  rw [hz, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]

end Blocks
end PropertyF
