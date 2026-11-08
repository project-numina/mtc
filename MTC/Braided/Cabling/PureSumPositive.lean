module
public import MTC.Braided.Cabling.PureSumColored

/-! Elementary strand-count bounds for positive-width colored tuples. -/
@[expose] public noncomputable section
open scoped BigOperators
namespace MTC.Braided.Cabling

/-- A tuple with at least two positive block widths has at least two original
strands, so its flattening lies in an ordinary braid image. -/
theorem two_le_sum_positive_widths (n : ℕ) (k : Fin (n + 2) → ℕ)
    (hk : ∀ i, 0 < k i) : 2 ≤ ∑ i, k i := by
  have h : n + 2 ≤ ∑ i, k i := by
    calc
      n + 2 = ∑ _ : Fin (n + 2), 1 := by simp
      _ ≤ ∑ i, k i := Finset.sum_le_sum fun i _ => hk i
  omega

end MTC.Braided.Cabling
end
