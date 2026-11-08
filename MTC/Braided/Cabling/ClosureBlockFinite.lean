module
public import MTC.Braided.Cabling.ClosureBlockProof
public import Mathlib.GroupTheory.OrderOfElement

/-! Finiteness consequences for the actual arbitrary-width block crossing. -/

@[expose] public noncomputable section
open CategoryTheory
namespace MTC.Braided
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]

/-- If the original braid image on the combined strands is finite, the
actual positive-block crossing has finite order. -/
theorem sweepBlockCross_pow_eq_one (X : C) (s r : ℕ)
    [Finite (braidImage X (s+r))] :
    ∃ n : ℕ, 0 < n ∧ (sweepBlockCross X s r)^n = 1 := by
  obtain ⟨n, hn, hp⟩ := (isOfFinOrder_of_finite (blockSweepImage X s r)).exists_pow_eq_one
  refine ⟨n, hn, ?_⟩
  have h := congrArg Subtype.val hp
  simpa only [Subgroup.coe_pow, Subgroup.coe_one, blockSweepImage_eq_cross] using h

/-- Property F for `X` makes every actual positive rectangular block crossing
periodic, including crossings of blocks of unequal lengths. -/
theorem sweepBlockCross_pow_eq_one_of_propertyF (X : C) (hX : ObjectPropertyF X)
    (s r : ℕ) : ∃ n : ℕ, 0 < n ∧ (sweepBlockCross X s r)^n = 1 := by
  letI := hX (s+r)
  exact sweepBlockCross_pow_eq_one X s r

end MTC.Braided
