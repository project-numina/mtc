module
public import MTC.Braided.Cabling.ClosureTwoRow

/-! Explicitly stack arbitrary numbers of single-strand sweeps. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace MTC.Braided
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]

/-- A rectangular braid built row by row. It crosses `r+1` rows with `s+1`
columns. The last sweep is padded on the right by the already-crossed rows. -/
def blockSweepWord (s : ℕ) : ∀ r : ℕ, BraidWords (s+r)
  | 0 => sweepFirstWord s
  | r+1 => insertRightWords s (r+1) (sweepFirstWord s) *
      insertLeftWord (s+r) (blockSweepWord s r)

/-- The corresponding product of genuine categorical braid-image elements. -/
def blockSweepImage (X : C) (s : ℕ) : ∀ r : ℕ, braidImage X (s+r)
  | 0 => sweepFirstImage X s
  | r+1 => Trace.addRightStrands X s (r+1) (sweepFirstImage X s) *
      addLeftStrand X (s+r) (blockSweepImage X s r)

/-- Evaluating the recursively constructed word gives the actual product of
categorical row-sweeps, for all positive block widths. -/
theorem blockSweepWord_action (X : C) (s : ℕ) : ∀ r : ℕ,
    braidWordAction X (s+r) (blockSweepWord s r) = blockSweepImage X s r
  | 0 => by
      apply Subtype.ext
      exact (sweepFirst_word X s).symm
  | r+1 => by
      simp only [blockSweepWord, blockSweepImage, map_mul, braidWordAction_insertRightWords]
      simp only [Nat.add_succ, braidWordAction_insertLeft, blockSweepWord_action X s r]
      congr 1
      congr 1
      apply Subtype.ext
      exact (sweepFirst_word X s).symm

/-- The first induction step is the previously established two-row word. -/
theorem blockSweepWord_one (s : ℕ) : blockSweepWord s 1 = twoRowWord s := by
  rfl

/-- For two rows, the iterated image is the actual categorical block crossing. -/
theorem blockSweepImage_one (X : C) (s : ℕ) :
    (blockSweepImage X s 1).val = twoRowCross X s := by
  rw [← blockSweepWord_action, blockSweepWord_one]
  exact (twoRowCross_word X s).symm

end MTC.Braided
