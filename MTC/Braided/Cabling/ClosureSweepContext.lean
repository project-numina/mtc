module
public import MTC.Braided.Cabling.ClosureSweep

/-! A single strand can sweep through any block, even with identity strands
on either side, by an explicit word in the actual categorical braid image. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace MTC.Braided
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]

/-- A single-strand sweep belongs to the original categorical braid image. -/
theorem sweepFirst_mem (X : C) (n : ℕ) : sweepFirst X n ∈ braidImage X n := by
  rw [sweepFirst_word]
  exact (braidWordAction X n (sweepFirstWord n)).property

/-- The actual categorical image element given by a single-strand sweep. -/
def sweepFirstImage (X : C) (n : ℕ) : braidImage X n :=
  ⟨sweepFirst X n, sweepFirst_mem X n⟩

/-- A sweep surrounded by arbitrary identity strands is realized by the
explicit left-shifted, right-padded sweep word. -/
theorem sweepFirst_word_with_surrounding (X : C) (n p t : ℕ) :
    braidWordAction X ((n+t)+p)
      (insertLeftWords (n+t) p (insertRightWords n t (sweepFirstWord n))) =
      Trace.addLeftStrands X (n+t) p (Trace.addRightStrands X n t (sweepFirstImage X n)) := by
  rw [braidWordAction_insertLeftWords, braidWordAction_insertRightWords]
  congr 2
  apply Subtype.ext
  exact (sweepFirst_word X n).symm

end MTC.Braided
