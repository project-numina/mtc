module
public import MTC.Braided.Cabling.ClosureFour

/-! Appending arbitrarily many original strands to the checked four-strand
block crossing, with an explicit word and actual categorical action. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace MTC.Braided
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]

/-- The width-two block crossing as an element of the actual four-strand image. -/
def fourBlockImage (X : C) : braidImage X 2 :=
  ⟨(fourBlockFlatten X).conjAut (braidGenerator (tensorPower X 2) 0 0), by
    rw [fourBlock_word]
    exact (braidWordAction X 2 (blockCrossingWord 1 0)).property⟩

/-- The checked block crossing with any number of identity strands appended
is represented by the explicit adjacent-strand word with those strands appended. -/
theorem fourBlock_word_with_tail (X : C) (t : ℕ) :
    braidWordAction X (2+t) (insertRightWords 2 t (blockCrossingWord 1 0)) =
      Trace.addRightStrands X 2 t (fourBlockImage X) := by
  rw [braidWordAction_insertRightWords]
  congr 1
  apply Subtype.ext
  exact (fourBlock_word X).symm

/-- The same crossing, with arbitrary numbers of identity strands before and
behind it, is evaluated by the explicitly shifted and padded braid word. -/
theorem fourBlock_word_with_surrounding (X : C) (p t : ℕ) :
    braidWordAction X ((2+t)+p)
      (insertLeftWords (2+t) p (insertRightWords 2 t (blockCrossingWord 1 0))) =
      Trace.addLeftStrands X (2+t) p (Trace.addRightStrands X 2 t (fourBlockImage X)) := by
  rw [braidWordAction_insertLeftWords, fourBlock_word_with_tail]

end MTC.Braided
