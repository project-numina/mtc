module
public import MTC.Braided.Cabling.ClosureTwoRow
public import MTC.Braided.Cabling.Generated

/-! Rectangular positive block crossings and their explicit candidate words. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.BraidedCategory
namespace MTC.Braided
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]

/-- The adjacent crossing index in a rectangle of `(r+1)` rows and `(s+1)` columns. -/
def rectangularCrossingIndex (r s : ℕ) (i : Fin (r+1)) (j : Fin (s+1)) :
    Fin ((r+s)+1) := ⟨i.val + (s-j.val), by omega⟩

/-- An explicit positive word for crossing a block of width `r+1` through a
block of width `s+1`. Its categorical realization is a separate theorem. -/
def rectangularWord (r s : ℕ) : BraidWords (r+s) :=
  (List.ofFn fun i : Fin (r+1) =>
    (List.ofFn fun j : Fin (s+1) => FreeGroup.of (rectangularCrossingIndex r s i j)).prod).prod

/-- The smallest rectangle gives the unique two-strand generator. -/
theorem rectangularWord_zero_zero : rectangularWord 0 0 = FreeGroup.of 0 := by
  simp [rectangularWord, rectangularCrossingIndex, List.ofFn_succ]

/-- A rectangle with two rows and two columns gives the usual four-strand word. -/
theorem rectangularWord_one_one : rectangularWord 1 1 =
    FreeGroup.of (1 : Fin 3) * FreeGroup.of 0 * (FreeGroup.of 2 * FreeGroup.of 1) := by
  simp [rectangularWord, rectangularCrossingIndex, List.ofFn_succ]

variable [Abelian C]

/-- Parenthesize a positive-width prefix and suffix of a tensor power as blocks. -/
def rectangularSplit (X : C) (r s : ℕ) :
    tensorPower X (r+s+2) ≅ tensorPower X (r+1) ⊗ tensorPower X (s+1) := by
  have h : r+s+2 = (r+1)+(s+1) := by omega
  exact eqToIso (congrArg (tensorPower X) h) ≪≫ (tensorPowerTensorIso X (r+1) (s+1)).symm

/-- Cross two positive-width blocks and flatten them back to the original
number of strands. -/
def rectangularCross (X : C) (r s : ℕ) : Aut (tensorPower X (r+s+2)) :=
  Aut.of (rectangularSplit X r s ≪≫
    β_ (tensorPower X (r+1)) (tensorPower X (s+1)) ≪≫
    (rectangularSplit X s r).symm ≪≫
    eqToIso (congrArg (tensorPower X) (by omega : s+r+2 = r+s+2)))


end MTC.Braided
