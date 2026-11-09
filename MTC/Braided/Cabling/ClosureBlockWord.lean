module
public import MTC.Braided.Cabling.ClosureInsertion
public import MTC.Braided.Cabling.ClosureFlatten
public import MTC.Braided.Cabling.ClosureCrossing

/-! Explicit positive block-crossing words. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.BraidedCategory
namespace MTC.Braided
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C] [Abelian C]

/-- An adjacent crossing in the rectangular positive block braid. The two
blocks have width `k+1`; `t` additional strands follow them. -/
def blockCrossingIndex (k t : ℕ) (i j : Fin (k + 1)) : Fin ((2 * k + t) + 1) :=
  ⟨i.val + (k - j.val), by omega⟩

/-- The positive braid moving the first block through the second. Each row
moves one strand across the opposite block, from right to left. -/
def blockCrossingWord (k t : ℕ) : BraidWords (2 * k + t) :=
  (List.ofFn fun i : Fin (k + 1) =>
    (List.ofFn fun j : Fin (k + 1) => FreeGroup.of (blockCrossingIndex k t i j)).prod).prod

/-- A single-strand block crossing is the first adjacent crossing. -/
theorem blockCrossingWord_zero (t : ℕ) :
    blockCrossingWord 0 t = FreeGroup.of (blockCrossingIndex 0 t 0 0) := by
  simp [blockCrossingWord, blockCrossingIndex, List.ofFn_succ]


/-- The two-by-two block braid consists of four adjacent crossings. -/
theorem blockCrossingWord_one_zero :
    blockCrossingWord 1 0 =
      FreeGroup.of (1 : Fin 3) * FreeGroup.of 0 *
        (FreeGroup.of 2 * FreeGroup.of 1) := by
  simp [blockCrossingWord, blockCrossingIndex, List.ofFn_succ]

end MTC.Braided
