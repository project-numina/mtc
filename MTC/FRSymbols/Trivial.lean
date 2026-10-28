module
public import MTC.FRSymbols.MatrixSymbols
public import Mathlib.Tactic

/-!
# A matrix-valued coherence sanity check

The rank-one fusion rule and all-one F and R blocks satisfy all three matrix
coherence equations. This checks that the matrix interface has inhabitants;
it does not by itself reconstruct the category of vector spaces.
-/

@[expose] public section
namespace MTC.FRSymbols.Trivial

/-- The one-label fusion rules. -/
def rules : FusionRules Unit where
  unit := ()
  dual := id
  N := fun _ _ _ => 1
  dual_involutive := by intro; rfl
  unit_mul := by intros; simp
  mul_unit := by intros; simp
  unit_multiplicity := by intros; simp
  associativity := by intros; simp

/-- Every matrix block is one by one, with its sole entry equal to one. -/
def symbols : MatrixSymbols rules ℤ where
  F := fun _ _ _ _ _ _ => 1
  Finv := fun _ _ _ _ _ _ => 1
  R := fun _ _ _ _ _ => 1
  Rinv := fun _ _ _ _ _ => 1

/-- All matrix inverses, pentagon, and both hexagon equations hold. -/
theorem coherent : symbols.Coherent := by
  simp [MatrixSymbols.Coherent, MatrixSymbols.Invertible, MatrixSymbols.Pentagon,
    MatrixSymbols.Hexagon₁, MatrixSymbols.Hexagon₂, symbols, rules, LeftTree, RightTree]
  all_goals decide

/-- The one-dimensional blocks are unitary for the standard involution on ℤ. -/
theorem unitary : symbols.Unitary := by
  simp [MatrixSymbols.Unitary, symbols]

end MTC.FRSymbols.Trivial
