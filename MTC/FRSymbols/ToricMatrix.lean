module
public import MTC.FRSymbols.MatrixSymbols
public import MTC.FRSymbols.ToricModularData

/-!
# Toric code in the matrix-valued F/R interface

The toric code provides a nontrivial check on the indexing of the matrix
hexagons, beyond the rank-one example. This file checks both full hexagons,
invertibility and unitarity with exact integer matrices. The pointed
pentagon is checked in `ToricCode`; the general matrix pentagon is not claimed
here for this instance.
-/

@[expose] public section
namespace MTC.FRSymbols.Pointed.ToricCode

/-- The fusion table in the same order as `label`. -/
def matrixRules : FusionRules (Fin 4) where
  unit := 0
  dual := id
  N := fusion
  dual_involutive := by intro; rfl
  unit_mul := by decide
  mul_unit := by decide
  unit_multiplicity := by decide
  associativity := by decide

/-- Toric-code associator and braiding blocks in the general matrix interface. -/
def matrixSymbols : MatrixSymbols matrixRules ℤ where
  F := fun _ _ _ _ _ _ => 1
  Finv := fun _ _ _ _ _ _ => 1
  R := fun a b _ _ _ => if Nat.testBit a.val 0 && Nat.testBit b.val 1 then -1 else 1
  Rinv := fun a b _ _ _ => if Nat.testBit a.val 0 && Nat.testBit b.val 1 then -1 else 1

/-- The scalar R block agrees with the pointed toric-code symbol. -/
theorem matrix_R_agrees (a b c : Fin 4) (i : Fin (matrixRules.N a b c))
    (j : Fin (matrixRules.N b a c)) :
    (matrixSymbols.R a b c i j : ℚ) = (symbols.R (label a) (label b) : ℚˣ) := by
  fin_cases a <;> fin_cases b <;>
    norm_num [matrixSymbols, symbols, braiding, label] <;> decide

/-- The F and R blocks are invertible in both directions. -/
theorem matrix_invertible : matrixSymbols.Invertible := by
  unfold MatrixSymbols.Invertible
  decide

/-- The first hexagon holds for every allowed set of fusion indices. -/
theorem matrix_hexagon₁ : matrixSymbols.Hexagon₁ := by
  unfold MatrixSymbols.Hexagon₁
  decide

/-- The second hexagon holds for every allowed set of fusion indices. -/
theorem matrix_hexagon₂ : matrixSymbols.Hexagon₂ := by
  unfold MatrixSymbols.Hexagon₂
  intro a
  fin_cases a <;> decide

/-- The chosen integer blocks are unitary for the standard involution. -/
theorem matrix_unitary : matrixSymbols.Unitary := by
  simp [MatrixSymbols.Unitary, matrixSymbols]

/-- The same blocks are unitary under the usual embedding of integers in ℂ. -/
theorem matrix_unitary_via : matrixSymbols.UnitaryVia (Int.castRingHom ℂ) := by
  constructor
  · intro a b c d i j
    simp [matrixSymbols]
  · intro a b c i j
    simp only [matrixSymbols]
    split_ifs <;> simp

end MTC.FRSymbols.Pointed.ToricCode
