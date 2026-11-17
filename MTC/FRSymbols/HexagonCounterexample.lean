module
public import MTC.FRSymbols.MatrixSymbols

/-!
# Off-diagonal second-hexagon coefficients are not implied by the diagonal ones

These invertible blocks use the Fibonacci fusion rules. They satisfy the
diagonal second-hexagon equations but have a nonzero off-diagonal coefficient.
No pentagon or first-hexagon assertion is made for these blocks.
-/

@[expose] public section
open scoped BigOperators
namespace MTC.FRSymbols.HexagonCounterexample

/-- Two labels with the fusion rule τ ⊗ τ = 𝟙 + τ. -/
def rules : FusionRules Bool where
  unit := false
  dual := id
  N := fun a b c => if a && b then 1 else if c = (a || b) then 1 else 0
  dual_involutive := by intro; rfl
  unit_mul := by decide
  mul_unit := by decide
  unit_multiplicity := by decide
  associativity := by decide

/-- The two-channel F block is [[1, 1], [0, 1]], and every R block is 1. -/
def symbols : MatrixSymbols rules ℤ where
  F := fun a b c d i j =>
    if a && b && c && d then
      if i.1 = j.1 then 1 else if i.1 = false ∧ j.1 = true then 1 else 0
    else 1
  Finv := fun a b c d i j =>
    if a && b && c && d then
      if i.1 = j.1 then 1 else if i.1 = false ∧ j.1 = true then -1 else 0
    else 1
  R := fun _ _ _ _ _ => 1
  Rinv := fun _ _ _ _ _ => 1

/-- The fixture has genuine inverse F and R blocks. -/
theorem invertible : symbols.Invertible := by
  unfold MatrixSymbols.Invertible
  decide

/-- Every coefficient with equal input and output labels is as the hexagon
requires, so these equations cannot detect the remaining coefficient. -/
theorem diagonal_equations_hold : ∀ a b c d e
    (μ : Fin (rules.N a b e)) (ν : Fin (rules.N e c d))
    (α : Fin (rules.N a b e)) (σ : Fin (rules.N c e d)),
    symbols.hexagon₂Path a b c d e e μ ν α σ =
      if μ = α then symbols.R e c d ν σ else 0 := by
  unfold MatrixSymbols.hexagon₂Path
  decide

/-- The coefficient from the unit channel to the τ channel is 1 instead of 0. -/
theorem full_hexagon_fails : ¬ symbols.Hexagon₂ := by
  intro h
  have hentry := h.2 true true true true false true
    ⟨0, by decide⟩ ⟨0, by decide⟩ ⟨0, by decide⟩ ⟨0, by decide⟩ (by decide)
  revert hentry
  unfold MatrixSymbols.hexagon₂Path
  decide

end MTC.FRSymbols.HexagonCounterexample
