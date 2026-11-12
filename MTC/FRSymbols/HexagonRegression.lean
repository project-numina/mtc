module
public import MTC.FRSymbols.MatrixSymbols

/-!
# Regression for off-diagonal second-hexagon coefficients

These invertible blocks use the Fibonacci fusion rules. They satisfy the
diagonal second-hexagon equations but have a nonzero off-diagonal coefficient.
No pentagon or first-hexagon assertion is made for these blocks.
-/

@[expose] public section
open scoped BigOperators
namespace MTC.FRSymbols.HexagonRegression

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

/-- The equations checked before independent output labels were introduced. -/
def diagonalHexagon : Prop := ∀ a b c d e
    (μ : Fin (rules.N a b e)) (ν : Fin (rules.N e c d))
    (α : Fin (rules.N a b e)) (σ : Fin (rules.N c e d)),
  (∑ x : Bool, ∑ β : Fin (rules.N b c x), ∑ γ : Fin (rules.N a x d),
    ∑ β' : Fin (rules.N c b x), ∑ y : Bool, ∑ δ : Fin (rules.N a c y),
    ∑ ε : Fin (rules.N y b d), ∑ δ' : Fin (rules.N c a y),
      symbols.F a b c d ⟨e, μ, ν⟩ ⟨x, β, γ⟩ * symbols.R b c x β β' *
      symbols.Finv a c b d ⟨x, β', γ⟩ ⟨y, δ, ε⟩ * symbols.R a c y δ δ' *
      symbols.F c a b d ⟨y, δ', ε⟩ ⟨e, α, σ⟩) =
  if μ = α then symbols.R e c d ν σ else 0

/-- All diagonal equations hold, so they cannot detect the missing coefficient. -/
theorem diagonal_equations_hold : diagonalHexagon := by
  unfold diagonalHexagon
  decide

/-- The coefficient from the unit channel to the τ channel is 1 instead of 0. -/
theorem full_hexagon_fails : ¬ symbols.Hexagon₂ := by
  intro h
  have hentry := h true true true true false true
    ⟨0, by decide⟩ ⟨0, by decide⟩ ⟨0, by decide⟩ ⟨0, by decide⟩
  revert hentry
  decide

end MTC.FRSymbols.HexagonRegression
