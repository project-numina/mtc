module
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Fusion rules

A finite based ring of fusion multiplicities, with a specified unit and duality.
The associativity axiom is stated as the equality of the two sums over
intermediate simple labels. These are necessary numerical data for a fusion
category; they do not by themselves specify a category.
-/

@[expose] public section
open scoped BigOperators

namespace MTC.FRSymbols

/-- Fusion multiplicities `N a b c` count the copies of `c` in `a ⊗ b`.
The duality axiom records the multiplicity of the unit in `a ⊗ b`. -/
structure FusionRules (L : Type*) [Fintype L] [DecidableEq L] where
  unit : L
  dual : L → L
  N : L → L → L → ℕ
  dual_involutive : Function.Involutive dual
  unit_mul : ∀ a c, N unit a c = if a = c then 1 else 0
  mul_unit : ∀ a c, N a unit c = if a = c then 1 else 0
  unit_multiplicity : ∀ a b, N a b unit = if dual a = b then 1 else 0
  associativity : ∀ a b c d,
    ∑ x, N a b x * N x c d = ∑ y, N b c y * N a y d

namespace FusionRules
variable {L : Type*} [Fintype L] [DecidableEq L] (F : FusionRules L)

/-- Braided fusion rules are commutative. -/
def IsCommutative : Prop := ∀ a b c, F.N a b c = F.N b a c

/-- Multiplicity-free means that every fusion space has dimension at most one. -/
def IsMultiplicityFree : Prop := ∀ a b c, F.N a b c ≤ 1

@[simp] theorem dual_dual (a : L) : F.dual (F.dual a) = a := F.dual_involutive a

end FusionRules
end MTC.FRSymbols
