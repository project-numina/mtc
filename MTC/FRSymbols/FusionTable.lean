module
public import MTC.FRSymbols.FusionRules
public import Mathlib.Data.Fintype.BigOperators

/-! # Fusion multiplicities and lexicographic matrix indices in a submitted table -/

@[expose] public section
open scoped BigOperators
namespace MTC.FRSymbols

structure FusionTable (rank : ℕ) where
  unit : ℕ
  dual : Array ℕ
  fusion : Array ℕ
  /-- An alternate lookup can accelerate kernel evaluation of large tables. -/
  lookup : ℕ → ℕ → ℕ → ℕ := fun a b c => fusion[(a * rank + b) * rank + c]?.getD 0
  lookup_eq : ∀ a b c, lookup a b c = fusion[(a * rank + b) * rank + c]?.getD 0 := by
    intros
    rfl

namespace FusionTable
variable {r : ℕ} (t : FusionTable r)

def mult (a b c : ℕ) : ℕ := t.lookup a b c

def dualLabel (a : Fin r) : Fin r :=
  let i := t.dual[a.val]?.getD r
  if h : i < r then ⟨i, h⟩ else a

def before (e : ℕ) (width : ℕ → ℕ) : ℕ :=
  (List.range e).foldl (fun total x => total + width x) 0

def leftSize (a b c d x : ℕ) : ℕ := t.mult a b x * t.mult x c d
def rightSize (a b c d x : ℕ) : ℕ := t.mult b c x * t.mult a x d

/-- Offset of a pair of multiplicity-labelled trivalent trees in a row-major block. -/
def offset (a b c d e α β g δ ε : ℕ) : ℕ :=
  let row := before e (t.leftSize a b c d) + α * t.mult e c d + β
  let col := before g (t.rightSize a b c d) + δ * t.mult a g d + ε
  row * before r (t.rightSize a b c d) + col

def blockSize (a b c d : ℕ) : ℕ :=
  before r (t.leftSize a b c d) * before r (t.rightSize a b c d)

structure Valid : Prop where
  unit_lt : t.unit < r
  dual_size : t.dual.size = r
  dual_lt : ∀ i : Fin r, t.dual[i.val]?.getD r < r
  fusion_size : t.fusion.size = r ^ 3
  involutive : ∀ a, t.dualLabel (t.dualLabel a) = a
  unit_mul : ∀ a c : Fin r, t.mult t.unit a c = if a = c then 1 else 0
  mul_unit : ∀ a c : Fin r, t.mult a t.unit c = if a = c then 1 else 0
  unit_multiplicity : ∀ a b : Fin r, t.mult a b t.unit = if t.dualLabel a = b then 1 else 0
  associative : ∀ a b c d : Fin r,
    (∑ x : Fin r, t.mult a b x * t.mult x c d) = ∑ x : Fin r, t.mult b c x * t.mult a x d

def rules (v : t.Valid) : FusionRules (Fin r) where
  unit := ⟨t.unit, v.unit_lt⟩
  dual := t.dualLabel
  N a b c := t.mult a b c
  dual_involutive := v.involutive
  unit_mul := v.unit_mul
  mul_unit := v.mul_unit
  unit_multiplicity := v.unit_multiplicity
  associativity := v.associative

end FusionTable
end MTC.FRSymbols
