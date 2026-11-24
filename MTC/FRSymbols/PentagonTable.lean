module
public import MTC.FRSymbols.FusionTable
public import MTC.FRSymbols.MatrixSymbols
public import MTC.FRSymbols.PentagonCoefficient

/-!
# Checking an exact associator table

The external file reader emits the data below. The rank, fusion rules, block
sizes, coefficient relation and every pentagon are checked inside Lean.
Nonempty blocks use the lexicographic trivalent bases of the Atlas.
-/

@[expose] public section
open scoped BigOperators
namespace MTC.FRSymbols

open PentagonCoefficient

/-- Dense label arrays in lexicographic order. Each block is row-major, and
each scalar is a list of rational power-basis coordinates, constant first. -/
structure PentagonTable (rank : ℕ) where
  order : ℕ
  unit : ℕ
  dual : Array ℕ
  fusion : Array ℕ
  blocks : Array (Array Coeff)

namespace PentagonTable
variable {r : ℕ} (t : PentagonTable r)

def toFusionTable : FusionTable r where
  unit := t.unit
  dual := t.dual
  fusion := t.fusion

abbrev mult := t.toFusionTable.mult
abbrev dualLabel := t.toFusionTable.dualLabel

def block (a b c d : ℕ) : Array Coeff :=
  t.blocks[((a * r + b) * r + c) * r + d]?.getD #[]

abbrev before := FusionTable.before
abbrev leftSize := t.toFusionTable.leftSize
abbrev rightSize := t.toFusionTable.rightSize

/-- Table layout and the based fusion-ring laws needed by the matrix specification. -/
structure Valid : Prop where
  order_pos : 0 < t.order
  unit_lt : t.unit < r
  dual_size : t.dual.size = r
  dual_lt : ∀ i : Fin r, t.dual[i.val]?.getD r < r
  fusion_size : t.fusion.size = r ^ 3
  blocks_size : t.blocks.size = r ^ 4
  block_size : ∀ a b c d : Fin r, (t.block a b c d).size =
    before r (t.leftSize a b c d) * before r (t.rightSize a b c d)
  involutive : ∀ a, t.dualLabel (t.dualLabel a) = a
  unit_mul : ∀ a c : Fin r, t.mult t.unit a c = if a = c then 1 else 0
  mul_unit : ∀ a c : Fin r, t.mult a t.unit c = if a = c then 1 else 0
  unit_multiplicity : ∀ a b : Fin r, t.mult a b t.unit = if t.dualLabel a = b then 1 else 0
  associative : ∀ a b c d : Fin r,
    (∑ x : Fin r, t.mult a b x * t.mult x c d) = ∑ x : Fin r, t.mult b c x * t.mult a x d

/-- Interpret the submitted fusion array as based fusion rules. -/
def rules (v : t.Valid) : FusionRules (Fin r) :=
  t.toFusionTable.rules ⟨v.unit_lt, v.dual_size, v.dual_lt, v.fusion_size, v.involutive,
    v.unit_mul, v.mul_unit, v.unit_multiplicity, v.associative⟩

/-- Coefficient at left tree (e,α,β) and right tree (g,δ,ε). -/
def entry (a b c d e α β g δ ε : ℕ) : Coeff :=
  (t.block a b c d)[t.toFusionTable.offset a b c d e α β g δ ε]?.getD []

/-- The exact associators represented by this table in Q(ζ_order). -/
noncomputable def associator (v : t.Valid) : FBlocks (t.rules v) (ExactCyclotomic t.order) :=
  fun a b c d i j => value t.order (t.entry a b c d i.1 i.2.1 i.2.2 j.1 j.2.1 j.2.2)

/-- The mathematical claim returned by the checker. The proof refers to the
submitted associators and to the same pentagon used for matrix F/R symbols. -/
structure Pentagon : Prop where
  valid : t.Valid
  all_pentagons : FBlocks.Pentagon (n := t.rules valid) (t.associator valid)

def sumFin : (n : ℕ) → (Fin n → Coeff) → Coeff
  | 0, _ => []
  | n + 1, f => add (f 0) (sumFin n (fun i => f i.succ))

private theorem value_sumFin (order n : ℕ) (f : Fin n → Coeff) :
    value order (sumFin n f) = ∑ i, value order (f i) := by
  induction n with
  | zero => simp [sumFin]
  | succ n ih => simp [sumFin, Fin.sum_univ_succ, ih]

/-- Check both paths for one pair of four-object fusion trees. -/
def checkEntry (monicTail : Coeff) (a b c d u e f g h α β γ δ ζ η : ℕ) : Bool :=
  let lhs := sumFin (t.mult e g u) fun ε =>
    mul (t.entry e c d u f β γ g δ ε) (t.entry a b g u e α ε h ζ η)
  let rhs := sumFin r fun j => sumFin (t.mult b c j) fun μ =>
    sumFin (t.mult a j f) fun ν => sumFin (t.mult j d h) fun ρ =>
      mul (mul (t.entry a b c f e α β j μ ν) (t.entry a j d u f ν γ h ρ η))
        (t.entry b c d h j μ ρ g δ ζ)
  eqMod monicTail lhs rhs

/-- Branch on each multiplicity index as soon as its labels are known.
Channels of dimension zero therefore contribute no equations. -/
def Checks (monicTail : Coeff) : Prop :=
  ∀ (a b e : Fin r) (α : Fin (t.mult a b e)) (c f : Fin r) (β : Fin (t.mult e c f))
    (d u : Fin r) (γ : Fin (t.mult f d u)) (g : Fin r) (δ : Fin (t.mult c d g))
    (h : Fin r) (ζ : Fin (t.mult b g h)) (η : Fin (t.mult a h u)),
    t.checkEntry monicTail a b c d u e f g h α β γ δ ζ η = true

instance (monicTail : Coeff) : Decidable (t.Checks monicTail) := by
  unfold Checks
  infer_instance

/-- Report the first pair of fusion trees whose two exact contractions differ.
This diagnostic uses the same scalar comparison as the acceptance theorem. -/
def firstFailure (monicTail : Coeff) : Option (Array ℕ) := Id.run do
  for a in [:r] do
    for b in [:r] do
      for c in [:r] do
        for d in [:r] do
          for u in [:r] do
            let left := trees (t.mult a b) (fun e f => t.mult e c f) (fun f => t.mult f d u)
            let right := trees (t.mult c d) (fun g h => t.mult b g h) (fun h => t.mult a h u)
            for (e, f, α, β, γ) in left do
              for (g, h, δ, ζ, η) in right do
                unless t.checkEntry monicTail a b c d u e f g h α β γ δ ζ η do
                  return some #[a, b, c, d, u, e, f, g, h, α, β, γ, δ, ζ, η]
  return none
where
  trees (first : ℕ → ℕ) (next : ℕ → ℕ → ℕ) (last : ℕ → ℕ) :
      List (ℕ × ℕ × ℕ × ℕ × ℕ) := do
    let e ← List.range r
    let α ← List.range (first e)
    let f ← List.range r
    let β ← List.range (next e f)
    let γ ← List.range (last f)
    pure (e, f, α, β, γ)

/-- Soundness for every rank, fusion multiplicity and positive conductor.
The relation used in polynomial reductions is checked once for the table. -/
theorem pentagon_of_check {monicTail : Coeff} (v : t.Valid)
    (hm : checkModulus t.order monicTail = true) (hc : t.Checks monicTail) : t.Pentagon := by
  have hmzero := @checkModulus_sound t.order ⟨Nat.ne_of_gt v.order_pos⟩ monicTail hm
  refine ⟨v, ?_⟩
  intro a b c d u e f g h α β γ δ ζ η
  have hentry := hc a b e α c f β d u γ g δ h ζ η
  unfold checkEntry at hentry
  have eq := eqMod_sound t.order monicTail _ _ hmzero hentry
  simp only [value_sumFin, value_mul] at eq
  exact eq

end PentagonTable
end MTC.FRSymbols
