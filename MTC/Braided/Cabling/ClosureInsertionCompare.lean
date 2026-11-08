module
public import MTC.Braided.Cabling.ClosureFlattenCompare
public import MTC.Braided.Cabling.ClosureCommonInterface

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace MTC.Braided
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C] [Abelian C]

set_option backward.isDefEq.respectTransparency false in
/-- Left strand insertion is the canonical recursive concatenation. -/
theorem insertLeftPowerIso_heq_join (X : C) (n : ℕ) : ∀ k,
    Trace.insertLeftPowerIso X n k ≍ joinPowerIso X k (n+2)
  | 0 => by rfl
  | k+1 => by
    simp only [Trace.insertLeftPowerIso, joinPowerIso]
    have ih := insertLeftPowerIso_heq_join X n k
    congr 2
    all_goals simp [strandSum_eq_add, tensorPower, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
