module
public import MTC.Braided.Cabling.ClosureJoinCompare

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace MTC.Braided
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

set_option backward.isDefEq.respectTransparency false in
 theorem flattenPower_zero_heq (X : C) (k : ℕ) :
    flattenPower X k 0 ≍ Iso.refl (𝟙_ C) := by
  unfold flattenPower
  exact cast_heq _ _

set_option backward.isDefEq.respectTransparency false in
 theorem flattenPower_succ_heq (X : C) (k n : ℕ) :
    flattenPower X k (n+1) ≍
      (Iso.refl (tensorPower X k) ⊗ᵢ flattenPower X k n) ≪≫
        tensorPowerTensorIso X k (n*k) := by
  conv_lhs => unfold flattenPower
  exact cast_heq _ _

set_option backward.isDefEq.respectTransparency false in
 theorem flattenBlocksRecursive_heq (X : C) (k : ℕ) : ∀ n,
    flattenBlocksRecursive X k n ≍ flattenPower X k n
  | 0 => (flattenPower_zero_heq X k).symm
  | n+1 => by
    apply HEq.trans _ (flattenPower_succ_heq X k n).symm
    simp only [flattenBlocksRecursive]
    have ih := flattenBlocksRecursive_heq X k n
    have hj := joinPowerIso_heq X k (blockStrandCount k n)
    congr 2
    all_goals try simp [blockStrandCount_eq_mul, strandSum_eq_add, Nat.succ_mul, Nat.add_comm]
    all_goals exact hj.trans (by congr 1; exact blockStrandCount_eq_mul k n)

/-- The cast-free recursive flattening is the existing flattening after
transport to the usual product index. -/
theorem flattenBlocks_eq_flattenPower (X : C) (k n : ℕ) :
    flattenBlocks X k n = flattenPower X k n := by
  apply eq_of_heq
  exact (iso_trans_eqToIso_heq (flattenBlocksRecursive X k n) _).trans
    (flattenBlocksRecursive_heq X k n)
