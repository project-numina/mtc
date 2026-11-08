module
public import MTC.Braided.Cabling.ClosureReindex

/-! Cast-free recursive flattening of blocks, with arithmetic transport only at
the external boundary. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace MTC.Braided
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- Addition recursing on the left argument, to match right-associated powers. -/
def strandSum : ℕ → ℕ → ℕ
  | 0, b => b
  | a+1, b => (strandSum a b)+1

/-- Left-recursive addition is ordinary addition. -/
theorem strandSum_eq_add : ∀ a b, strandSum a b = a+b
  | 0, b => by simp [strandSum]
  | a+1, b => by simp [strandSum, strandSum_eq_add a b, Nat.succ_add]

/-- Join two powers recursively without intermediate index transports. -/
def joinPowerIso (X : C) : ∀ a b, tensorPower X a ⊗ tensorPower X b ≅
    tensorPower X (strandSum a b)
  | 0, b => λ_ (tensorPower X b)
  | a+1, b => (α_ X (tensorPower X a) (tensorPower X b)) ≪≫
      (Iso.refl X ⊗ᵢ joinPowerIso X a b)

/-- Strand count of `n` blocks of `k` strands, recursing by joining a block. -/
def blockStrandCount (k : ℕ) : ℕ → ℕ
  | 0 => 0
  | n+1 => strandSum k (blockStrandCount k n)

/-- Recursive block strand count agrees with multiplication. -/
theorem blockStrandCount_eq_mul (k : ℕ) : ∀ n,
    blockStrandCount k n = n*k
  | 0 => by simp [blockStrandCount]
  | n+1 => by
    simp only [blockStrandCount, strandSum_eq_add, blockStrandCount_eq_mul k n, Nat.succ_mul]
    omega

/-- Flatten any number of same-width blocks with no index casts in the recursion. -/
def flattenBlocksRecursive (X : C) (k : ℕ) : ∀ n,
    tensorPower (tensorPower X k) n ≅ tensorPower X (blockStrandCount k n)
  | 0 => Iso.refl _
  | n+1 => (Iso.refl (tensorPower X k) ⊗ᵢ flattenBlocksRecursive X k n) ≪≫
      joinPowerIso X k (blockStrandCount k n)

/-- The recursive flattening with its standard multiplication index. -/
def flattenBlocks (X : C) (k n : ℕ) :
    tensorPower (tensorPower X k) n ≅ tensorPower X (n*k) :=
  flattenBlocksRecursive X k n ≪≫ powerIndexIso X (blockStrandCount_eq_mul k n)

/-- Normalize a recursive join to the canonical split's strand index. -/
def joinPowerNormalized (X : C) (s r : ℕ) :
    tensorPower X (r+1) ⊗ tensorPower X (s+1) ≅ tensorPower X (s+r+2) :=
  joinPowerIso X (r+1) (s+1) ≪≫
    powerIndexIso X (by rw [strandSum_eq_add]; omega : strandSum (r+1) (s+1) = s+r+2)

set_option backward.isDefEq.respectTransparency false in
set_option maxRecDepth 4096 in
/-- A recursive join is the inverse of the canonical block split. -/
theorem joinPowerNormalized_eq_split (X : C) (s : ℕ) : ∀ r : ℕ,
    joinPowerNormalized X s r = (sweepBlockSplit X s r).symm
  | 0 => by
    apply Iso.ext
    simp [joinPowerNormalized, joinPowerIso, powerIndexIso, sweepBlockSplit, tensorPower]
  | r+1 => by
    have hrecur : joinPowerNormalized X s (r+1) =
        α_ X (tensorPower X (r+1)) (tensorPower X (s+1)) ≪≫
          (Iso.refl X ⊗ᵢ joinPowerNormalized X s r) := by
      apply Iso.ext
      simp only [joinPowerNormalized, joinPowerIso, powerIndexIso, Iso.trans_hom,
        tensorIso_hom, Iso.refl_hom, id_tensorHom, whiskerLeft_comp,
        eqToIso.hom, whiskerLeft_eqToHom, Category.assoc]
    rw [hrecur, joinPowerNormalized_eq_split X s r]
    apply Iso.ext
    simp [sweepBlockSplit, tensorIso_inv]


end MTC.Braided
