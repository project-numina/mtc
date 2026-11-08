module
public import MTC.Braided.Cabling.ClosureInsertionCompare

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace MTC.Braided
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C] [Abelian C]

set_option backward.isDefEq.respectTransparency false in
/-- Flattening a single block removes the trailing tensor unit. -/
theorem flattenPower_one_heq (X : C) (k : ℕ) :
    flattenPower X k 1 ≍ ρ_ (tensorPower X k) := by
  have h := flattenBlocksRecursive_heq X k 1
  simp only [flattenBlocksRecursive, blockStrandCount] at h
  have hid : (Iso.refl (tensorPower X k) ⊗ᵢ Iso.refl (𝟙_ C)) = Iso.refl _ := by
    apply Iso.ext
    simp
  simp only [tensorPower] at h
  rw [hid, Iso.refl_trans] at h
  have hj := joinPowerIso_heq X k 0
  rw [tensorPowerTensorIso_zero] at hj
  exact h.symm.trans hj

set_option backward.isDefEq.respectTransparency false in
/-- The two-block flattening is the same structural flattening. -/
theorem twoBlockFlatten_heq_flattenPower (X : C) (k : ℕ) :
    twoBlockFlatten X k ≍ flattenPower X (k+1) 2 := by
  have hs := joinPowerNormalized_eq_split X k k
  have hj : joinPowerIso X (k+1) (k+1) ≍ (sweepBlockSplit X k k).symm := by
    have h := iso_trans_eqToIso_heq (joinPowerIso X (k+1) (k+1))
      (congrArg (tensorPower X) (by rw [strandSum_eq_add]; omega :
        strandSum (k+1) (k+1) = k+k+2))
    change joinPowerNormalized X k k ≍ joinPowerIso X (k+1) (k+1) at h
    exact h.symm.trans (heq_of_eq hs)
  have ht := (joinPowerIso_heq X (k+1) (k+1)).symm.trans hj
  have hu := flattenPower_one_heq X (k+1)
  have hf := flattenPower_succ_heq X (k+1) 1
  apply HEq.trans _ hf.symm
  simp only [twoBlockFlatten]
  congr 2
  all_goals try exact hu.symm
  all_goals try exact ht.symm
  all_goals try simp
  all_goals try omega
  all_goals exact ht.symm.trans (by congr 1; omega)
