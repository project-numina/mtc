module
public import MTC.Braided.Cabling.ClosureFlattenLocalCompare

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace MTC.Braided
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C] [Abelian C]

set_option backward.isDefEq.respectTransparency false in
/-- Crossing two unequal positive-width blocks, flattening before and after,
is the concrete rectangular braid word on the original strands. -/
theorem heterogeneousBlockCross_word (X : C) (s r : ℕ) :
    Aut.of ((joinPowerNormalized X s r).symm ≪≫
      β_ (tensorPower X (r+1)) (tensorPower X (s+1)) ≪≫
      joinPowerNormalized X r s ≪≫
      powerIndexIso X (by omega : r+s+2 = s+r+2)) =
    (braidWordAction X (s+r) (blockSweepWord s r)).val := by
  rw [joinPowerNormalized_eq_split, joinPowerNormalized_eq_split]
  rw [← sweepBlockMerge_eq_split]
  exact sweepBlockCross_word X s r

set_option backward.isDefEq.respectTransparency false in
/-- Crossing an empty left block gives the identity on original strands. -/
theorem heterogeneousBlockCross_zero_left (X : C) (b : ℕ) :
    ((joinPowerIso X 0 b).symm ≪≫ β_ (tensorPower X 0) (tensorPower X b) ≪≫
      joinPowerIso X b 0) ≍ Iso.refl (tensorPower X b) := by
  have hj := joinPowerIso_heq X b 0
  rw [tensorPowerTensorIso_zero] at hj
  have hh : ((joinPowerIso X 0 b).symm ≪≫ β_ (tensorPower X 0) (tensorPower X b) ≪≫
      joinPowerIso X b 0) ≍
      ((λ_ (tensorPower X b)).symm ≪≫ β_ (𝟙_ C) (tensorPower X b) ≪≫ ρ_ (tensorPower X b)) := by
    simp only [joinPowerIso, tensorPower]
    congr 2
    all_goals simp [strandSum_eq_add]
  apply hh.trans
  apply heq_of_eq
  apply Iso.ext
  simp

set_option backward.isDefEq.respectTransparency false in
/-- Crossing an empty right block gives the identity on original strands. -/
theorem heterogeneousBlockCross_zero_right (X : C) (a : ℕ) :
    ((joinPowerIso X a 0).symm ≪≫ β_ (tensorPower X a) (tensorPower X 0) ≪≫
      joinPowerIso X 0 a) ≍ Iso.refl (tensorPower X a) := by
  have hj := joinPowerIso_heq X a 0
  rw [tensorPowerTensorIso_zero] at hj
  have hh : ((joinPowerIso X a 0).symm ≪≫ β_ (tensorPower X a) (tensorPower X 0) ≪≫
      joinPowerIso X 0 a) ≍
      ((ρ_ (tensorPower X a)).symm ≪≫ β_ (tensorPower X a) (𝟙_ C) ≪≫ λ_ (tensorPower X a)) := by
    simp only [joinPowerIso, tensorPower]
    congr 2
    all_goals simp [strandSum_eq_add]
  apply hh.trans
  apply heq_of_eq
  apply Iso.ext
  simp
