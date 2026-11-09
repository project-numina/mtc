module
public import Mathlib.GroupTheory.OrderOfElement
public import MTC.Braided.Cabling.ClosureInterchange

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.BraidedCategory
namespace MTC.Braided
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]

set_option backward.isDefEq.respectTransparency false in
set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
/-- One further row is a left-whiskered block crossing followed by a
single-strand sweep with the previous rows appended on the right. -/
theorem sweepBlockCross_succ (X : C) (s r : ℕ) (a : braidImage X (s+r))
    (ha : a.val = sweepBlockCross X s r) :
    sweepBlockCross X s (r+1) =
      (Trace.addRightStrands X s (r+1) (sweepFirstImage X s)).val *
        (addLeftStrand X (s+r) a).val := by
  apply Aut.ext
  apply Iso.ext
  simp only [Aut.mul_asIso, Iso.trans_hom, addRightStrands_asHom]
  change (sweepBlockCross X s (r+1)).asIso.hom =
    X ◁ a.val.asIso.hom ≫
      (Trace.insertRightPowerIso X s (r+1)).inv ≫
      ((sweepFirst X s).asIso.hom ▷ tensorPower X (r+1)) ≫
        (Trace.insertRightPowerIso X s (r+1)).hom
  rw [ha]
  simp only [sweepBlockCross, sweepBlockSplit, sweepFirst, singleAcrossPower_eq_braiding]
  rw [sweepBlockMerge_succ_prepend]
  simp only [Iso.trans_hom, Iso.symm_hom, tensorIso_hom,
    Iso.refl_hom, tensorHom_id, id_tensorHom, whiskerLeft_comp, Category.assoc]
  simp only [tensorPower, braiding_tensor_left_hom]
  monoidal
  rw [insertRightPowerIso_eq_merge]
  simp [Category.assoc]
  monoidal

/-- Every row-sweep product is the actual rectangular block crossing. -/
theorem blockSweepImage_eq_cross (X : C) (s : ℕ) : ∀ r : ℕ,
    (blockSweepImage X s r).val = sweepBlockCross X s r
  | 0 => sweepBlockImage_zero X s
  | r+1 => by
    rw [sweepBlockCross_succ X s r (blockSweepImage X s r) (blockSweepImage_eq_cross X s r)]
    rfl

/-- Actual rectangular crossings of arbitrary positive widths are realized
by explicit words in the original adjacent braid generators. -/
theorem sweepBlockCross_word (X : C) (s r : ℕ) :
    sweepBlockCross X s r = (braidWordAction X (s+r) (blockSweepWord s r)).val := by
  rw [blockSweepWord_action]
  exact (blockSweepImage_eq_cross X s r).symm

end MTC.Braided

end

/-! Finiteness consequences for the actual arbitrary-width block crossing. -/

@[expose] public noncomputable section
open CategoryTheory
namespace MTC.Braided
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]

/-- If the original braid image on the combined strands is finite, the
actual positive-block crossing has finite order. -/
theorem sweepBlockCross_pow_eq_one (X : C) (s r : ℕ)
    [Finite (braidImage X (s+r))] :
    ∃ n : ℕ, 0 < n ∧ (sweepBlockCross X s r)^n = 1 := by
  obtain ⟨n, hn, hp⟩ := (isOfFinOrder_of_finite (blockSweepImage X s r)).exists_pow_eq_one
  refine ⟨n, hn, ?_⟩
  have h := congrArg Subtype.val hp
  simpa only [Subgroup.coe_pow, Subgroup.coe_one, blockSweepImage_eq_cross] using h

/-- Property F for `X` makes every actual positive rectangular block crossing
periodic, including crossings of blocks of unequal lengths. -/
theorem sweepBlockCross_pow_eq_one_of_propertyF (X : C) (hX : ObjectPropertyF X)
    (s r : ℕ) : ∃ n : ℕ, 0 < n ∧ (sweepBlockCross X s r)^n = 1 := by
  letI := hX (s+r)
  exact sweepBlockCross_pow_eq_one X s r

end MTC.Braided
