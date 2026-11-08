module
public import MTC.Braided.Cabling.ClosureBlockInduction
public import MTC.Braided.Trace.OverlapCoherence

/-! Recursive block parenthesizations aligned with the row-sweep induction. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.BraidedCategory
namespace MTC.Braided
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]

/-- Split `r+1` leading strands from `s+1` trailing strands. -/
def sweepBlockSplit (X : C) (s : ℕ) : ∀ r : ℕ,
    tensorPower X (s+r+2) ≅ tensorPower X (r+1) ⊗ tensorPower X (s+1)
  | 0 => (ρ_ X).symm ⊗ᵢ Iso.refl (tensorPower X (s+1))
  | r+1 => (Iso.refl X ⊗ᵢ sweepBlockSplit X s r) ≪≫
      (α_ X (tensorPower X (r+1)) (tensorPower X (s+1))).symm

/-- Flatten `s+1` leading strands followed by `r+1` trailing strands. -/
def sweepBlockMerge (X : C) (s : ℕ) : ∀ r : ℕ,
    tensorPower X (s+1) ⊗ tensorPower X (r+1) ≅ tensorPower X (s+r+2)
  | 0 => (Iso.refl (tensorPower X (s+1)) ⊗ᵢ ρ_ X) ≪≫ Trace.appendIso X (s+1)
  | r+1 => (Iso.refl (tensorPower X (s+1)) ⊗ᵢ (Trace.appendIso X (r+1)).symm) ≪≫
      (α_ (tensorPower X (s+1)) (tensorPower X (r+1)) X).symm ≪≫
      (sweepBlockMerge X s r ⊗ᵢ Iso.refl X) ≪≫ Trace.appendIso X (s+r+2)

/-- The actual categorical rectangular block crossing, using the recursive
parenthesizations that match `blockSweepWord`. -/
def sweepBlockCross (X : C) (s r : ℕ) : Aut (tensorPower X (s+r+2)) :=
  Aut.of (sweepBlockSplit X s r ≪≫
    β_ (tensorPower X (r+1)) (tensorPower X (s+1)) ≪≫ sweepBlockMerge X s r)

set_option backward.isDefEq.respectTransparency false in
/-- A one-row block crossing is the single-strand sweep. -/
theorem sweepBlockCross_zero (X : C) (s : ℕ) :
    sweepBlockCross X s 0 = sweepFirst X s := by
  apply Aut.ext
  apply Iso.ext
  simp only [sweepBlockCross, sweepBlockSplit, sweepBlockMerge, sweepFirst,
    singleAcrossPower_eq_braiding, Iso.trans_hom, Iso.symm_hom, tensorIso_hom,
    Iso.refl_hom, tensorHom_id, id_tensorHom]
  rw [braiding_naturality_left_assoc]
  simp

set_option backward.isDefEq.respectTransparency false in
/-- Repeated right insertions are right whiskering by a tensor power,
transported through the canonical insertion isomorphism. -/
theorem addRightStrands_asHom (X : C) (n : ℕ) : ∀ (k : ℕ) (a : braidImage X n),
    ((Trace.addRightStrands X n k a).val).asIso.hom =
      (Trace.insertRightPowerIso X n k).inv ≫ (a.val.asIso.hom ▷ tensorPower X k) ≫
        (Trace.insertRightPowerIso X n k).hom
  | 0, a => by simp [Trace.addRightStrands, Trace.insertRightPowerIso, Trace.braidTensorPower, tensorPower]
  | k+1, a => by
    change (Trace.appendIso X (n+k+2)).inv ≫
      (((Trace.addRightStrands X n k a).val).asIso.hom ▷ X) ≫
        (Trace.appendIso X (n+k+2)).hom = _
    rw [addRightStrands_asHom X n k a]
    simp only [Trace.insertRightPowerIso, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom,
      Iso.symm_inv, tensorIso_hom, tensorIso_inv, Iso.refl_hom, Iso.refl_inv,
      tensorHom_id, comp_whiskerRight, Category.assoc, id_tensorHom, whisker_exchange_assoc]
    rw [← associator_naturality_left_assoc]
    simp

/-- The row-induction base agrees with the actual block crossing. -/
theorem sweepBlockImage_zero (X : C) (s : ℕ) :
    (blockSweepImage X s 0).val = sweepBlockCross X s 0 := by
  change sweepFirst X s = sweepBlockCross X s 0
  exact (sweepBlockCross_zero X s).symm

end MTC.Braided
