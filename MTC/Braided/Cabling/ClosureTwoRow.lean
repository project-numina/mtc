module
public import MTC.Braided.Cabling.ClosureSweep

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.BraidedCategory
namespace MTC.Braided
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]

/-- Cross two strands as a block past a block of n+1 strands, and flatten. -/
def twoRowCross (X : C) (n : ℕ) : Aut (tensorPower X (n+3)) :=
  Aut.of ((α_ X X (tensorPower X (n+1))).symm ≪≫
    β_ (X ⊗ X) (tensorPower X (n+1)) ≪≫
    (α_ (tensorPower X (n+1)) X X).symm ≪≫
    (Trace.appendIso X (n+1) ⊗ᵢ Iso.refl X) ≪≫ Trace.appendIso X (n+2))

set_option backward.isDefEq.respectTransparency false in
set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
/-- The two-row block crossing is two single-strand sweeps. -/
theorem twoRowCross_eq_sweeps (X : C) (n : ℕ) :
    twoRowCross X n = Trace.addRightAut X n (sweepFirst X n) * leftSweep X n := by
  apply Aut.ext
  apply Iso.ext
  simp only [Aut.mul_asIso, Iso.trans_hom]
  change (twoRowCross X n).asIso.hom = (leftSweep X n).asIso.hom ≫
    ((Trace.appendIso X (n+2)).conjAut ((tensorRight X).mapAut _ (sweepFirst X n))).asIso.hom
  rw [Iso.conjAut_hom]
  change ((α_ X X (tensorPower X (n+1))).symm ≪≫
    β_ (X ⊗ X) (tensorPower X (n+1)) ≪≫
    (α_ (tensorPower X (n+1)) X X).symm ≪≫
    (Trace.appendIso X (n+1) ⊗ᵢ Iso.refl X) ≪≫ Trace.appendIso X (n+2)).hom =
      ((Iso.refl X ⊗ᵢ (sweepFirst X n).asIso)).hom ≫
        (Trace.appendIso X (n+2)).inv ≫ ((sweepFirst X n).asIso.hom ▷ X) ≫
          (Trace.appendIso X (n+2)).hom
  simp only [sweepFirst, singleAcrossPower_eq_braiding, Iso.trans_hom, Iso.symm_hom,
    tensorIso_hom, Iso.refl_hom, tensorHom_id, id_tensorHom, braiding_tensor_left_hom]
  rw [Trace.appendIso_succ X (n+1)]
  simp only [Iso.trans_hom, Iso.trans_inv, tensorIso_hom, tensorIso_inv, Iso.refl_hom, Iso.refl_inv, id_tensorHom]
  simp [Category.assoc]

/-- Two sweeps with the required identity-strand insertions. -/
def twoRowWord (n : ℕ) : BraidWords (n+1) :=
  insertRightWord n (sweepFirstWord n) * insertLeftWord n (sweepFirstWord n)

set_option backward.isDefEq.respectTransparency false in
/-- The actual two-row block crossing is represented by the explicit word. -/
theorem twoRowCross_word (X : C) (n : ℕ) :
    twoRowCross X n = (braidWordAction X (n+1) (twoRowWord n)).val := by
  rw [twoRowCross_eq_sweeps, sweepFirst_word]
  simp only [twoRowWord, map_mul, braidWordAction_insertRight, braidWordAction_insertLeft]
  congr 1
  apply Aut.ext
  apply Iso.ext
  simp [leftSweep, addLeftStrand, Functor.mapAut, tensorLeft, sweepFirst_word,
    MonoidHom.codRestrict, MonoidHom.comp]
  rfl

/-- Every two-row crossing belongs to the corresponding actual braid image. -/
theorem twoRowCross_mem (X : C) (n : ℕ) : twoRowCross X n ∈ braidImage X (n+1) := by
  rw [twoRowCross_word]
  exact (braidWordAction X (n+1) (twoRowWord n)).property

/-- Two-row block crossing as an element of the actual image. -/
def twoRowCrossImage (X : C) (n : ℕ) : braidImage X (n+1) :=
  ⟨twoRowCross X n, twoRowCross_mem X n⟩

/-- The two-row block braid admits arbitrary prefixes and suffixes of
identity strands, with an explicit word in the surrounding braid image. -/
theorem twoRowCross_word_with_surrounding (X : C) (n p t : ℕ) :
    braidWordAction X (((n+1)+t)+p)
      (insertLeftWords ((n+1)+t) p (insertRightWords (n+1) t (twoRowWord n))) =
      Trace.addLeftStrands X ((n+1)+t) p
        (Trace.addRightStrands X (n+1) t (twoRowCrossImage X n)) := by
  rw [braidWordAction_insertLeftWords, braidWordAction_insertRightWords]
  congr 2
  apply Subtype.ext
  exact (twoRowCross_word X n).symm

end MTC.Braided

end

/-! Explicitly stack arbitrary numbers of single-strand sweeps. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace MTC.Braided
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]

/-- A rectangular braid built row by row. It crosses `r+1` rows with `s+1`
columns. The last sweep is padded on the right by the already-crossed rows. -/
def blockSweepWord (s : ℕ) : ∀ r : ℕ, BraidWords (s+r)
  | 0 => sweepFirstWord s
  | r+1 => insertRightWords s (r+1) (sweepFirstWord s) *
      insertLeftWord (s+r) (blockSweepWord s r)

/-- The corresponding product of genuine categorical braid-image elements. -/
def blockSweepImage (X : C) (s : ℕ) : ∀ r : ℕ, braidImage X (s+r)
  | 0 => sweepFirstImage X s
  | r+1 => Trace.addRightStrands X s (r+1) (sweepFirstImage X s) *
      addLeftStrand X (s+r) (blockSweepImage X s r)

/-- Evaluating the recursively constructed word gives the actual product of
categorical row-sweeps, for all positive block widths. -/
theorem blockSweepWord_action (X : C) (s : ℕ) : ∀ r : ℕ,
    braidWordAction X (s+r) (blockSweepWord s r) = blockSweepImage X s r
  | 0 => by
      apply Subtype.ext
      exact (sweepFirst_word X s).symm
  | r+1 => by
      simp only [blockSweepWord, blockSweepImage, map_mul, braidWordAction_insertRightWords]
      simp only [Nat.add_succ, braidWordAction_insertLeft, blockSweepWord_action X s r]
      congr 1
      congr 1
      apply Subtype.ext
      exact (sweepFirst_word X s).symm

/-- The first induction step is the previously established two-row word. -/
theorem blockSweepWord_one (s : ℕ) : blockSweepWord s 1 = twoRowWord s := by
  rfl

/-- For two rows, the iterated image is the actual categorical block crossing. -/
theorem blockSweepImage_one (X : C) (s : ℕ) :
    (blockSweepImage X s 1).val = twoRowCross X s := by
  rw [← blockSweepWord_action, blockSweepWord_one]
  exact (twoRowCross_word X s).symm

end MTC.Braided
