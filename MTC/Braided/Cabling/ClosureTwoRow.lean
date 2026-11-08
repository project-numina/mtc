module
public import MTC.Braided.Cabling.ClosureSweepContext

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

end MTC.Braided
