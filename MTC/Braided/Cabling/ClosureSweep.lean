module
public import MTC.Braided.Cabling.ClosureCrossing
public import MTC.Braided.Cabling.ClosureInsertion

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.BraidedCategory
namespace MTC.Braided
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]

/-- Move the first strand past all the remaining strands, then flatten. -/
def sweepFirst (X : C) (n : ℕ) : Aut (tensorPower X (n+2)) :=
  Aut.of (singleAcrossPower X (n+1) ≪≫ Trace.appendIso X (n+1))

set_option backward.isDefEq.respectTransparency false in
/-- For two strands, the first-strand sweep is the adjacent generator. -/
theorem sweepFirst_zero (X : C) : sweepFirst X 0 = braidGenerator X 0 0 := by
  apply Aut.ext
  apply Iso.ext
  simp only [sweepFirst, singleAcrossPower_eq_braiding, braidGenerator,
    Iso.trans_hom, tensorIso_hom, Iso.refl_hom]
  simp only [tensorPower, braiding_tensor_right_hom, braiding_tensorUnit_right]
  simp [Trace.appendIso, tensorPower]

/-- The last adjacent crossing, recursively whiskered by identity strands. -/
def lastCross (X : C) : ∀ n, Aut (tensorPower X (n+2))
  | 0 => braidGenerator X 0 0
  | n+1 => (tensorLeft X).mapAut (tensorPower X (n+2)) (lastCross X n)

/-- The recursive last crossing is the actual last adjacent generator. -/
theorem lastCross_eq_generator (X : C) : ∀ n,
    lastCross X n = braidGenerator X n (Fin.last n)
  | 0 => rfl
  | n+1 => by
    apply Aut.ext
    apply Iso.ext
    have ih := congrArg (fun a : Aut (tensorPower X (n+2)) => a.asIso.hom)
      (lastCross_eq_generator X n)
    rw [← Fin.succ_last]
    generalize h : Fin.last n = q at *
    rcases q with ⟨j, hj⟩
    simp only [lastCross, Fin.succ_mk, braidGenerator, Functor.mapAut, tensorIso_hom, Iso.refl_hom, id_tensorHom]
    change X ◁ (lastCross X n).asIso.hom = X ◁ (braidGenerator X n ⟨j, hj⟩).asIso.hom
    rw [ih]

/-- Whisker a sweep with a new identity strand on the left. -/
def leftSweep (X : C) (n : ℕ) : Aut (tensorPower X (n+1+2)) := by
  change Aut (X ⊗ tensorPower X (n+2))
  exact Aut.of (Iso.refl X ⊗ᵢ (sweepFirst X n).asIso)

set_option backward.isDefEq.respectTransparency false in
set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
/-- Sweeping one strand through a longer block begins with the first crossing,
followed by the sweep through the remaining factors. -/
theorem sweepFirst_succ (X : C) (n : ℕ) :
    sweepFirst X (n+1) =
      leftSweep X n *
        braidGenerator X (n+1) 0 := by
  apply Aut.ext
  apply Iso.ext
  change (singleAcrossPower X (n+2) ≪≫ Trace.appendIso X (n+2)).hom =
    ((braidGenerator X (n+1) 0).asIso ≪≫
      (Iso.refl X ⊗ᵢ (singleAcrossPower X (n+1) ≪≫ Trace.appendIso X (n+1)))).hom
  rw [singleAcrossPower_eq_braiding, singleAcrossPower_eq_braiding]
  simp only [← Fin.zero_eta, braidGenerator.eq_1, Iso.trans_hom, Iso.symm_hom, tensorIso_hom, Iso.refl_hom, tensorHom_id]
  simp only [id_tensorHom, tensorPower, braiding_tensor_right_hom]
  rw [Trace.appendIso_succ X (n+1)]
  simp only [Iso.trans_hom, tensorIso_hom, Iso.refl_hom, id_tensorHom]
  monoidal

/-- The adjacent-generator word sweeping the first strand to the end. -/
def sweepFirstWord : ∀ n : ℕ, BraidWords n
  | 0 => FreeGroup.of 0
  | n+1 => insertLeftWord n (sweepFirstWord n) * FreeGroup.of 0

set_option backward.isDefEq.respectTransparency false in
/-- The first-strand sweep is the action of its explicit adjacent word. -/
theorem sweepFirst_word (X : C) : ∀ n,
    sweepFirst X n = (braidWordAction X n (sweepFirstWord n)).val
  | 0 => by simp [sweepFirstWord, braidWordAction, sweepFirst_zero]
  | n+1 => by
    rw [sweepFirst_succ]
    have ih := sweepFirst_word X n
    simp only [sweepFirstWord, map_mul, braidWordAction_insertLeft]
    change leftSweep X n * braidGenerator X (n+1) 0 =
      (addLeftStrand X n (braidWordAction X n (sweepFirstWord n))).val * _
    have ha : leftSweep X n =
        (addLeftStrand X n (braidWordAction X n (sweepFirstWord n))).val := by
      apply Aut.ext
      apply Iso.ext
      simp [leftSweep, addLeftStrand, Functor.mapAut, tensorLeft, ih, tensorIso_hom, MonoidHom.codRestrict, MonoidHom.comp]
      rfl
    rw [ha]
    congr 1
    simp [braidWordAction]

end MTC.Braided
