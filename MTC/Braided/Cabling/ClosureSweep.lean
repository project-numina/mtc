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

end MTC.Braided
