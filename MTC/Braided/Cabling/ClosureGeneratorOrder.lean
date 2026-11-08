module
public import MTC.Braided.Cabling.ClosureTwoBlockPower
public import MTC.Braided.Trace.RightStrand
public import Mathlib.GroupTheory.OrderOfElement

/-! Periodicity of each actual adjacent generator across all strand counts. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace MTC.Braided
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]

/-- Finiteness of the two-strand image forces each adjacent generator, at
every strand count, to have finite order. -/
theorem braidGenerator_pow_eq_one_of_twoBlock (X : C) [Finite (braidImage X 0)] :
    ∀ (n : ℕ) (i : Fin (n+1)), ∃ m : ℕ, 0 < m ∧ braidGenerator X n i ^ m = 1
  | 0, i => by
    have hi : i = 0 := Fin.eq_zero i
    subst i
    let a : braidImage X 0 := ⟨braidGenerator X 0 0, Subgroup.subset_closure ⟨0, rfl⟩⟩
    obtain ⟨m, hm, hp⟩ := (isOfFinOrder_of_finite a).exists_pow_eq_one
    refine ⟨m, hm, ?_⟩
    exact congrArg Subtype.val hp
  | n+1, i => by
    refine Fin.cases ?_ (fun j => ?_) i
    · obtain ⟨m, hm, hp⟩ := braidGenerator_pow_eq_one_of_twoBlock X n 0
      refine ⟨m, hm, ?_⟩
      have h := congrArg (Trace.addRightAut X n) hp
      have hz : (0 : Fin (n+1)).castSucc = 0 := by ext; rfl
      simpa only [map_pow, map_one, Trace.addRightAut_generator, hz] using h
    · obtain ⟨m, hm, hp⟩ := braidGenerator_pow_eq_one_of_twoBlock X n j
      refine ⟨m, hm, ?_⟩
      have h := congrArg ((tensorLeft X).mapAut (tensorPower X (n+2))) hp
      simp only [map_pow, map_one] at h
      have heq : (tensorLeft X).mapAut (tensorPower X (n+2)) (braidGenerator X n j) =
          braidGenerator X (n+1) j.succ := by
        apply Aut.ext
        apply Iso.ext
        rcases j with ⟨j, hj⟩
        simp [Functor.mapAut, tensorLeft, braidGenerator, tensorIso_hom, id_tensorHom]
      rw [heq] at h
      exact h

/-- Property F of `X` makes every adjacent braid generator on every positive
tensor power periodic. This alone does not assert finiteness of its image. -/
theorem tensorPower_braidGenerator_pow_eq_one (X : C) (hX : ObjectPropertyF X)
    (k n : ℕ) (i : Fin (n+1)) :
    ∃ m : ℕ, 0 < m ∧ braidGenerator (tensorPower X (k+1)) n i ^ m = 1 := by
  letI := hX (k+k)
  letI := finite_twoBlock_image_of_power X k
  exact braidGenerator_pow_eq_one_of_twoBlock (tensorPower X (k+1)) n i

end MTC.Braided
