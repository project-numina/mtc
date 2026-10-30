module
public import MTC.Braided.Definitions
public import Mathlib.Tactic
public import MTC.Braided.Trace.ThreeTrace
public import MTC.Braided.Trace.RightStrand

/-!
# Relations of tensor-power braid generators

Self-transparency makes each adjacent generator involutive. Neighbouring
generators satisfy the braid relation, and disjoint generators commute.
We write `b X n i` for the braid generator on the tensor power of `X`.
-/
@[expose] public noncomputable section
local notation "b" => PropertyF.braidGenerator
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.CentreCalculus
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]

/-- An object whose self-braiding squares to the identity. -/
abbrev SelfTransparent (X : C) : Prop :=
  (β_ X X).hom ≫ (β_ X X).hom = 𝟙 (X ⊗ X)

/-- Adding a strand on the left shifts the braid generator by one. -/
theorem braidGenerator_succ (X : C) {n : ℕ} (k : Fin (n + 1)) :
    (tensorLeft X).mapAut (tensorPower X (n + 2)) (b X n k) =
      b X (n + 1) k.succ :=
  Aut.ext <| Iso.ext <| by
    rcases k with ⟨k, hk⟩
    simp [Functor.mapAut, braidGenerator, tensorIso_hom, tensorLeft, id_tensorHom]

variable {X : C} (hX : SelfTransparent X)

include hX in
set_option backward.isDefEq.respectTransparency false in
/-- The first braid generator is involutive on a self-transparent object. -/
theorem braidGenerator_zero_involutive (n : ℕ) :
    b X n ⟨0, Nat.zero_lt_succ n⟩ *
      b X n ⟨0, Nat.zero_lt_succ n⟩ = 1 :=
  Aut.ext <| Iso.ext <| by
    cases n <;>
      simp only [Aut.mul_asIso, Aut.one_asIso, Iso.trans_hom, Iso.refl_hom,
        braidGenerator, Iso.symm_hom, tensorIso_hom, tensorHom_id, Category.assoc,
        Iso.hom_inv_id_assoc] <;>
      rw [← Category.assoc ((β_ X X).hom ▷ _) ((β_ X X).hom ▷ _),
        ← comp_whiskerRight, hX, id_whiskerRight, Category.id_comp, Iso.inv_hom_id]

include hX in
set_option backward.isDefEq.respectTransparency false in
/-- Self-transparency makes each adjacent braid generator an involution. -/
theorem braidGenerator_involutive (n : ℕ) (i : Fin (n + 1)) :
    b X n i * b X n i = 1 := by
  induction n with
  | zero => simpa [Fin.eq_zero i] using braidGenerator_zero_involutive hX 0
  | succ n ih =>
    refine Fin.cases (braidGenerator_zero_involutive hX (n + 1)) (fun j => ?_) i
    simpa only [map_mul, map_one, braidGenerator_succ] using
      congrArg ((tensorLeft X).mapAut (tensorPower X (n + 2))) (ih j)

end PropertyF.Ground.CentreCalculus

open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.CentreCalculus
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  (X : C)

/-- Every neighboring pair of actual tensor-power braid generators satisfies
Yang–Baxter. -/
theorem adjacent_braid_relation (n : ℕ) (i : Fin (n + 1)) :
    b X (n + 1) i.castSucc * b X (n + 1) i.succ *
      b X (n + 1) i.castSucc =
    b X (n + 1) i.succ * b X (n + 1) i.castSucc *
      b X (n + 1) i.succ := by
  induction n with
  | zero => simpa [Fin.eq_zero i] using Calculus.three_braid_relation X
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa [map_mul, Calculus.addRightAut_generator] using
        congrArg (Calculus.addRightAut X (n + 1)) (ih 0)
    · have h := congrArg ((tensorLeft X).mapAut (tensorPower X (n + 3))) (ih j)
      simp only [map_mul, braidGenerator_succ] at h
      convert h using 1 <;> congr 2

set_option backward.isDefEq.respectTransparency false in
/-- A crossing on the first two strands commutes with any crossing after them. -/
theorem first_distant_commute (n : ℕ) (j : Fin (n + 1)) :
    b X (n + 2) 0 * b X (n + 2) j.succ.succ =
      b X (n + 2) j.succ.succ * b X (n + 2) 0 :=
  Aut.ext <| Iso.ext <| by
    simp only [Aut.mul_asIso, Iso.trans_hom]
    change (b X (n + 2) j.succ.succ).asIso.hom ≫
        (b X (n + 2) ⟨0, by omega⟩).asIso.hom =
      (b X (n + 2) ⟨0, by omega⟩).asIso.hom ≫
        (b X (n + 2) j.succ.succ).asIso.hom
    rcases j with ⟨j, hj⟩
    simpa only [Fin.succ, braidGenerator, Iso.trans_hom, Iso.symm_hom, tensorIso_hom,
      Iso.refl_hom, tensorHom_id, id_tensorHom] using
      (Calculus.first_pair_natural X (β_ X X).hom (b X n ⟨j, hj⟩).asIso.hom).symm

set_option backward.isDefEq.respectTransparency false in
/-- Crossings supported on disjoint pairs of strands commute. -/
theorem distant_braid_commute (n : ℕ) (i j : Fin (n + 1)) (hij : i.val + 1 < j.val) :
    b X n i * b X n j = b X n j * b X n i := by
  induction n with
  | zero => omega
  | succ n ih =>
    induction i using Fin.cases with
    | zero =>
      cases n with
      | zero => omega
      | succ n =>
        obtain ⟨j', rfl⟩ := Fin.exists_succ_eq_of_ne_zero (x := j) (by omega)
        obtain ⟨j'', rfl⟩ := Fin.exists_succ_eq_of_ne_zero (x := j') (by rintro rfl; simp at hij)
        exact first_distant_commute X n j''
    | succ i =>
      obtain ⟨j', rfl⟩ := Fin.exists_succ_eq_of_ne_zero (x := j) (by rintro rfl; simp at hij)
      simpa only [map_mul, braidGenerator_succ] using
        congrArg ((tensorLeft X).mapAut (tensorPower X (n + 2)))
          (ih i j' (by simpa using hij))

end PropertyF.Ground.CentreCalculus
