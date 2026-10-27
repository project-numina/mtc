module
public import PropertyF.Ground.Calculus.ThreeBraid
public import PropertyF.Ground.Calculus.RightStrand

/-! Adjacent braid relations for all tensor powers. -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.CentreCalculus
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]

/-- Every neighboring pair of actual tensor-power braid generators satisfies
Yang–Baxter. -/
theorem adjacent_braid_relation (X : C) : ∀ (n : ℕ) (i : Fin (n + 1)),
    braidGenerator X (n + 1) i.castSucc * braidGenerator X (n + 1) i.succ *
      braidGenerator X (n + 1) i.castSucc =
    braidGenerator X (n + 1) i.succ * braidGenerator X (n + 1) i.castSucc *
      braidGenerator X (n + 1) i.succ := by
  intro n
  induction n with
  | zero =>
    intro i
    have hi : i = 0 := Fin.eq_zero i
    subst i
    exact Calculus.three_braid_relation X
  | succ n ih =>
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · have h := congrArg (Calculus.addRightAut X (n + 1)) (ih 0)
      simp only [map_mul, Calculus.addRightAut_generator] at h
      convert h using 1 <;> congr 2
    · have h := congrArg ((tensorLeft X).mapAut (tensorPower X (n + 3))) (ih j)
      simp only [map_mul] at h
      have hg (k : Fin (n + 2)) :
          (tensorLeft X).mapAut (tensorPower X (n + 3)) (braidGenerator X (n + 1) k) =
            braidGenerator X (n + 2) k.succ := by
        apply Aut.ext
        apply Iso.ext
        rcases k with ⟨k, hk⟩
        simp [Functor.mapAut, braidGenerator, tensorIso_hom, tensorLeft, id_tensorHom]
      simp only [hg] at h
      convert h using 1 <;> congr 2

set_option backward.isDefEq.respectTransparency false in
/-- A crossing on the first two strands commutes with any crossing after them. -/
theorem first_distant_commute (X : C) (n : ℕ) (j : Fin (n + 1)) :
    braidGenerator X (n + 2) 0 * braidGenerator X (n + 2) j.succ.succ =
      braidGenerator X (n + 2) j.succ.succ * braidGenerator X (n + 2) 0 := by
  apply Aut.ext
  apply Iso.ext
  simp only [Aut.mul_asIso, Iso.trans_hom]
  change (braidGenerator X (n + 2) j.succ.succ).asIso.hom ≫
      (braidGenerator X (n + 2) ⟨0, by omega⟩).asIso.hom =
    (braidGenerator X (n + 2) ⟨0, by omega⟩).asIso.hom ≫
      (braidGenerator X (n + 2) j.succ.succ).asIso.hom
  rcases j with ⟨j, hj⟩
  simp only [Fin.succ, braidGenerator, Iso.trans_hom, Iso.symm_hom, tensorIso_hom,
    Iso.refl_hom, tensorHom_id, id_tensorHom]
  change (X ◁ X ◁ (braidGenerator X n ⟨j, hj⟩).asIso.hom) ≫
      ((α_ X X (tensorPower X (n + 2))).inv ≫ (β_ X X).hom ▷ _ ≫
        (α_ X X (tensorPower X (n + 2))).hom) =
    ((α_ X X (tensorPower X (n + 2))).inv ≫ (β_ X X).hom ▷ _ ≫
        (α_ X X (tensorPower X (n + 2))).hom) ≫
      (X ◁ X ◁ (braidGenerator X n ⟨j, hj⟩).asIso.hom)
  exact (Calculus.crossing_natural X _ _ (braidGenerator X n ⟨j, hj⟩).asIso.hom).symm

set_option backward.isDefEq.respectTransparency false in
/-- Crossings supported on disjoint pairs of strands commute. -/
theorem distant_braid_commute (X : C) : ∀ (n : ℕ) (i j : Fin (n + 1)),
    i.val + 1 < j.val →
    braidGenerator X n i * braidGenerator X n j =
      braidGenerator X n j * braidGenerator X n i := by
  intro n
  induction n with
  | zero =>
    intro i j h
    have hi := i.isLt
    have hj := j.isLt
    omega
  | succ n ih =>
    intro i j
    revert j
    refine Fin.cases ?_ (fun i' => ?_) i <;> intro j
    · cases n with
      | zero =>
        intro h
        have hj := j.isLt
        omega
      | succ n =>
        refine Fin.cases ?_ (fun j' => ?_) j
        · intro h; simp only [Fin.val_succ, Fin.val_zero] at h; omega
        · refine Fin.cases ?_ (fun j'' => ?_) j'
          · intro h; simp only [Fin.val_succ, Fin.val_zero] at h; omega
          · intro h
            exact first_distant_commute X n j''
    · refine Fin.cases ?_ (fun j' => ?_) j
      · intro h; simp only [Fin.val_succ, Fin.val_zero] at h; omega
      · intro h
        have h' : i'.val + 1 < j'.val := by simpa using h
        have hh := congrArg ((tensorLeft X).mapAut (tensorPower X (n + 2))) (ih i' j' h')
        simp only [map_mul] at hh
        have hg (k : Fin (n + 1)) :
            (tensorLeft X).mapAut (tensorPower X (n + 2)) (braidGenerator X n k) =
              braidGenerator X (n + 1) k.succ := by
          apply Aut.ext
          apply Iso.ext
          rcases k with ⟨k, hk⟩
          simp [Functor.mapAut, braidGenerator, tensorIso_hom, tensorLeft, id_tensorHom]
        simpa only [hg] using hh

end PropertyF.Ground.CentreCalculus
