module
public import PropertyF.Definitions
public import Mathlib.Tactic

/-! Involutivity of the actual tensor-power generators for a self-centralizing object. -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.CentreCalculus
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]

set_option backward.isDefEq.respectTransparency false in
/-- Self-transparency makes each adjacent braid generator an involution. -/
theorem braidGenerator_involutive (X : C)
    (hX : (β_ X X).hom ≫ (β_ X X).hom = 𝟙 (X ⊗ X)) :
    ∀ (n : ℕ) (i : Fin (n + 1)), braidGenerator X n i * braidGenerator X n i = 1 := by
  have hzero (n : ℕ) : braidGenerator X n ⟨0, Nat.zero_lt_succ n⟩ * braidGenerator X n ⟨0, Nat.zero_lt_succ n⟩ = 1 := by
    apply Aut.ext
    apply Iso.ext
    simp only [Aut.mul_asIso, Aut.one_asIso, Iso.trans_hom, Iso.refl_hom]
    cases n <;>
      simp only [braidGenerator, Iso.trans_hom, Iso.symm_hom, tensorIso_hom,
        Iso.refl_hom, tensorHom_id, Category.assoc, Iso.hom_inv_id_assoc] <;>
      rw [← Category.assoc ((β_ X X).hom ▷ _) ((β_ X X).hom ▷ _),
        ← comp_whiskerRight, hX, id_whiskerRight, Category.id_comp, Iso.inv_hom_id]

  intro n
  induction n with
  | zero =>
    intro i
    have hi : i = 0 := Fin.eq_zero i
    subst i
    exact hzero 0
  | succ n ih =>
    intro i
    refine Fin.cases (hzero (n + 1)) (fun j => ?_) i
    have h := congrArg (fun a : Aut (tensorPower X (n + 2)) => a.asIso.hom) (ih j)
    simp only [Aut.mul_asIso, Aut.one_asIso, Iso.trans_hom, Iso.refl_hom] at h
    apply Aut.ext
    apply Iso.ext
    simp only [Aut.mul_asIso, Aut.one_asIso, Iso.trans_hom, Iso.refl_hom]
    cases j with
    | mk j hj =>
      simp only [Fin.succ, braidGenerator, tensorIso_hom, Iso.refl_hom, id_tensorHom]
      rw [← whiskerLeft_comp, h, whiskerLeft_id]
      rfl

end PropertyF.Ground.CentreCalculus
