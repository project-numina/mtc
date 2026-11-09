module
public import MTC.Braided.Cabling.ClosureRecursiveFlatten

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace MTC.Braided
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

theorem strandSum_assoc (a b c : ℕ) :
    strandSum (strandSum a b) c = strandSum a (strandSum b c) := by
  simp only [strandSum_eq_add, Nat.add_assoc]

set_option backward.isDefEq.respectTransparency false in
set_option maxRecDepth 4096 in
/-- Joining three powers agrees with reassociating and joining from the right. -/
theorem joinPowerIso_assoc (X : C) : ∀ a b c : ℕ,
    ((joinPowerIso X a b ⊗ᵢ Iso.refl (tensorPower X c)) ≪≫
      joinPowerIso X (strandSum a b) c ≪≫
      powerIndexIso X (strandSum_assoc a b c)) =
    (α_ (tensorPower X a) (tensorPower X b) (tensorPower X c)) ≪≫
      (Iso.refl (tensorPower X a) ⊗ᵢ joinPowerIso X b c) ≪≫
      joinPowerIso X a (strandSum b c)
  | 0, b, c => by
    apply Iso.ext
    simp only [strandSum, joinPowerIso, powerIndexIso, Iso.trans_hom,
      tensorIso_hom, Iso.refl_hom, id_tensorHom, tensorHom_id,
      eqToIso.hom, eqToHom_refl, Category.comp_id]
    monoidal
  | a+1, b, c => by
    apply Iso.ext
    simp only [strandSum, joinPowerIso, powerIndexIso, Iso.trans_hom,
      tensorIso_hom, Iso.refl_hom, id_tensorHom, tensorHom_id,
      eqToIso.hom, whiskerLeft_eqToHom, Category.assoc]
    have ih := congrArg Iso.hom (joinPowerIso_assoc X a b c)
    simp only [Iso.trans_hom, tensorIso_hom, Iso.refl_hom, id_tensorHom,
      tensorHom_id, powerIndexIso, eqToIso.hom, Category.assoc] at ih
    have hh : (X ◁ ((joinPowerIso X a b).hom ▷ tensorPower X c ≫
        (joinPowerIso X (strandSum a b) c).hom ≫
          eqToHom (congrArg (tensorPower X) (strandSum_assoc a b c)))) =
        X ◁ ((α_ (tensorPower X a) (tensorPower X b) (tensorPower X c)).hom ≫
          tensorPower X a ◁ (joinPowerIso X b c).hom ≫
            (joinPowerIso X a (strandSum b c)).hom) := congrArg (fun f => X ◁ f) ih
    simp only [whiskerLeft_comp, whiskerLeft_eqToHom, Category.assoc] at hh
    monoidal_nf
    simp only [Iso.trans_hom, whiskerLeftIso_hom, whiskerRightIso_hom,
      Iso.refl_hom, whiskerLeft_id, whiskerRight_id, Category.comp_id,
      Category.id_comp, Iso.inv_hom_id_assoc, Iso.hom_inv_id_assoc, Category.assoc] at *
    simp only [whiskerLeft_id, id_whiskerRight, Iso.symm_hom, Iso.inv_hom_id_assoc,
      Category.id_comp, Category.comp_id] at *
    rw [hh]
    monoidal
