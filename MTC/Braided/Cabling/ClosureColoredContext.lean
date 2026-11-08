module
public import MTC.Braided.Cabling.ClosureColoredWords

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace MTC.Braided
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- Flatten three consecutive blocks by joining the last two first. -/
def rightTripleFlatten (X : C) (a b t : ℕ) :
    tensorPower X a ⊗ (tensorPower X b ⊗ tensorPower X t) ≅
      tensorPower X (strandSum a (strandSum b t)) :=
  (Iso.refl (tensorPower X a) ⊗ᵢ joinPowerIso X b t) ≪≫
    joinPowerIso X a (strandSum b t)

/-- Flatten three consecutive blocks by joining the first two first. -/
def leftTripleFlatten (X : C) (a b t : ℕ) :
    (tensorPower X a ⊗ tensorPower X b) ⊗ tensorPower X t ≅
      tensorPower X (strandSum (strandSum a b) t) :=
  (joinPowerIso X a b ⊗ᵢ Iso.refl (tensorPower X t)) ≪≫
    joinPowerIso X (strandSum a b) t

/-- Either grouping gives the same flattening, with the canonical associator. -/
theorem leftTripleFlatten_heq (X : C) (a b t : ℕ) :
    leftTripleFlatten X a b t ≍
      (α_ (tensorPower X a) (tensorPower X b) (tensorPower X t)) ≪≫
        rightTripleFlatten X a b t := by
  have ht := iso_trans_eqToIso_heq (leftTripleFlatten X a b t)
    (congrArg (tensorPower X) (strandSum_assoc a b t))
  have ha := joinPowerIso_assoc X a b t
  rw [← Iso.trans_assoc] at ha
  change leftTripleFlatten X a b t ≪≫ _ =
    (α_ (tensorPower X a) (tensorPower X b) (tensorPower X t)) ≪≫
      rightTripleFlatten X a b t at ha
  exact ht.symm.trans (heq_of_eq ha)

set_option backward.isDefEq.respectTransparency false in
/-- A crossing of the first two blocks can be evaluated after grouping them,
with the third block carried along unchanged. -/
theorem rightTripleCross_heq (X : C) (a b t : ℕ) [BraidedCategory C] :
    ((rightTripleFlatten X a b t).symm ≪≫
      (α_ (tensorPower X a) (tensorPower X b) (tensorPower X t)).symm ≪≫
      ((β_ (tensorPower X a) (tensorPower X b)) ⊗ᵢ Iso.refl (tensorPower X t)) ≪≫
      (α_ (tensorPower X b) (tensorPower X a) (tensorPower X t)) ≪≫
      rightTripleFlatten X b a t) ≍
    ((leftTripleFlatten X a b t).symm ≪≫
      ((β_ (tensorPower X a) (tensorPower X b)) ⊗ᵢ Iso.refl (tensorPower X t)) ≪≫
      leftTripleFlatten X b a t) := by
  have ha := leftTripleFlatten_heq X a b t
  have hb := leftTripleFlatten_heq X b a t
  have hc : ((rightTripleFlatten X a b t).symm ≪≫
      (α_ (tensorPower X a) (tensorPower X b) (tensorPower X t)).symm ≪≫
      ((β_ (tensorPower X a) (tensorPower X b)) ⊗ᵢ Iso.refl (tensorPower X t)) ≪≫
      (α_ (tensorPower X b) (tensorPower X a) (tensorPower X t)) ≪≫
      rightTripleFlatten X b a t) =
    (((α_ (tensorPower X a) (tensorPower X b) (tensorPower X t)) ≪≫
        rightTripleFlatten X a b t).symm ≪≫
      ((β_ (tensorPower X a) (tensorPower X b)) ⊗ᵢ Iso.refl (tensorPower X t)) ≪≫
      ((α_ (tensorPower X b) (tensorPower X a) (tensorPower X t)) ≪≫
        rightTripleFlatten X b a t)) := by
    apply Iso.ext
    simp [Iso.trans_hom, Iso.trans_inv, Category.assoc]
  apply HEq.trans (heq_of_eq hc)
  congr 2
  all_goals try exact ha.symm
  all_goals try exact hb.symm
  all_goals simp [strandSum_eq_add, Nat.add_assoc]

set_option backward.isDefEq.respectTransparency false in
/-- Grouped crossing is a flattened two-block crossing with an identity suffix. -/
theorem leftTripleCross_eq (X : C) (a b t : ℕ) [BraidedCategory C] :
    ((leftTripleFlatten X a b t).symm ≪≫
      ((β_ (tensorPower X a) (tensorPower X b)) ⊗ᵢ Iso.refl (tensorPower X t)) ≪≫
      leftTripleFlatten X b a t) =
    ((joinPowerIso X (strandSum a b) t).symm ≪≫
      (((joinPowerIso X a b).symm ≪≫ β_ (tensorPower X a) (tensorPower X b) ≪≫
        joinPowerIso X b a) ⊗ᵢ Iso.refl (tensorPower X t)) ≪≫
      joinPowerIso X (strandSum b a) t) := by
  apply Iso.ext
  simp only [leftTripleFlatten, Iso.trans_hom, Iso.symm_hom, Iso.trans_inv,
    tensorIso_hom, tensorIso_inv, Iso.refl_hom, Iso.refl_inv, tensorHom_id,
    Category.assoc]
  monoidal
