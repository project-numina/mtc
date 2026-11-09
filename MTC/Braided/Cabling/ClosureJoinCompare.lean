module
public import MTC.Braided.Cabling.ClosureJoinAssociativity

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace MTC.Braided
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

set_option backward.isDefEq.respectTransparency false in
 theorem tensorPowerTensorIso_zero_left_heq (X : C) (b : ℕ) :
    tensorPowerTensorIso X 0 b ≍ λ_ (tensorPower X b) := by
  unfold tensorPowerTensorIso
  exact cast_heq _ _

set_option backward.isDefEq.respectTransparency false in
 theorem tensorPowerTensorIso_succ_heq (X : C) (a b : ℕ) :
    tensorPowerTensorIso X (a+1) b ≍
      (α_ X (tensorPower X a) (tensorPower X b)) ≪≫
        (Iso.refl X ⊗ᵢ tensorPowerTensorIso X a b) := by
  conv_lhs => unfold tensorPowerTensorIso
  exact cast_heq _ _

set_option backward.isDefEq.respectTransparency false in
 theorem joinPowerIso_heq (X : C) : ∀ a b : ℕ,
    joinPowerIso X a b ≍ tensorPowerTensorIso X a b
  | 0, b => by
    exact (tensorPowerTensorIso_zero_left_heq X b).symm
  | a+1, b => by
    apply HEq.trans _ (tensorPowerTensorIso_succ_heq X a b).symm
    simp only [joinPowerIso]
    have ih := joinPowerIso_heq X a b
    congr 2
    all_goals simp [strandSum_eq_add, strandSum, tensorPower]

/-- A target transport does not change an isomorphism heterogeneously. -/
theorem iso_trans_eqToIso_heq {A B D : C} (f : A ≅ B) (h : B = D) :
    f ≪≫ eqToIso h ≍ f := by
  cases h
  simp

/-- The cast-free join and canonical tensor-power concatenation agree after
transporting their strand counts. -/
theorem joinPowerIso_eq_tensorPowerTensorIso (X : C) (a b : ℕ) :
    joinPowerIso X a b ≪≫ powerIndexIso X (strandSum_eq_add a b) =
      tensorPowerTensorIso X a b := by
  apply eq_of_heq
  exact (iso_trans_eqToIso_heq (joinPowerIso X a b) _).trans (joinPowerIso_heq X a b)
