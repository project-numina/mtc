module
public import PropertyF.Ground.Calculus.OverlapCoherence
public import PropertyF.Ground.Cabling.PowerGeneral
public import PropertyF.Ground.Calculus.ReversePower

/-! Coherence of the canonical tensor-power concatenation isomorphisms. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.Calculus
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [Abelian C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]

omit [Linear ℂ C] [MonoidalLinear ℂ C] in
set_option backward.isDefEq.respectTransparency false in
/-- Repeated left insertion agrees with canonical concatenation, up to the
arithmetic equality of strand counts. -/
theorem insertLeftPowerIso_eq_concat (X : C) (n k : ℕ) :
    (insertLeftPowerIso X n k).hom =
      (tensorPowerTensorIso X k (n + 2)).hom ≫
        eqToHom (congrArg (tensorPower X) (by omega : k + (n + 2) = (n + k) + 2)) := by
  induction k with
  | zero =>
    change (λ_ (tensorPower X (n + 2))).hom = _
    symm
    apply castIso_hom_comp
  | succ k ih =>
    have h₁ : (k + 1) + (n + 2) = (k + (n + 2)) + 1 := by omega
    have h₂ : k + (n + 2) = (n + k) + 2 := by omega
    have hcomp :
        eqToHom (congrArg (tensorPower X) (by omega : (k + 1) + (n + 2) = (n + (k + 1)) + 2)) =
        eqToHom (congrArg (tensorPower X) h₁) ≫
          (X ◁ eqToHom (congrArg (tensorPower X) h₂)) := by
      rw [whiskerLeft_eqToHom, eqToHom_trans]
    rw [hcomp, ← Category.assoc, powerTensor_succ_general]
    simp only [insertLeftPowerIso, Iso.trans_hom, tensorIso_hom, Iso.refl_hom, id_tensorHom]
    rw [ih, whiskerLeft_comp, Category.assoc]

omit [Linear ℂ C] [MonoidalLinear ℂ C] in
set_option backward.isDefEq.respectTransparency false in
/-- Cast-free reverse concatenation agrees with the standard tensor-power
concatenation up to the commutativity of the length indices. -/
theorem reverseConcat_eq_concat (X : C) (a b : ℕ) :
    (reverseConcatIso X a b).hom =
      (tensorPowerTensorIso X a b).hom ≫
        eqToHom (congrArg (tensorPower X) (by omega : a + b = b + a)) := by
  induction a with
  | zero =>
    change (λ_ (tensorPower X b)).hom = _
    symm
    apply castIso_hom_comp
  | succ a ih =>
    have h₁ : (a + 1) + b = (a + b) + 1 := by omega
    have h₂ : a + b = b + a := by omega
    have hcomp :
        eqToHom (congrArg (tensorPower X) (by omega : (a + 1) + b = b + (a + 1))) =
        eqToHom (congrArg (tensorPower X) h₁) ≫
          (X ◁ eqToHom (congrArg (tensorPower X) h₂)) := by
      rw [whiskerLeft_eqToHom, eqToHom_trans]
    rw [hcomp, ← Category.assoc, powerTensor_succ_general]
    simp only [reverseConcatIso, Iso.trans_hom, tensorIso_hom, Iso.refl_hom, id_tensorHom]
    rw [ih, whiskerLeft_comp, Category.assoc]

end PropertyF.Ground.Calculus
