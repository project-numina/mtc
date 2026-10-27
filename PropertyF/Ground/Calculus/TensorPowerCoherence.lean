module
public import PropertyF.Ground.Calculus.OverlapCoherence
public import PropertyF.Ground.Cabling.PowerGeneral

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

end PropertyF.Ground.Calculus
