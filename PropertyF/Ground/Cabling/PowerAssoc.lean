module
public import PropertyF.Ground.Cabling.CableTensor
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open PropertyF.Ground.Calculus
@[expose] public noncomputable section
namespace PropertyF
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [Abelian C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]

set_option backward.isDefEq.respectTransparency false in
/-- Tensor-power normalization respects associativity, including transport of
the total strand count. -/
theorem powerTensor_assoc (X : C) (a b c : ℕ) :
    ((tensorPowerTensorIso X a b ⊗ᵢ Iso.refl (tensorPower X c)) ≪≫
      tensorPowerTensorIso X (a+b) c).hom ≫
        eqToHom (congrArg (tensorPower X) (Nat.add_assoc a b c)) =
      ((α_ (tensorPower X a) (tensorPower X b) (tensorPower X c)) ≪≫
        (Iso.refl (tensorPower X a) ⊗ᵢ tensorPowerTensorIso X b c) ≪≫
          tensorPowerTensorIso X a (b+c)).hom := by
  rw [← concatPowerIso_eq X a b, ← concatPowerIso_eq X (a+b) c, ← concatPowerIso_eq X b c,
    ← concatPowerIso_eq X a (b+c)]
  induction c with
  | zero =>
    simp only [concatPowerIso, tensorPower, eqToHom_refl, Category.comp_id]
    dsimp only [Iso.trans_hom, tensorIso_hom, Iso.refl_hom]
    monoidal
  | succ c ih =>
    have h₁ : tensorPower X ((a+b)+c) = tensorPower X (a+(b+c)) :=
      congrArg (tensorPower X) (Nat.add_assoc a b c)
    have h₂ : tensorPower X ((a+b)+(c+1)) = tensorPower X (a+(b+(c+1))) :=
      congrArg (tensorPower X) (Nat.add_assoc a b (c+1))
    have hnatGen (p q : ℕ) (h : p = q) :
        (appendIso X p).hom ≫ eqToHom (congrArg (fun v => tensorPower X (v+1)) h) =
          (eqToHom (congrArg (tensorPower X) h) ▷ X) ≫ (appendIso X q).hom := by
      cases h
      simp
    have hnat : (appendIso X ((a+b)+c)).hom ≫ eqToHom h₂ =
        (eqToHom h₁ ▷ X) ≫ (appendIso X (a+(b+c))).hom := hnatGen _ _ (Nat.add_assoc a b c)
    simp only [concatPowerIso, Iso.trans_hom, Iso.symm_hom, tensorIso_hom, Iso.refl_hom]
    simp only [Category.assoc, hnat, ← comp_whiskerRight_assoc]
    simp only [id_tensorHom, tensorHom_id, whiskerLeft_comp, Category.assoc]
    simp only [← whiskerLeft_comp_assoc, Iso.hom_inv_id, id_whiskerLeft, Category.id_comp]
    rw [← whisker_exchange_assoc (concatPowerIso X a b).hom (appendIso X c).inv]
    rw [associator_inv_naturality_left_assoc]
    simp only [← comp_whiskerRight_assoc]
    simp only [Iso.trans_hom, tensorIso_hom, Iso.refl_hom, id_tensorHom, tensorHom_id, Category.assoc] at ih
    change (concatPowerIso X a b).hom ▷ tensorPower X c ≫
      (concatPowerIso X (a+b) c).hom ≫ eqToHom h₁ =
      (α_ (tensorPower X a) (tensorPower X b) (tensorPower X c)).hom ≫
        (tensorPower X a ◁ (concatPowerIso X b c).hom) ≫
          (concatPowerIso X a (b+c)).hom at ih
    rw [ih]
    simp only [comp_whiskerRight, whiskerLeft_comp, Category.assoc]
    slice_rhs 5 6 =>
      rw [← whiskerLeft_comp]
      change tensorPower X a ◁ ((appendIso X (b+c)).hom ≫ (appendIso X (b+c)).inv)
      rw [Iso.hom_inv_id, whiskerLeft_id]
    simp only [Category.id_comp, Category.comp_id]
    monoidal
end PropertyF
