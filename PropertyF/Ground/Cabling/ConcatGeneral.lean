module
public import PropertyF.Ground.Cabling.ConcatLeft
open CategoryTheory CategoryTheory.MonoidalCategory
open PropertyF.Ground.Calculus
@[expose] public noncomputable section
namespace PropertyF
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [Abelian C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]

set_option backward.isDefEq.respectTransparency false in
/-- The right-recursive power comparison satisfies the same left-successor
coherence as the standard comparison. -/
theorem concatPowerIso_succ_left (X : C) (a b : ℕ) :
    (concatPowerIso X (a+1) b).hom ≫
      eqToHom (congrArg (tensorPower X) (by omega : (a+1)+b=(a+b)+1)) =
    ((α_ X (tensorPower X a) (tensorPower X b)) ≪≫
      (Iso.refl X ⊗ᵢ concatPowerIso X a b)).hom := by
  induction b with
  | zero =>
    simp only [eqToHom_refl, Category.comp_id]
    change (ρ_ (X ⊗ tensorPower X a)).hom =
      ((α_ X (tensorPower X a) (𝟙_ C)) ≪≫ (Iso.refl X ⊗ᵢ ρ_ (tensorPower X a))).hom
    dsimp only [Iso.trans_hom, tensorIso_hom, Iso.refl_hom]
    monoidal
  | succ b ih =>
    let p := (a+1)+b
    let q := (a+b)+1
    have hab : p=q := by dsimp [p,q]; omega
    have hnatGen (p q : ℕ) (h : p = q) :
        (appendIso X p).hom ≫ eqToHom (congrArg (fun v => tensorPower X (v+1)) h) =
          (eqToHom (congrArg (tensorPower X) h) ▷ X) ≫ (appendIso X q).hom := by
      cases h
      simp
    have hnat : (appendIso X p).hom ≫
        eqToHom (congrArg (tensorPower X) (by omega : (a+1)+(b+1)=(a+(b+1))+1)) =
        (eqToHom (congrArg (tensorPower X) hab) ▷ X) ≫ (appendIso X q).hom :=
      hnatGen p q hab
    have ih' : (concatPowerIso X (a+1) b).hom ≫ eqToHom (congrArg (tensorPower X) hab) =
      ((α_ X (tensorPower X a) (tensorPower X b)) ≪≫
        (Iso.refl X ⊗ᵢ concatPowerIso X a b)).hom := ih
    have hl : (concatPowerIso X (a+1) (b+1)).hom =
      ((𝟙 (tensorPower X (a+1)) ⊗ₘ (appendIso X b).inv) ≫
        (α_ (tensorPower X (a+1)) (tensorPower X b) X).inv ≫
        ((concatPowerIso X (a+1) b).hom ▷ X) ≫ (appendIso X p).hom) := by
      dsimp [concatPowerIso, tensorIso_hom, Iso.trans_hom, Iso.symm_hom]
      simp [tensorHom_id, p]
    rw [hl]
    simp only [Category.assoc, hnat, ← comp_whiskerRight_assoc, ih']
    rw [appendIso_succ]
    dsimp only [concatPowerIso, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv,
      tensorIso_hom, tensorIso_inv, Iso.refl_hom, Iso.refl_inv, tensorPower]
    monoidal
/-- The right-recursive and standard tensor-power normalizations agree for
all block lengths. -/
theorem concatPowerIso_eq (X : C) (a b : ℕ) :
    concatPowerIso X a b = tensorPowerTensorIso X a b := by
  induction a with
  | zero => exact concatPowerIso_eq_zero_left X b
  | succ a ih =>
    apply Iso.ext
    apply (cancel_mono (eqToHom (congrArg (tensorPower X)
      (by omega : (a+1)+b=(a+b)+1)))).mp
    rw [concatPowerIso_succ_left, powerTensor_succ_general, ih]
end PropertyF
