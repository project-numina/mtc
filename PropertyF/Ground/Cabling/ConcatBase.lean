module
public import PropertyF.Ground.Cabling.ConcatPower
open CategoryTheory CategoryTheory.MonoidalCategory
open PropertyF.Ground.Calculus
@[expose] public noncomputable section
namespace PropertyF
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [Abelian C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]

/-- Right-recursive and standard tensor-power comparisons agree when the
right block is empty. -/
theorem concatPowerIso_zero (X : C) (m : ℕ) :
    concatPowerIso X m 0 = tensorPowerTensorIso X m 0 := by
  apply Iso.ext
  change (ρ_ (tensorPower X m)).hom = (tensorPowerTensorIso X m 0).hom
  exact (powerTensor_zero_right X m).symm

/-- The same comparisons agree for a single right strand. -/
theorem concatPowerIso_one (X : C) (m : ℕ) :
    concatPowerIso X m 1 = tensorPowerTensorIso X m 1 := by
  apply Iso.ext
  rw [powerTensor_one_right]
  dsimp only [concatPowerIso, appendIso, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom,
    Iso.symm_inv, tensorIso_hom, tensorIso_inv, Iso.refl_hom, Iso.refl_inv, tensorPower]
  change (𝟙 (tensorPower X m) ⊗ₘ ((ρ_ X).hom ≫ (λ_ X).inv)) ≫
    (α_ (tensorPower X m) (𝟙_ C) X).inv ≫
      ((ρ_ (tensorPower X m)).hom ⊗ₘ 𝟙 X) ≫ (appendIso X m).hom =
    (𝟙 (tensorPower X m) ⊗ₘ (ρ_ X).hom) ≫ (appendIso X m).hom
  monoidal
end PropertyF
