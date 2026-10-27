module
public import PropertyF.Ground.Cabling.MoveHeadInsert
open CategoryTheory CategoryTheory.MonoidalCategory
open PropertyF.Ground.Calculus
@[expose] public noncomputable section
namespace PropertyF
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [Abelian C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]

/-- Right-unit normalization of a tensor power is the usual right unitor. -/
theorem powerTensor_zero_right (X : C) (b : ℕ) :
    (tensorPowerTensorIso X b 0).hom = (ρ_ (tensorPower X b)).hom := by
  induction b with
  | zero =>
    change (λ_ (𝟙_ C)).hom = (ρ_ (𝟙_ C)).hom
    monoidal
  | succ b ih =>
    have h : (tensorPowerTensorIso X (b+1) 0).hom =
        ((α_ X (tensorPower X b) (𝟙_ C)) ≪≫
          (Iso.refl X ⊗ᵢ tensorPowerTensorIso X b 0)).hom := by rfl
    rw [h]
    change (α_ X (tensorPower X b) (𝟙_ C)).hom ≫
      (𝟙 X ⊗ₘ (tensorPowerTensorIso X b 0).hom) = (ρ_ (X ⊗ tensorPower X b)).hom
    rw [ih]
    monoidal

/-- Normalizing a right singleton agrees with calculus' append isomorphism. -/
theorem powerTensor_one_right (X : C) (n : ℕ) :
    tensorPowerTensorIso X n 1 =
      (Iso.refl (tensorPower X n) ⊗ᵢ ρ_ X) ≪≫ appendIso X n := by
  induction n with
  | zero =>
    apply Iso.ext
    change (λ_ (tensorPower X 1)).hom =
      ((Iso.refl (𝟙_ C) ⊗ᵢ ρ_ X) ≪≫ ((λ_ X) ≪≫ (ρ_ X).symm)).hom
    dsimp only [tensorPower, Iso.trans_hom, Iso.symm_hom, tensorIso_hom, Iso.refl_hom]
    monoidal
  | succ n ih =>
    apply Iso.ext
    rw [powerTensor_succ]
    have hh := congrArg (fun e : _ ≅ _ => e.hom) ih
    change (α_ X (tensorPower X n) (tensorPower X 1)).hom ≫
      (𝟙 X ⊗ₘ (tensorPowerTensorIso X n 1).hom) = _
    rw [hh]
    rw [appendIso_succ]
    change (α_ X (tensorPower X n) (X ⊗ 𝟙_ C)).hom ≫
      (𝟙 X ⊗ₘ ((𝟙 (tensorPower X n) ⊗ₘ (ρ_ X).hom) ≫ (appendIso X n).hom)) =
      (𝟙 (X ⊗ tensorPower X n) ⊗ₘ (ρ_ X).hom) ≫
        (α_ X (tensorPower X n) X).hom ≫ (𝟙 X ⊗ₘ (appendIso X n).hom)
    monoidal
end PropertyF
