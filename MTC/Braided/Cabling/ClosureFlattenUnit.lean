module
public import MTC.Braided.Cabling.ClosureCommonInterface

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace MTC.Braided
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C] [Abelian C]

set_option backward.isDefEq.respectTransparency false in
/-- Concatenating a zero-length tensor power is the right unitor. -/
theorem tensorPowerTensorIso_zero (X : C) : ∀ k : ℕ,
    tensorPowerTensorIso X k 0 = ρ_ (tensorPower X k)
  | 0 => by
    apply Iso.ext
    simp [tensorPowerTensorIso, tensorPower, unitors_equal]
  | k+1 => by
    have ih := tensorPowerTensorIso_zero X k
    apply Iso.ext
    simp only [tensorPowerTensorIso, tensorPower, Iso.trans_hom, tensorIso_hom,
      Iso.refl_hom, id_tensorHom]
    rw [ih]
    change ((α_ X (tensorPower X k) (𝟙_ C)) ≪≫ (Iso.refl X ⊗ᵢ ρ_ (tensorPower X k))).hom = (ρ_ (X ⊗ tensorPower X k)).hom
    simp only [Iso.trans_hom, tensorIso_hom, Iso.refl_hom, id_tensorHom]
    monoidal


end MTC.Braided
