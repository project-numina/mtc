module
public import PropertyF.Ground.Cabling.PrefixCompare
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
@[expose] public noncomputable section
namespace PropertyF
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [Abelian C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]

/-- The tensor product of two cabled braid maps is again a cabled braid map. -/
theorem cableHom_tensor (X : C) {a b c d : ℕ}
    (f : tensorPower X a ⟶ tensorPower X b) (g : tensorPower X c ⟶ tensorPower X d)
    (hf : cableHom X a b f) (hg : cableHom X c d g) :
    cableHom X (a+c) (b+d)
      ((tensorPowerTensorIso X a c).inv ≫ (f ⊗ₘ g) ≫ (tensorPowerTensorIso X b d).hom) := by
  have h₁ := cableHom_append_right X f hf c
  have h₂ := cableHom_prepend_left X g hg b
  have h := cableHom_comp X h₁ h₂
  simpa only [Category.assoc, Iso.hom_inv_id_assoc, tensorHom_def] using h
end PropertyF
