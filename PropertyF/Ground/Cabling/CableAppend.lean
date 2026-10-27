module
public import PropertyF.Ground.Cabling.ConcatGeneral
public import PropertyF.Ground.Cabling.CableClass
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
@[expose] public noncomputable section
namespace PropertyF
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [Abelian C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]

/-- Tensoring a cabled braid map on the right by an arbitrary tensor-power
block remains a cabled braid map under standard normalization. -/
theorem cableHom_append_right (X : C) {m n : ℕ}
    (f : tensorPower X m ⟶ tensorPower X n) (hf : cableHom X m n f) (k : ℕ) :
    cableHom X (m+k) (n+k)
      ((tensorPowerTensorIso X m k).inv ≫ (f ▷ tensorPower X k) ≫
        (tensorPowerTensorIso X n k).hom) := by
  obtain ⟨h, a, hf⟩ := hf
  subst n
  simp only [eqToHom_refl, Category.comp_id] at hf
  subst f
  let b : braidImageAllSubgroup X (m+k) :=
    ⟨addRightAutAllIter X m k a.val, addRightAutAllIter_mem X m a.val a.property k⟩
  refine ⟨rfl, b, ?_⟩
  simp only [eqToHom_refl, Category.comp_id]
  change (tensorPowerTensorIso X m k).inv ≫ (a.val.asIso.hom ▷ tensorPower X k) ≫
    (tensorPowerTensorIso X m k).hom = (addRightAutAllIter X m k a.val).asIso.hom
  rw [addRightAutAllIter_hom, concatPowerIso_eq]
end PropertyF
