module
public import PropertyF.Ground.Cabling.AllInsert
open CategoryTheory CategoryTheory.MonoidalCategory
open PropertyF.Ground.Calculus
@[expose] public noncomputable section
namespace PropertyF
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [Abelian C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]

/-- Right-recursive tensor-power comparison, valid at every strand count. -/
def concatPowerIso (X : C) (a : ℕ) : ∀ b : ℕ,
    tensorPower X a ⊗ tensorPower X b ≅ tensorPower X (a+b)
  | 0 => ρ_ (tensorPower X a)
  | b + 1 => (Iso.refl (tensorPower X a) ⊗ᵢ (appendIso X b).symm) ≪≫
      (α_ (tensorPower X a) (tensorPower X b) X).symm ≪≫
      (concatPowerIso X a b ⊗ᵢ Iso.refl X) ≪≫ appendIso X (a+b)

/-- General right insertion is conjugation by this comparison isomorphism. -/
theorem addRightAutAllIter_hom (X : C) (m k : ℕ) (a : Aut (tensorPower X m)) :
    (addRightAutAllIter X m k a).asIso.hom =
      (concatPowerIso X m k).inv ≫ (a.asIso.hom ▷ tensorPower X k) ≫
        (concatPowerIso X m k).hom := by
  induction k with
  | zero =>
    change a.asIso.hom = (ρ_ (tensorPower X m)).inv ≫ (a.asIso.hom ▷ (𝟙_ C)) ≫
      (ρ_ (tensorPower X m)).hom
    monoidal
  | succ k ih =>
    change (appendIso X (m+k)).inv ≫ (((addRightAutAllIter X m k a).asIso.hom) ▷ X) ≫
      (appendIso X (m+k)).hom = _
    rw [ih]
    dsimp only [concatPowerIso, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv,
      tensorIso_hom, tensorIso_inv, Iso.refl_hom, Iso.refl_inv]
    simp only [id_tensorHom, tensorHom_id, comp_whiskerRight, Category.assoc]
    simp only [whisker_exchange_assoc]
    rw [← associator_naturality_left_assoc]
    simp
end PropertyF
