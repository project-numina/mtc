module
public import PropertyF.Definitions
public import Mathlib.CategoryTheory.Endomorphism
public import Mathlib.CategoryTheory.Conj
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.BraidedCategory
@[expose] public noncomputable section
namespace PropertyF.Ground.Modular
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
def tensorPowerIso {X Y : C} (f : X ≅ Y) : ∀ n, tensorPower X n ≅ tensorPower Y n
  | 0 => Iso.refl _
  | n + 1 => f ⊗ᵢ tensorPowerIso f n

/-- Naturality of the first adjacent braiding, with its associators. -/
lemma braid_first {X Y A B : C} (f : X ≅ Y) (g : A ≅ B) :
    ((α_ X X A).symm ≪≫ ((β_ X X) ⊗ᵢ Iso.refl A) ≪≫ α_ X X A).hom ≫
        (f ⊗ᵢ f ⊗ᵢ g).hom =
      (f ⊗ᵢ f ⊗ᵢ g).hom ≫
        ((α_ Y Y B).symm ≪≫ ((β_ Y Y) ⊗ᵢ Iso.refl B) ≪≫ α_ Y Y B).hom := by
  simp only [Iso.trans_hom, Iso.symm_hom, tensorIso_hom, Iso.refl_hom, Category.assoc]
  rw [← associator_naturality, associator_inv_naturality_assoc]
  simp only [← Category.assoc, tensorHom_comp_tensorHom, Category.id_comp, Category.comp_id,
    braiding_naturality]
/-- Every adjacent braid generator is natural in an object isomorphism. -/
theorem braidGenerator_natural {X Y : C} (f : X ≅ Y) (n : ℕ)
    (i : Fin (n + 1)) :
    (braidGenerator X n i).asIso.hom ≫ (tensorPowerIso f (n + 2)).hom =
      (tensorPowerIso f (n + 2)).hom ≫ (braidGenerator Y n i).asIso.hom := by
  induction n with
  | zero =>
    have hi : i = 0 := Fin.eq_zero i
    subst i
    exact braid_first f (tensorPowerIso f 0)
  | succ n ih =>
    rcases i with ⟨i, hi⟩
    cases i with
    | zero => exact braid_first f (tensorPowerIso f (n + 1))
    | succ i =>
      change (𝟙 X ⊗ₘ (braidGenerator X n ⟨i, Nat.lt_of_succ_lt_succ hi⟩).asIso.hom) ≫
          (f.hom ⊗ₘ (tensorPowerIso f (n + 2)).hom) =
        (f.hom ⊗ₘ (tensorPowerIso f (n + 2)).hom) ≫
          (𝟙 Y ⊗ₘ (braidGenerator Y n ⟨i, Nat.lt_of_succ_lt_succ hi⟩).asIso.hom)
      simp only [tensorHom_comp_tensorHom, Category.id_comp, Category.comp_id, ih]

/-- Conjugation by the tensor-power isomorphism takes generators to generators. -/
theorem conjugate_braidGenerator {X Y : C} (f : X ≅ Y) (n : ℕ)
    (i : Fin (n + 1)) :
    (tensorPowerIso f (n + 2)).conjAut (braidGenerator X n i) = braidGenerator Y n i := by
  apply Aut.ext
  apply Iso.ext
  simp only [Iso.conjAut_apply, Iso.trans_hom, Iso.symm_hom]
  rw [braidGenerator_natural, Iso.inv_hom_id_assoc]

/-- Isomorphic objects have isomorphic braid-image groups. -/
def braidImageIso {X Y : C} (f : X ≅ Y) (n : ℕ) : braidImage X n ≃* braidImage Y n := by
  let e := (tensorPowerIso f (n + 2)).conjAut
  have hm : (braidImage X n).map e.toMonoidHom = braidImage Y n := by
    rw [braidImage, MonoidHom.map_closure, ← Set.range_comp]
    have heq : (e ∘ braidGenerator X n) = braidGenerator Y n := by
      funext i
      exact conjugate_braidGenerator f n i
    change Subgroup.closure (Set.range (e ∘ braidGenerator X n)) = braidImage Y n
    rw [heq]
    rfl
  exact ((braidImage X n).equivMapOfInjective e.toMonoidHom e.injective).trans
    (MulEquiv.subgroupCongr hm)

end PropertyF.Ground.Modular
