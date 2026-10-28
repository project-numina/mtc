module
public import PropertyF.Definitions
public import Mathlib.CategoryTheory.Endomorphism
public import Mathlib.CategoryTheory.Conj

/-!
# Braid images of isomorphic objects

Tensor powers transport adjacent braid generators along an isomorphism. Conjugation
by these tensor-power isomorphisms identifies the associated braid-image groups.
-/
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.BraidedCategory
@[expose] public noncomputable section
namespace PropertyF.Ground.Modular
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
/-- Tensor powers transport an isomorphism between objects. -/
def tensorPowerIso {X Y : C} (f : X ≅ Y) : ∀ n, tensorPower X n ≅ tensorPower Y n
  | 0 => Iso.refl _
  | n + 1 => f ⊗ᵢ tensorPowerIso f n

/-- Braiding the first two strands of a right-associated tensor product. -/
abbrev firstBraiding (X A : C) : X ⊗ (X ⊗ A) ≅ X ⊗ (X ⊗ A) :=
  (α_ X X A).symm ≪≫ ((β_ X X) ⊗ᵢ Iso.refl A) ≪≫ α_ X X A

/-- The first braid generator is the associated braiding on the first two strands. -/
lemma braidGenerator_zero (X : C) (n : ℕ) :
    (braidGenerator X n 0).asIso.hom =
      (firstBraiding X (tensorPower X n)).hom :=
  Nat.casesOn n rfl (fun _ ↦ rfl)

/-- Naturality of the first adjacent braiding, with its associators. -/
lemma braid_first {X Y A B : C} (f : X ≅ Y) (g : A ≅ B) :
    (firstBraiding X A).hom ≫ (f ⊗ᵢ f ⊗ᵢ g).hom =
      (f ⊗ᵢ f ⊗ᵢ g).hom ≫ (firstBraiding Y B).hom := by
  simp only [firstBraiding, Iso.trans_hom, Iso.symm_hom, tensorIso_hom, Iso.refl_hom, Category.assoc]
  rw [← associator_naturality, associator_inv_naturality_assoc]
  simp only [← Category.assoc, tensorHom_comp_tensorHom, Category.id_comp, Category.comp_id,
    braiding_naturality]
variable {X Y : C} (f : X ≅ Y)

/-- Every adjacent braid generator is natural in an object isomorphism. -/
theorem braidGenerator_natural (n : ℕ)
    (i : Fin (n + 1)) :
    (braidGenerator X n i).asIso.hom ≫ (tensorPowerIso f (n + 2)).hom =
      (tensorPowerIso f (n + 2)).hom ≫ (braidGenerator Y n i).asIso.hom := by
  induction n with
  | zero => exact Fin.cases (braid_first f (tensorPowerIso f 0)) (fun j ↦ Fin.elim0 j) i
  | succ n ih =>
    refine Fin.cases (braid_first f (tensorPowerIso f (n + 1))) (fun j ↦ ?_) i
    change (𝟙 X ⊗ₘ (braidGenerator X n j).asIso.hom) ≫
        (f.hom ⊗ₘ (tensorPowerIso f (n + 2)).hom) =
      (f.hom ⊗ₘ (tensorPowerIso f (n + 2)).hom) ≫
        (𝟙 Y ⊗ₘ (braidGenerator Y n j).asIso.hom)
    simp only [tensorHom_comp_tensorHom, Category.id_comp, Category.comp_id, ih]

/-- Conjugation by the tensor-power isomorphism takes generators to generators. -/
theorem conjugate_braidGenerator (n : ℕ)
    (i : Fin (n + 1)) :
    (tensorPowerIso f (n + 2)).conjAut (braidGenerator X n i) = braidGenerator Y n i :=
  Aut.ext (Iso.ext (by
    simp only [Iso.conjAut_apply, Iso.trans_hom, Iso.symm_hom]
    rw [braidGenerator_natural, Iso.inv_hom_id_assoc]))

include f in
/-- Isomorphic objects have isomorphic braid-image groups. -/
def braidImageIso (n : ℕ) : braidImage X n ≃* braidImage Y n := by
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
