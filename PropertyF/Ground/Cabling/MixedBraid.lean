module
public import PropertyF.Ground.Cabling.TensorComponents
public import PropertyF.Ground.Cabling.Naturality
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.BraidedCategory CategoryTheory.Limits
@[expose] public noncomputable section
namespace PropertyF
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]

def firstMixedBraid (A B R : C) : A ⊗ (B ⊗ R) ≅ B ⊗ (A ⊗ R) :=
  (α_ A B R).symm ≪≫ ((β_ A B) ⊗ᵢ Iso.refl R) ≪≫ α_ B A R

/-- The crossing is natural in its two independently varying strands. -/
theorem firstMixedBraid_natural {A B R Y S : C} (f : A ⟶ Y) (g : B ⟶ Y) (h : R ⟶ S) :
    (firstMixedBraid A B R).hom ≫ (g ⊗ₘ (f ⊗ₘ h)) =
      (f ⊗ₘ (g ⊗ₘ h)) ≫ (firstMixedBraid Y Y S).hom := by
  simp only [firstMixedBraid, Iso.trans_hom, Iso.symm_hom, tensorIso_hom, Iso.refl_hom, Category.assoc]
  rw [← associator_naturality, associator_inv_naturality_assoc]
  simp only [← Category.assoc, tensorHom_comp_tensorHom, Category.id_comp, Category.comp_id,
    braiding_naturality]

variable [Abelian C] [MonoidalPreadditive C]
attribute [local instance] Abelian.hasFiniteBiproducts

omit [MonoidalPreadditive C] in
set_option backward.isDefEq.respectTransparency false in
/-- The first crossing carries tensor products of block inclusions to the
corresponding tensor products with the first two factors interchanged. -/
theorem firstBraid_components {I : Type} [Fintype I] (f : I → C)
    (a b : I) (n : ℕ) (t : Fin n → I) :
    (biproduct.ι f a ⊗ₘ (biproduct.ι f b ⊗ₘ tupleTensorInclusion f n t)) ≫
      (braidGenerator (⨁ f) n 0).asIso.hom =
    (firstMixedBraid (f a) (f b) (tupleTensor f n t)).hom ≫
      (biproduct.ι f b ⊗ₘ (biproduct.ι f a ⊗ₘ tupleTensorInclusion f n t)) := by
  have hg : braidGenerator (⨁ f) n 0 = Aut.of (firstMixedBraid (⨁ f) (⨁ f) (tensorPower (⨁ f) n)) := by
    cases n <;> rfl
  rw [hg]
  simpa [firstMixedBraid, Category.assoc] using
    (firstMixedBraid_natural (biproduct.ι f a) (biproduct.ι f b) (tupleTensorInclusion f n t)).symm
omit [MonoidalPreadditive C] in
set_option backward.isDefEq.respectTransparency false in
/-- Prefixing a spectator strand transports a block crossing by one position. -/
theorem tailBraid_components {I : Type} [Fintype I] (f : I → C)
    (a : I) (n : ℕ) (i : Fin (n + 1)) (U V : C)
    (u : U ⟶ tensorPower (⨁ f) (n + 2))
    (v : V ⟶ tensorPower (⨁ f) (n + 2)) (g : U ⟶ V)
    (h : u ≫ (braidGenerator (⨁ f) n i).asIso.hom = g ≫ v) :
    (biproduct.ι f a ⊗ₘ u) ≫ (braidGenerator (⨁ f) (n + 1) i.succ).asIso.hom =
      (𝟙 (f a) ⊗ₘ g) ≫ (biproduct.ι f a ⊗ₘ v) := by
  rcases i with ⟨i, hi⟩
  have hg : braidGenerator (⨁ f) (n + 1) (⟨i, hi⟩ : Fin (n+1)).succ =
      Aut.of (Iso.refl (⨁ f) ⊗ᵢ (braidGenerator (⨁ f) n ⟨i, hi⟩).asIso) := by
    apply Aut.ext
    apply Iso.ext
    simp [braidGenerator, tensorIso_hom, id_tensorHom]
  rw [hg]
  simp only [tensorIso_hom, Iso.refl_hom, tensorHom_comp_tensorHom,
    Category.id_comp, Category.comp_id, h]

end PropertyF
