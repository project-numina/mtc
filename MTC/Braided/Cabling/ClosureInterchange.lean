module
public import MTC.Braided.Cabling.ClosureCanonicalBlocks

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace MTC.Braided
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- A merge on the first two factors commutes with an independent change of
the third factor, with all reassociation made explicit. -/
theorem merge_iso_interchange {A B D E F : C} (e : A ⊗ B ≅ D) (f : E ≅ F) :
    (α_ A B E).symm ≪≫ (e ⊗ᵢ Iso.refl E) ≪≫ (Iso.refl D ⊗ᵢ f) =
      (Iso.refl A ⊗ᵢ (Iso.refl B ⊗ᵢ f)) ≪≫ (α_ A B F).symm ≪≫
        (e ⊗ᵢ Iso.refl F) := by
  apply Iso.ext
  simp only [Iso.trans_hom, Iso.symm_hom, tensorIso_hom, Iso.refl_hom,
    id_tensorHom, tensorHom_id]
  rw [← whisker_exchange]
  rw [associator_inv_naturality_right_assoc]

end MTC.Braided
