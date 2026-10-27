module
public import PropertyF.Ground.Dimensions.TensorTrace
public import PropertyF.Ground.Calculus.PartialTrace

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
open PropertyF.Ground.Calculus
namespace PropertyF.Ground.Dimensions
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
  [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]

/-- Closing the right tensor factor and then the left gives the total pivotal trace. -/
theorem rightTrace_partialTrace (p : PivotalStructure (C := C)) (X Y : C) (f : End (X ⊗ Y)) :
  p.rightTrace (rightPartialTrace p X Y f).asHom = p.rightTrace f.asHom := by
  apply End.homEquiv.injective
  change (p.rightTrace (rightPartialTrace p X Y f).asHom).asHom = (p.rightTrace f.asHom).asHom
  rw [rightTrace_tensor_pairing]
  simp only [PivotalStructure.rightTrace, rightPartialTrace, LinearMap.coe_mk, AddHom.coe_mk]
  have hc : η_ (X ⊗ Y) ((Yᘁ) ⊗ (Xᘁ)) =
      η_ X (Xᘁ) ⊗≫ (X ◁ η_ Y (Yᘁ)) ▷ (Xᘁ) ⊗≫ 𝟙 _ := rfl
  have he : ε_ ((Yᘁ) ⊗ (Xᘁ)) (((Xᘁ)ᘁ) ⊗ ((Yᘁ)ᘁ)) =
      𝟙 (((Xᘁ)ᘁ ⊗ (Yᘁ)ᘁ) ⊗ (Yᘁ ⊗ Xᘁ)) ⊗≫ ((Xᘁ)ᘁ : C) ◁ (ε_ (Yᘁ) ((Yᘁ)ᘁ) ▷ (Xᘁ)) ⊗≫ ε_ (Xᘁ) ((Xᘁ)ᘁ) := rfl
  rw [hc, he]
  simp only [tensorHom_def, comp_whiskerRight]
  monoidal
  simp
  rw [whisker_exchange_assoc (p.iso X).hom (λ_ (Xᘁ)).hom]
  rw [whisker_exchange_assoc (p.iso X).hom (ε_ (Yᘁ) ((Yᘁ)ᘁ) ▷ (Xᘁ))]
  rw [whisker_exchange_assoc (p.iso X).hom ((p.iso Y).hom ▷ (Yᘁ) ▷ (Xᘁ))]
  rw [← associator_naturality_left_assoc (p.iso X).hom (Y ⊗ Yᘁ) (Xᘁ)]
  rw [← comp_whiskerRight_assoc, ← associator_naturality_left]

  rw [comp_whiskerRight, Category.assoc]

end PropertyF.Ground.Dimensions
