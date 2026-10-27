module
public import PropertyF.Ground.Calculus.PartialTrace

/-! Partial traces between distinct objects for centre averaging. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.CentreInduction
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
  [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]

/-- Close a common right tensor factor in a morphism between possibly
different objects. -/
def partialTraceHom (p : Dimensions.PivotalStructure (C := C)) (X Y T : C) :
    (X ⊗ T ⟶ Y ⊗ T) →ₗ[ℂ] (X ⟶ Y) where
  toFun f := (ρ_ X).inv ≫ (X ◁ η_ T (Tᘁ)) ≫ (α_ X T (Tᘁ)).inv ≫
    (f ▷ Tᘁ) ≫ (α_ Y T (Tᘁ)).hom ≫
    (Y ◁ ((p.iso T).hom ▷ Tᘁ)) ≫
    (Y ◁ ε_ (Tᘁ) ((Tᘁ)ᘁ)) ≫ (ρ_ Y).hom
  map_add' f g := by simp
  map_smul' z f := by simp

/-- Closing a right identity strand scales a morphism by the pivotal
trace of the strand. -/
theorem partialTraceHom_whisker (p : Dimensions.PivotalStructure (C := C))
    (X Y T : C) (f : X ⟶ Y) :
    partialTraceHom p X Y T (f ▷ T) =
      f ≫ (ρ_ Y).inv ≫ (Y ◁ (p.rightTrace (𝟙 T)).asHom) ≫ (ρ_ Y).hom := by
  simp only [partialTraceHom, LinearMap.coe_mk, AddHom.coe_mk,
    Dimensions.PivotalStructure.rightTrace,
    Category.id_comp, tensorHom_def, whiskerLeft_id, Category.comp_id,
    whiskerLeft_comp, Category.assoc]
  rw [← associator_inv_naturality_left_assoc]
  simp only [Iso.inv_hom_id_assoc]
  rw [whisker_exchange_assoc, ← rightUnitor_inv_naturality_assoc]

end PropertyF.Ground.CentreInduction
