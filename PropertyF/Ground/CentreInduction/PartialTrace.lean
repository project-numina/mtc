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


end PropertyF.Ground.CentreInduction

namespace PropertyF.Ground.CentreInduction
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
  [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]

/-- Partial trace commutes with precomposition on the surviving factor. -/
theorem partialTraceHom_precompose (p : Dimensions.PivotalStructure (C := C))
    {W X Y : C} (T : C) (f : W ⟶ X) (g : X ⊗ T ⟶ Y ⊗ T) :
    partialTraceHom p W Y T ((f ▷ T) ≫ g) = f ≫ partialTraceHom p X Y T g := by
  simp only [partialTraceHom, LinearMap.coe_mk, AddHom.coe_mk, comp_whiskerRight,
    Category.assoc]
  rw [← associator_inv_naturality_left_assoc, whisker_exchange_assoc,
    ← rightUnitor_inv_naturality_assoc]

/-- Partial trace commutes with postcomposition on the surviving factor. -/
theorem partialTraceHom_postcompose (p : Dimensions.PivotalStructure (C := C))
    {X Y Z : C} (T : C) (g : X ⊗ T ⟶ Y ⊗ T) (f : Y ⟶ Z) :
    partialTraceHom p X Z T (g ≫ (f ▷ T)) = partialTraceHom p X Y T g ≫ f := by
  simp only [partialTraceHom, LinearMap.coe_mk, AddHom.coe_mk, comp_whiskerRight,
    Category.assoc]
  rw [associator_naturality_left_assoc, ← whisker_exchange_assoc,
    ← whisker_exchange_assoc, rightUnitor_naturality]

end PropertyF.Ground.CentreInduction
