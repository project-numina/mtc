module
public import PropertyF.Ground.Dimensions.IteratedTrace
public import PropertyF.Ground.Dimensions.PivotalDual

/-! Left partial trace for the strand-deletion identity. -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.CentreCalculus
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
  [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]

/-- Close the first factor using the pivotal left dual. -/
def leftPartialTrace (p : Dimensions.PivotalStructure (C := C)) (X Y : C) :
    End (X ⊗ Y) →ₗ[ℂ] End Y where
  toFun f := End.of ((λ_ Y).inv ≫
    ((η_ (Xᘁ) ((Xᘁ)ᘁ) ≫ ((Xᘁ) ◁ (p.iso X).inv)) ▷ Y) ≫
    (α_ (Xᘁ) X Y).hom ≫ ((Xᘁ) ◁ f.asHom) ≫
    (α_ (Xᘁ) X Y).inv ≫ (ε_ X (Xᘁ) ▷ Y) ≫ (λ_ Y).hom)
  map_add' f g := by
    apply End.ext
    simp
  map_smul' z f := by
    apply End.ext
    simp

/-- Inserting a map on the untraced right factor. -/
def insertLeftIdentity (X Y : C) (a : End Y) : End (X ⊗ Y) :=
  End.of (X ◁ a.asHom)

/-- Left partial trace is a bimodule map over the untraced factor. -/
theorem leftPartialTrace_left (p : Dimensions.PivotalStructure (C := C))
    (X Y : C) (a : End Y) (f : End (X ⊗ Y)) :
    leftPartialTrace p X Y (insertLeftIdentity X Y a * f) =
      a * leftPartialTrace p X Y f := by
  apply End.ext
  simp only [leftPartialTrace, insertLeftIdentity, LinearMap.coe_mk, AddHom.coe_mk,
    End.mul_asHom, whiskerLeft_comp, Category.assoc]
  rw [associator_inv_naturality_right_assoc]
  rw [whisker_exchange_assoc, leftUnitor_naturality]

theorem leftPartialTrace_right (p : Dimensions.PivotalStructure (C := C))
    (X Y : C) (a : End Y) (f : End (X ⊗ Y)) :
    leftPartialTrace p X Y (f * insertLeftIdentity X Y a) =
      leftPartialTrace p X Y f * a := by
  apply End.ext
  simp only [leftPartialTrace, insertLeftIdentity, LinearMap.coe_mk, AddHom.coe_mk,
    End.mul_asHom, whiskerLeft_comp, Category.assoc]
  rw [← associator_naturality_right_assoc]
  rw [← whisker_exchange_assoc, ← leftUnitor_inv_naturality_assoc]

/-- Closing the first factor commutes with a spectator factor on the right. -/
theorem leftPartialTrace_whiskerRight (p : Dimensions.PivotalStructure (C := C))
    (X Y Z : C) (f : End (X ⊗ Y)) :
    leftPartialTrace p X (Y ⊗ Z) (End.of
      ((α_ X Y Z).inv ≫ (f.asHom ▷ Z) ≫ (α_ X Y Z).hom)) =
      End.of ((leftPartialTrace p X Y f).asHom ▷ Z) := by
  apply End.ext
  simp only [leftPartialTrace, LinearMap.coe_mk, AddHom.coe_mk,
    comp_whiskerRight, whiskerLeft_comp, Category.assoc]
  monoidal

end PropertyF.Ground.CentreCalculus
