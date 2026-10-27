module
public import PropertyF.Ground.Dimensions.Trace

/-! Partial trace over the right tensor factor, constructed from duality. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.Calculus
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
  [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]

/-- Close the right tensor factor using evaluation, coevaluation, and the
pivotal isomorphism. -/
def rightPartialTrace (p : Dimensions.PivotalStructure (C := C)) (X Y : C) :
    End (X ⊗ Y) →ₗ[ℂ] End X where
  toFun f := End.of ((ρ_ X).inv ≫ (X ◁ η_ Y (Yᘁ)) ≫ (α_ X Y (Yᘁ)).inv ≫
    (f.asHom ▷ (Yᘁ)) ≫ (α_ X Y (Yᘁ)).hom ≫
    (X ◁ ((p.iso Y).hom ▷ (Yᘁ))) ≫
    (X ◁ ε_ (Yᘁ) ((Yᘁ)ᘁ)) ≫ (ρ_ X).hom)
  map_add' f g := by
    apply End.ext
    simp
  map_smul' z f := by
    apply End.ext
    simp

/-- Insert an endomorphism on the untraced tensor factor. -/
def insertRightIdentity (X Y : C) (a : End X) : End (X ⊗ Y) :=
  End.of (a.asHom ▷ Y)

/-- Partial trace commutes with postcomposition on the untraced factor. -/
theorem rightPartialTrace_left (p : Dimensions.PivotalStructure (C := C))
    (X Y : C) (a : End X) (f : End (X ⊗ Y)) :
    rightPartialTrace p X Y (insertRightIdentity X Y a * f) =
      a * rightPartialTrace p X Y f := by
  apply End.ext
  simp only [rightPartialTrace, insertRightIdentity, LinearMap.coe_mk, AddHom.coe_mk,
    End.mul_asHom, comp_whiskerRight, Category.assoc]
  rw [associator_naturality_left_assoc, ← whisker_exchange_assoc,
    ← whisker_exchange_assoc, rightUnitor_naturality]


/-- Partial trace commutes with precomposition on the untraced factor. -/
theorem rightPartialTrace_right (p : Dimensions.PivotalStructure (C := C))
    (X Y : C) (a : End X) (f : End (X ⊗ Y)) :
    rightPartialTrace p X Y (f * insertRightIdentity X Y a) =
      rightPartialTrace p X Y f * a := by
  apply End.ext
  simp only [rightPartialTrace, insertRightIdentity, LinearMap.coe_mk, AddHom.coe_mk,
    End.mul_asHom, comp_whiskerRight, Category.assoc]
  rw [← associator_inv_naturality_left_assoc, whisker_exchange_assoc,
    ← rightUnitor_inv_naturality_assoc]

/-- Tracing an identity strand gives the categorical dimension of the closed
factor, acting on the untraced object. -/
theorem rightPartialTrace_one (p : Dimensions.PivotalStructure (C := C))
    (X Y : C) : rightPartialTrace p X Y 1 =
      End.of ((ρ_ X).inv ≫ (X ◁ (p.rightTrace (𝟙 Y)).asHom) ≫ (ρ_ X).hom) := by
  apply End.ext
  simp only [rightPartialTrace, LinearMap.coe_mk, AddHom.coe_mk,
    End.one_asHom, id_whiskerRight, Category.comp_id, Iso.inv_hom_id_assoc,
    Dimensions.PivotalStructure.rightTrace, Category.id_comp,
    tensorHom_def, whiskerLeft_id, Category.comp_id]
  simp only [whiskerLeft_comp, Category.assoc]

/-- The partial trace of an inserted endomorphism is the dimension of the
closed factor times that endomorphism. -/
theorem rightPartialTrace_insert (p : Dimensions.PivotalStructure (C := C))
    (scalar : End (𝟙_ C) ≃ₐ[ℂ] ℂ) (X Y : C) (a : End X) :
    rightPartialTrace p X Y (insertRightIdentity X Y a) =
      (scalar (p.rightTrace (𝟙 Y))) • a := by
  have hscalar : p.rightTrace (𝟙 Y) = (scalar (p.rightTrace (𝟙 Y))) • (1 : End (𝟙_ C)) := by
    apply scalar.injective
    simp
  have hone : rightPartialTrace p X Y 1 = (scalar (p.rightTrace (𝟙 Y))) • (1 : End X) := by
    rw [rightPartialTrace_one, hscalar]
    apply End.ext
    simp
  have hins : insertRightIdentity X Y a = insertRightIdentity X Y a * 1 := by simp
  rw [hins, rightPartialTrace_left, hone]
  simp

end PropertyF.Ground.Calculus
