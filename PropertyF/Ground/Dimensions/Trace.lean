module
public import PropertyF.Ground.Dimensions.Pivotal
public import Mathlib.CategoryTheory.Monoidal.Linear

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.Dimensions.PivotalStructure

universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
  [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  (p : PivotalStructure (C := C)) {X : C}

omit [Linear ℂ C] [MonoidalLinear ℂ C] in
/-- The right trace is linear in its endomorphism argument. -/
theorem rightTrace_add (f g : X ⟶ X) : p.rightTrace (f + g) = p.rightTrace f + p.rightTrace g := by
  apply End.homEquiv.injective
  simp [rightTrace, tensorHom_def]

theorem rightTrace_smul (c : ℂ) (f : X ⟶ X) : p.rightTrace (c • f) = c • p.rightTrace f := by
  apply End.homEquiv.injective
  simp [rightTrace, tensorHom_def]

omit [Linear ℂ C] [MonoidalLinear ℂ C] in
/-- The left trace is linear in its endomorphism argument. -/
theorem leftTrace_add (f g : X ⟶ X) : p.leftTrace (f + g) = p.leftTrace f + p.leftTrace g := by
  apply End.homEquiv.injective
  simp [leftTrace, tensorHom_def]

theorem leftTrace_smul (c : ℂ) (f : X ⟶ X) : p.leftTrace (c • f) = c • p.leftTrace f := by
  apply End.homEquiv.injective
  simp [leftTrace, tensorHom_def]

end PropertyF.Ground.Dimensions.PivotalStructure

namespace PropertyF.Ground.Dimensions.PivotalStructure
open CategoryTheory CategoryTheory.MonoidalCategory
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]

/-- The right pivotal trace is cyclic. -/
theorem rightTrace_cyclic (p : PivotalStructure (C := C)) {X Y : C}
    (f : X ⟶ Y) (g : Y ⟶ X) : p.rightTrace (f ≫ g) = p.rightTrace (g ≫ f) := by
  apply End.homEquiv.injective
  change η_ X (Xᘁ) ≫ (((f ≫ g) ≫ (p.iso X).hom) ⊗ₘ 𝟙 (Xᘁ)) ≫ ε_ (Xᘁ) ((Xᘁ)ᘁ) =
    η_ Y (Yᘁ) ≫ (((g ≫ f) ≫ (p.iso Y).hom) ⊗ₘ 𝟙 (Yᘁ)) ≫ ε_ (Yᘁ) ((Yᘁ)ᘁ)
  simp only [Category.assoc]
  calc
    _ = η_ X (Xᘁ) ≫ f ▷ (Xᘁ) ≫ g ▷ (Xᘁ) ≫ (p.iso X).hom ▷ (Xᘁ) ≫ ε_ (Xᘁ) ((Xᘁ)ᘁ) := by simp [tensorHom_def, comp_whiskerRight]
    _ = η_ Y (Yᘁ) ≫ Y ◁ fᘁ ≫ g ▷ (Xᘁ) ≫ (p.iso X).hom ▷ (Xᘁ) ≫ ε_ (Xᘁ) ((Xᘁ)ᘁ) := by rw [coevaluation_comp_rightAdjointMate_assoc]
    _ = η_ Y (Yᘁ) ≫ g ▷ (Yᘁ) ≫ X ◁ fᘁ ≫ (p.iso X).hom ▷ (Xᘁ) ≫ ε_ (Xᘁ) ((Xᘁ)ᘁ) := by rw [whisker_exchange_assoc g (fᘁ)]
    _ = η_ Y (Yᘁ) ≫ g ▷ (Yᘁ) ≫ (p.iso X).hom ▷ (Yᘁ) ≫ ((Xᘁ)ᘁ) ◁ fᘁ ≫ ε_ (Xᘁ) ((Xᘁ)ᘁ) := by rw [whisker_exchange_assoc (p.iso X).hom (fᘁ)]
    _ = η_ Y (Yᘁ) ≫ g ▷ (Yᘁ) ≫ (p.iso X).hom ▷ (Yᘁ) ≫ (fᘁ)ᘁ ▷ (Yᘁ) ≫ ε_ (Yᘁ) ((Yᘁ)ᘁ) := by rw [← rightAdjointMate_comp_evaluation]
    _ = η_ Y (Yᘁ) ≫ ((g ≫ f ≫ (p.iso Y).hom) ⊗ₘ 𝟙 (Yᘁ)) ≫ ε_ (Yᘁ) ((Yᘁ)ᘁ) := by
      simp only [tensorHom_def, whiskerLeft_id, Category.comp_id, p.naturality f,
        comp_whiskerRight, Category.assoc]

/-- In a spherical category the left pivotal trace is cyclic as well. -/
theorem leftTrace_cyclic_of_spherical (p : PivotalStructure (C := C)) (hp : p.IsSpherical)
    {X Y : C} (f : X ⟶ Y) (g : Y ⟶ X) : p.leftTrace (f ≫ g) = p.leftTrace (g ≫ f) := by
  rw [hp X (f ≫ g), hp Y (g ≫ f)]
  exact p.rightTrace_cyclic f g

/-- Pivotal dimensions are invariant under object isomorphism. -/
theorem rightTrace_id_iso (p : PivotalStructure (C := C)) {X Y : C} (e : X ≅ Y) :
    p.rightTrace (𝟙 X) = p.rightTrace (𝟙 Y) := by
  simpa using p.rightTrace_cyclic e.hom e.inv

end PropertyF.Ground.Dimensions.PivotalStructure

namespace PropertyF.Ground.Dimensions
open CategoryTheory CategoryTheory.MonoidalCategory
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RigidCategory C]

/-- The left quantum trace of an isomorphism is the right quantum trace of the
corresponding inverse dual isomorphism. -/
theorem leftQuantumTrace_eq_rightDual {X : C} (j : X ≅ (Xᘁ)ᘁ) :
    leftQuantumTrace j = rightQuantumTrace (rightDualIsoMap j).symm := by
  apply End.homEquiv.injective
  change η_ (Xᘁ) ((Xᘁ)ᘁ) ≫ (𝟙 (Xᘁ) ⊗ₘ j.inv) ≫ ε_ X (Xᘁ) =
    η_ (Xᘁ) ((Xᘁ)ᘁ) ≫ ((j.invᘁ) ⊗ₘ 𝟙 ((Xᘁ)ᘁ)) ≫ ε_ ((Xᘁ)ᘁ) (((Xᘁ)ᘁ)ᘁ)
  simp only [tensorHom_def, id_whiskerRight, whiskerLeft_id, Category.id_comp, Category.comp_id]
  rw [rightAdjointMate_comp_evaluation]

end PropertyF.Ground.Dimensions
