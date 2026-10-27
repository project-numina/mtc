module
public import PropertyF.Ground.Centre.Product
public import Mathlib.CategoryTheory.Monoidal.Rigid.Basic

/-! The canonical positive and negative images of a dual pair form a dual pair
in the actual centre. This does not establish rigidity for arbitrary centre objects. -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Functor.Monoidal
open CategoryTheory.Functor.LaxMonoidal CategoryTheory.Functor.OplaxMonoidal
namespace PropertyF.Ground.Centre
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]

/-- The positive embedding carries a dual pair to a dual pair in the centre. -/
@[instance_reducible] def positiveExactPairing (X Y : C) [ExactPairing X Y] :
    ExactPairing ((CategoryTheory.Center.ofBraided C).obj X)
      ((CategoryTheory.Center.ofBraided C).obj Y) where
  coevaluation' := ε (CategoryTheory.Center.ofBraided C) ≫
    (CategoryTheory.Center.ofBraided C).map (η_ X Y) ≫
      δ (CategoryTheory.Center.ofBraided C) X Y
  evaluation' := μ (CategoryTheory.Center.ofBraided C) Y X ≫
    (CategoryTheory.Center.ofBraided C).map (ε_ X Y) ≫ η (CategoryTheory.Center.ofBraided C)
  coevaluation_evaluation' := by
    apply CategoryTheory.Center.ext
    simp only [CategoryTheory.Center.comp_f, CategoryTheory.Center.ofBraided_ε_f,
      CategoryTheory.Center.ofBraided_δ_f, CategoryTheory.Center.ofBraided_μ_f,
      CategoryTheory.Center.ofBraided_η_f, CategoryTheory.Center.ofBraided_map_f,
      CategoryTheory.Center.whiskerLeft_f, CategoryTheory.Center.whiskerRight_f,
      CategoryTheory.Center.associator_inv_f, CategoryTheory.Center.rightUnitor_hom_f,
      CategoryTheory.Center.leftUnitor_inv_f, whiskerLeft_comp, comp_whiskerRight]
    change (Y ◁ 𝟙 (𝟙_ C) ≫ Y ◁ η_ X Y ≫ Y ◁ 𝟙 (X ⊗ Y)) ≫
      (α_ Y X Y).inv ≫ 𝟙 (Y ⊗ X) ▷ Y ≫ ε_ X Y ▷ Y ≫ 𝟙 (𝟙_ C) ▷ Y =
        (ρ_ Y).hom ≫ (λ_ Y).inv
    simpa only [whiskerLeft_id, id_whiskerRight, Category.id_comp, Category.comp_id] using
      ExactPairing.coevaluation_evaluation X Y
  evaluation_coevaluation' := by
    apply CategoryTheory.Center.ext
    simp only [CategoryTheory.Center.comp_f, CategoryTheory.Center.ofBraided_ε_f,
      CategoryTheory.Center.ofBraided_δ_f, CategoryTheory.Center.ofBraided_μ_f,
      CategoryTheory.Center.ofBraided_η_f, CategoryTheory.Center.ofBraided_map_f,
      CategoryTheory.Center.whiskerLeft_f, CategoryTheory.Center.whiskerRight_f,
      CategoryTheory.Center.associator_hom_f, CategoryTheory.Center.leftUnitor_hom_f,
      CategoryTheory.Center.rightUnitor_inv_f, whiskerLeft_comp, comp_whiskerRight]
    change (𝟙 (𝟙_ C) ▷ X ≫ η_ X Y ▷ X ≫ 𝟙 (X ⊗ Y) ▷ X) ≫
      (α_ X Y X).hom ≫ X ◁ 𝟙 (Y ⊗ X) ≫ X ◁ ε_ X Y ≫ X ◁ 𝟙 (𝟙_ C) =
        (λ_ X).hom ≫ (ρ_ X).inv
    simpa only [whiskerLeft_id, id_whiskerRight, Category.id_comp, Category.comp_id] using
      ExactPairing.evaluation_coevaluation X Y

/-- The negative embedding carries a dual pair to a dual pair in the centre. -/
@[instance_reducible] def negativeExactPairing (X Y : C) [ExactPairing X Y] :
    ExactPairing ((negative C).obj X) ((negative C).obj Y) := by
  letI := CategoryTheory.reverseBraiding C
  exact positiveExactPairing X Y

/-- The dual pair of a product image is another product image. This constructs
duals for those centre objects without assuming rigidity of the full centre. -/
@[instance_reducible] def productImageExactPairing (X Y X' Y' : C)
    [ExactPairing X X'] [ExactPairing Y Y'] :
    ExactPairing (productFunctor.obj (X, Y)) (productFunctor.obj (X', Y')) := by
  letI : ExactPairing ((CategoryTheory.Center.ofBraided C).obj X)
      ((CategoryTheory.Center.ofBraided C).obj X') := positiveExactPairing X X'
  letI : ExactPairing ((negative C).obj Y) ((negative C).obj Y') := negativeExactPairing Y Y'
  change ExactPairing (((CategoryTheory.Center.ofBraided C).obj X) ⊗ ((negative C).obj Y))
    (((CategoryTheory.Center.ofBraided C).obj X') ⊗ ((negative C).obj Y'))
  exact exactPairingCongrRight (β_ ((CategoryTheory.Center.ofBraided C).obj X')
    ((negative C).obj Y'))

end PropertyF.Ground.Centre
