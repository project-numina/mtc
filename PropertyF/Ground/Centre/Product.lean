module
public import PropertyF.Ground.Centre.Embeddings

/-! The underlying bifunctor of the canonical centre product construction.
The source here is the ordinary product category, not the Deligne tensor product;
its monoidal structure is inherited from the two embeddings and the centre tensor functor. No Deligne-product dominance is asserted. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Functor.Monoidal
namespace PropertyF.Ground.Centre
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]

/-- Componentwise braiding, with the second component reversed. -/
@[instance_reducible]
def mixedBraiding : BraidedCategory (C × C) where
  braiding X Y := (β_ X.1 Y.1).prod (β_ Y.2 X.2).symm
  braiding_naturality_right := by
    intro X Y Z f
    ext <;> simp
  braiding_naturality_left := by
    intro X Y f Z
    ext <;> simp
  hexagon_forward := by
    intro X Y Z
    ext <;> simp
  hexagon_reverse := by
    intro X Y Z
    ext <;> simp

/-- The objectwise product of the two centre embeddings. -/
def productFunctor : (C × C) ⥤ CategoryTheory.Center C :=
  ((CategoryTheory.Center.ofBraided C).prod (negative C)) ⋙ tensor (CategoryTheory.Center C)

instance productMonoidal : (productFunctor (C := C)).Monoidal := by
  unfold productFunctor
  infer_instance

/-- The product functor contains every object of the positive image. -/
def positiveProductIso (X : C) : productFunctor.obj (X, 𝟙_ C) ≅
    (CategoryTheory.Center.ofBraided C).obj X :=
  whiskerLeftIso ((CategoryTheory.Center.ofBraided C).obj X) (εIso (negative C)).symm ≪≫
    ρ_ ((CategoryTheory.Center.ofBraided C).obj X)

/-- The product functor contains every object of the negative image. -/
def negativeProductIso (X : C) : productFunctor.obj (𝟙_ C, X) ≅ (negative C).obj X :=
  whiskerRightIso (εIso (CategoryTheory.Center.ofBraided C)).symm ((negative C).obj X) ≪≫
    λ_ ((negative C).obj X)

end PropertyF.Ground.Centre
