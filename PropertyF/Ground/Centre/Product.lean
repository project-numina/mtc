module
public import PropertyF.Ground.Centre.Basic

/-! The underlying bifunctor of the canonical centre product construction.
The source here is the ordinary product category, not the Deligne tensor product;
its braided monoidal structure follows from the centrality of the two images. No Deligne-product dominance is asserted. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Functor.Monoidal
open CategoryTheory.BraidedCategory
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

/-- Interchange of two tensor pairs respects braiding when both cross pairs centralize. -/
theorem tensor_interchange_braiding {D : Type*} [Category* D] [MonoidalCategory D]
    [BraidedCategory D] (A B C E : D)
    (h : (β_ C B).hom = (β_ B C).inv)
    (h' : (β_ A E).hom = (β_ E A).inv) :
    tensorμ A C B E ≫ ((β_ A B).hom ⊗ₘ (β_ C E).hom) =
      (β_ (A ⊗ C) (B ⊗ E)).hom ≫ tensorμ B E A C := by
  simp [tensorμ, h, h', tensorHom_def]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The ordinary product functor preserves the mixed braiding. -/
@[instance_reducible]
def productBraided : @Functor.Braided (C × C) _ _ (mixedBraiding (C := C))
    (CategoryTheory.Center C) _ _ _ productFunctor := by
  letI : BraidedCategory (C × C) := mixedBraiding
  refine { braided := ?_ }
  intro X Y
  let A := (CategoryTheory.Center.ofBraided C).obj X.1
  let B := (CategoryTheory.Center.ofBraided C).obj Y.1
  let D := (negative C).obj X.2
  let E := (negative C).obj Y.2
  have hDB : (β_ D B).hom = (β_ B D).inv := by
    apply (cancel_mono (β_ B D).hom).mp
    simpa [Centralizes, B, D] using centralizes_symm (positive_negative_centralize Y.1 X.2)
  have hAE : (β_ A E).hom = (β_ E A).inv := by
    apply (cancel_mono (β_ E A).hom).mp
    simpa [A, E] using positive_negative_centralize X.1 Y.2
  have h := tensor_interchange_braiding A B D E hDB hAE
  apply CategoryTheory.Center.ext
  have h' := congrArg CategoryTheory.Center.Hom.f h
  have hμ (x y : C) : (Functor.LaxMonoidal.μ (negative C) x y).f = 𝟙 _ := rfl
  have hβ₁ : (β_ X Y).hom.1 = (β_ X.1 Y.1).hom := rfl
  have hβ₂ : (β_ X Y).hom.2 = (β_ Y.2 X.2).inv := rfl
  have hp : (β_ A B).hom.f = (β_ X.1 Y.1).hom := rfl
  have hn : (β_ D E).hom.f = (β_ Y.2 X.2).inv := rfl
  have hm {x y : C} (f : x ⟶ y) : ((negative C).map f).f = f := rfl
  have ho (x : C) : ((CategoryTheory.Center.ofBraided C).obj x).1 = x := rfl
  have ho' (x : C) : ((negative C).obj x).1 = x := rfl
  simpa [A, B, D, E, productFunctor, hμ, hβ₁, hβ₂, hp, hn, hm, ho, ho'] using h'


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
