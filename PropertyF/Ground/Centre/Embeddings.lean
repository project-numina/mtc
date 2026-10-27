module
public import PropertyF.CenterBasics
public import Mathlib.CategoryTheory.Functor.FullyFaithful

/-! The two canonical embeddings of a braided category into its Drinfeld centre. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.Centre

universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]

/-- The negative embedding uses the inverse of the braiding in the opposite order. -/
def negative (C : Type u) [Category.{v} C] [MonoidalCategory C] [BraidedCategory C] :
    C ⥤ CategoryTheory.Center C :=
  @CategoryTheory.Center.ofBraided C _ _ (CategoryTheory.reverseBraiding C)

instance negativeMonoidal : (negative C).Monoidal := by
  unfold negative
  exact @CategoryTheory.Center.instMonoidalOfBraided C _ _ (CategoryTheory.reverseBraiding C)

instance positiveFaithful : (CategoryTheory.Center.ofBraided C).Faithful where
  map_injective := by
    intro X Y f g h
    exact congrArg CategoryTheory.Center.Hom.f h

instance positiveFull : (CategoryTheory.Center.ofBraided C).Full where
  map_surjective := by
    intro X Y f
    exact ⟨f.f, CategoryTheory.Center.ext _ _ rfl⟩

instance negativeFaithful : (negative C).Faithful where
  map_injective := by
    intro X Y f g h
    exact congrArg CategoryTheory.Center.Hom.f h

instance negativeFull : (negative C).Full where
  map_surjective := by
    intro X Y f
    exact ⟨f.f, CategoryTheory.Center.ext _ _ rfl⟩

/-- The two canonical images centralize one another in the actual centre. -/
theorem positive_negative_centralize (X Y : C) :
    (β_ ((CategoryTheory.Center.ofBraided C).obj X) ((negative C).obj Y)).hom ≫
      (β_ ((negative C).obj Y) ((CategoryTheory.Center.ofBraided C).obj X)).hom = 𝟙 _ := by
  apply CategoryTheory.Center.ext
  change (β_ X Y).hom ≫ (β_ X Y).inv = 𝟙 _
  exact Iso.hom_inv_id _

end PropertyF.Ground.Centre
