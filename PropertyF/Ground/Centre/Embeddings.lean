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

instance positiveBraided : (CategoryTheory.Center.ofBraided C).Braided where
  braided X Y := by
    apply CategoryTheory.Center.ext
    change (𝟙 _ ≫ (β_ X Y).hom) = (β_ X Y).hom ≫ 𝟙 _
    simp

/-- The negative embedding preserves the reversed braiding. -/
@[instance_reducible]
def negativeBraided : @Functor.Braided C _ _ (CategoryTheory.reverseBraiding C)
    (CategoryTheory.Center C) _ _ _ (negative C) :=
  @positiveBraided C _ _ (CategoryTheory.reverseBraiding C)

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

/-- Two centre objects centralize when their double braiding is the identity. -/
def Centralizes (A B : CategoryTheory.Center C) : Prop :=
  (β_ A B).hom ≫ (β_ B A).hom = 𝟙 _

/-- The paper's half-braiding test is exactly centralization of the positive image. -/
theorem centralizes_positive_image_iff (Y : CategoryTheory.Center C) :
    (∀ X : C, Centralizes Y ((CategoryTheory.Center.ofBraided C).obj X)) ↔
      CentralizesPositive Y := by
  constructor
  · intro h X
    exact congrArg CategoryTheory.Center.Hom.f (h X)
  · intro h X
    apply CategoryTheory.Center.ext
    exact h X

/-- The corresponding test for the negative image. -/
theorem centralizes_negative_image_iff (Y : CategoryTheory.Center C) :
    (∀ X : C, Centralizes Y ((negative C).obj X)) ↔ CentralizesNegative Y := by
  constructor
  · intro h X
    exact congrArg CategoryTheory.Center.Hom.f (h X)
  · intro h X
    apply CategoryTheory.Center.ext
    exact h X

/-- An object centralizing the positive image is canonically isomorphic to an
object in the negative image, with the identity underlying morphism. -/
def negativeIsoOfCentralizesPositive (Y : CategoryTheory.Center C)
    (h : ∀ X : C, Centralizes Y ((CategoryTheory.Center.ofBraided C).obj X)) :
    Y ≅ (negative C).obj Y.1 := by
  have hβ := (centralizesPositive_iff Y).mp ((centralizes_positive_image_iff Y).mp h)
  let f : Y ⟶ (negative C).obj Y.1 :=
    ⟨𝟙 _, fun X => by
      change (𝟙 Y.1 ▷ X) ≫ (β_ X Y.1).inv = (Y.2.β X).hom ≫ (X ◁ 𝟙 Y.1)
      simpa only [id_whiskerRight, whiskerLeft_id, Category.id_comp, Category.comp_id, Iso.symm_hom] using
        (congrArg Iso.hom (hβ X)).symm⟩
  letI : IsIso f.f := inferInstanceAs (IsIso (𝟙 Y.1))
  exact CategoryTheory.Center.isoMk f

/-- An object centralizing the negative image belongs to the positive image. -/
def positiveIsoOfCentralizesNegative (Y : CategoryTheory.Center C)
    (h : ∀ X : C, Centralizes Y ((negative C).obj X)) :
    Y ≅ (CategoryTheory.Center.ofBraided C).obj Y.1 := by
  have hβ := (centralizesNegative_iff Y).mp ((centralizes_negative_image_iff Y).mp h)
  let f : Y ⟶ (CategoryTheory.Center.ofBraided C).obj Y.1 :=
    ⟨𝟙 _, fun X => by
      change (𝟙 Y.1 ▷ X) ≫ (β_ Y.1 X).hom = (Y.2.β X).hom ≫ (X ◁ 𝟙 Y.1)
      simpa only [id_whiskerRight, whiskerLeft_id, Category.id_comp, Category.comp_id, Iso.symm_hom] using
        (congrArg Iso.hom (hβ X)).symm⟩
  letI : IsIso f.f := inferInstanceAs (IsIso (𝟙 Y.1))
  exact CategoryTheory.Center.isoMk f

end PropertyF.Ground.Centre
