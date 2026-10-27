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

omit [BraidedCategory C] in
/-- Centralization is invariant under isomorphism in its first argument. -/
theorem centralizes_of_iso_left {A B T : CategoryTheory.Center C} (i : A ≅ B)
    (h : Centralizes B T) : Centralizes A T := by
  unfold Centralizes at *
  apply (cancel_mono (i.hom ▷ T)).mp
  calc
    ((β_ A T).hom ≫ (β_ T A).hom) ≫ (i.hom ▷ T) =
        (i.hom ▷ T) ≫ ((β_ B T).hom ≫ (β_ T B).hom) := by
      simp only [Category.assoc, BraidedCategory.braiding_naturality_left_assoc]
      rw [← BraidedCategory.braiding_naturality_right T i.hom]
    _ = 𝟙 _ ≫ (i.hom ▷ T) := by rw [h]; simp

omit [BraidedCategory C] in
/-- Centralization is symmetric. -/
theorem centralizes_symm {A B : CategoryTheory.Center C} (h : Centralizes A B) :
    Centralizes B A := by
  unfold Centralizes at *
  apply (cancel_epi (β_ A B).hom).mp
  simp only [← Category.assoc, h, Category.id_comp, Category.comp_id]

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

/-- The categorical centralizer of the positive image is exactly the
essential image of the negative embedding. -/
theorem centralizes_positive_iff_negative_essential_image (Y : CategoryTheory.Center C) :
    (∀ X : C, Centralizes Y ((CategoryTheory.Center.ofBraided C).obj X)) ↔
      ∃ X : C, Nonempty (Y ≅ (negative C).obj X) := by
  constructor
  · intro h
    exact ⟨Y.1, ⟨negativeIsoOfCentralizesPositive Y h⟩⟩
  · rintro ⟨X, ⟨i⟩⟩ Z
    apply centralizes_of_iso_left i
    exact centralizes_symm (positive_negative_centralize Z X)

/-- The categorical centralizer of the negative image is the essential image
of the positive embedding. -/
theorem centralizes_negative_iff_positive_essential_image (Y : CategoryTheory.Center C) :
    (∀ X : C, Centralizes Y ((negative C).obj X)) ↔
      ∃ X : C, Nonempty (Y ≅ (CategoryTheory.Center.ofBraided C).obj X) := by
  constructor
  · intro h
    exact ⟨Y.1, ⟨positiveIsoOfCentralizesNegative Y h⟩⟩
  · rintro ⟨X, ⟨i⟩⟩ Z
    apply centralizes_of_iso_left i
    exact positive_negative_centralize X Z

/-- The positive embedding detects transparency in the original category. -/
theorem transparent_iff_positive_centralizes_positive (X : C) :
    Transparent X ↔ ∀ Y : C, Centralizes ((CategoryTheory.Center.ofBraided C).obj X)
      ((CategoryTheory.Center.ofBraided C).obj Y) := by
  constructor
  · intro h Y
    apply CategoryTheory.Center.ext
    exact h Y
  · intro h Y
    exact congrArg CategoryTheory.Center.Hom.f (h Y)

/-- The intersection of the two essential images consists exactly of the
positive images of transparent objects. -/
theorem transparent_iff_positive_in_negative_image (X : C) :
    Transparent X ↔ ∃ Y : C,
      Nonempty ((CategoryTheory.Center.ofBraided C).obj X ≅ (negative C).obj Y) := by
  rw [← centralizes_positive_iff_negative_essential_image,
    ← transparent_iff_positive_centralizes_positive]

end PropertyF.Ground.Centre
