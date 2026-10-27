module
public import PropertyF.CenterBasics
public import Mathlib.CategoryTheory.Functor.FullyFaithful
public import Mathlib.CategoryTheory.Monoidal.Linear
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero
public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.Algebra.Module.Submodule.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
# Basic structure of the Drinfeld centre

The positive and negative embeddings of a braided category into its centre
centralize each other. For an additive monoidal category, centre morphisms
inherit additive and linear structures, and the zero object lifts to the centre.

## Main definitions and results

* `negative` is the embedding induced by the reversed braiding.
* `Centralizes` and its image characterizations describe the two embeddings.
* `centerZero` and the centre instances lift additive and linear structure.
-/



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

end PropertyF.Ground.Centre



@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.Centre
universe v u
variable {C : Type u} [Category.{v} C] [Preadditive C] [MonoidalCategory C]
  [MonoidalPreadditive C]

/-- Centre morphisms form an additive subgroup of the underlying Hom group. -/
def homSubgroup (X Y : CategoryTheory.Center C) : AddSubgroup (X.1 ⟶ Y.1) where
  carrier := {f | ∀ U, (f ▷ U) ≫ (Y.2.β U).hom = (X.2.β U).hom ≫ (U ◁ f)}
  zero_mem' := by simp
  add_mem' := by
    intro f g hf hg U
    simp only [MonoidalPreadditive.add_whiskerRight, Preadditive.add_comp,
      MonoidalPreadditive.whiskerLeft_add, Preadditive.comp_add, hf U, hg U]
  neg_mem' := by
    intro f hf U
    change (tensorRight U).map (-f) ≫ (Y.2.β U).hom =
      (X.2.β U).hom ≫ (tensorLeft U).map (-f)
    rw [Functor.map_neg, Functor.map_neg, Preadditive.neg_comp, Preadditive.comp_neg]
    exact congrArg Neg.neg (hf U)

/-- A centre morphism is its underlying map satisfying the intertwining equations. -/
def homEquivSubgroup (X Y : CategoryTheory.Center C) :
    (X ⟶ Y) ≃ homSubgroup X Y where
  toFun f := ⟨f.f, f.comm⟩
  invFun f := ⟨f.1, f.2⟩
  left_inv f := by cases f; rfl
  right_inv f := by cases f; rfl

instance centerPreadditive : Preadditive (CategoryTheory.Center C) where
  homGroup X Y := (homEquivSubgroup X Y).addCommGroup
  add_comp X Y Z f g h := by
    apply CategoryTheory.Center.ext
    exact Preadditive.add_comp _ _ _ _ _ _
  comp_add X Y Z f g h := by
    apply CategoryTheory.Center.ext
    exact Preadditive.comp_add _ _ _ _ _ _

instance centerForgetFaithful : (CategoryTheory.Center.forget C).Faithful where
  map_injective := by
    intro X Y f g h
    exact CategoryTheory.Center.ext _ _ h

instance centerForgetAdditive : (CategoryTheory.Center.forget C).Additive where
  map_add := by intros; rfl

instance centerMonoidalPreadditive : MonoidalPreadditive (CategoryTheory.Center C) :=
  monoidalPreadditive_of_faithful (CategoryTheory.Center.forget C)

section Linear
variable (R : Type*) [Ring R] [Linear R C] [MonoidalLinear R C]

/-- Intertwining maps form a submodule when the tensor product is linear. -/
def homSubmodule (X Y : CategoryTheory.Center C) : Submodule R (X.1 ⟶ Y.1) where
  carrier := homSubgroup X Y
  zero_mem' := (homSubgroup X Y).zero_mem
  add_mem' := (homSubgroup X Y).add_mem
  smul_mem' := by
    intro r f hf
    change ∀ U, ((r • f) ▷ U) ≫ (Y.2.β U).hom = (X.2.β U).hom ≫ (U ◁ (r • f))
    intro U
    simp only [MonoidalLinear.smul_whiskerRight, Linear.smul_comp,
      MonoidalLinear.whiskerLeft_smul, Linear.comp_smul, hf U]

/-- The centre Hom group and the submodule of intertwiners are additively equivalent. -/
def homAddEquivSubmodule (X Y : CategoryTheory.Center C) :
    (X ⟶ Y) ≃+ homSubmodule R X Y where
  toFun f := ⟨f.f, f.comm⟩
  invFun f := ⟨f.1, f.2⟩
  left_inv f := by cases f; rfl
  right_inv f := by cases f; rfl
  map_add' _ _ := rfl

instance centerLinear : Linear R (CategoryTheory.Center C) where
  homModule X Y := (homAddEquivSubmodule R X Y).module R
  smul_comp X Y Z r f g := by
    apply CategoryTheory.Center.ext
    exact Linear.smul_comp _ _ _ _ _ _
  comp_smul X Y Z f r g := by
    apply CategoryTheory.Center.ext
    exact Linear.comp_smul _ _ _ _ _ _

instance centerForgetLinear : (CategoryTheory.Center.forget C).Linear R where
  map_smul := by intros; rfl

instance centerMonoidalLinear : MonoidalLinear R (CategoryTheory.Center C) :=
  MonoidalLinear.ofFaithful R (CategoryTheory.Center.forget C)

end Linear

/-- A finite-dimensional underlying Hom space gives a finite-dimensional
centre Hom space, since the forgetful map is injective and linear. -/
theorem finiteDimensional_hom (K : Type*) [Field K] [Linear K C] [MonoidalLinear K C]
    (X Y : CategoryTheory.Center C) [FiniteDimensional K (X.1 ⟶ Y.1)] :
    FiniteDimensional K (X ⟶ Y) :=
  FiniteDimensional.of_injective
    (show (X ⟶ Y) →ₗ[K] (X.1 ⟶ Y.1) from
      (CategoryTheory.Center.forget C).mapLinearMap K)
    (Functor.map_injective (CategoryTheory.Center.forget C))

section Unit
variable [BraidedCategory C]
open CategoryTheory.Functor.Monoidal

instance positiveLinear (K : Type*) [Field K] [Linear K C] [MonoidalLinear K C] :
    (CategoryTheory.Center.ofBraided C).Linear K where
  map_smul := by
    intros
    apply CategoryTheory.Center.ext
    rfl

instance negativeLinear (K : Type*) [Field K] [Linear K C] [MonoidalLinear K C] :
    (negative C).Linear K where
  map_smul := by
    intros
    apply CategoryTheory.Center.ext
    rfl

end Unit
end PropertyF.Ground.Centre


@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open scoped ZeroObject
namespace PropertyF.Ground.Centre
universe v u
variable {C : Type u} [Category.{v} C] [Preadditive C] [MonoidalCategory C]
  [MonoidalPreadditive C] [HasZeroObject C]

/-- Tensoring a zero object on the right remains a zero object. -/
theorem zeroTensorRight (U : C) : IsZero ((0 : C) ⊗ U) :=
  (tensorRight U).map_isZero (isZero_zero C)

/-- Tensoring a zero object on the left remains a zero object. -/
theorem zeroTensorLeft (U : C) : IsZero (U ⊗ (0 : C)) :=
  (tensorLeft U).map_isZero (isZero_zero C)

/-- The unique half-braiding on the zero object. -/
def centerZero : CategoryTheory.Center C :=
  ⟨0, { β := fun U => (zeroTensorRight U).iso (zeroTensorLeft U)
        monoidal := fun U U' => (zeroTensorRight (U ⊗ U')).eq_of_src _ _
        naturality := fun {U _U'} _f => (zeroTensorRight U).eq_of_src _ _ }⟩

omit [HasZeroObject C] in
/-- The forgetful functor detects zero objects. -/
theorem isZero_of_forget (Z : CategoryTheory.Center C) (h : IsZero Z.1) : IsZero Z := by
  apply (IsZero.iff_id_eq_zero _).mpr
  apply CategoryTheory.Center.ext
  exact h.eq_of_src _ _

/-- The constructed centre object over zero is a zero object. -/
theorem centerZero_isZero : IsZero (centerZero (C := C)) :=
  isZero_of_forget _ (isZero_zero C)

instance centerHasZeroObject : HasZeroObject (CategoryTheory.Center C) :=
  centerZero_isZero.hasZeroObject

end PropertyF.Ground.Centre
