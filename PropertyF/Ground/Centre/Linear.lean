module
public import Mathlib.CategoryTheory.Monoidal.Center
public import Mathlib.CategoryTheory.Monoidal.Linear
public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.Algebra.Module.Submodule.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-! Linear structure on the Drinfeld centre, obtained from its defining equations. -/

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

end PropertyF.Ground.Centre
