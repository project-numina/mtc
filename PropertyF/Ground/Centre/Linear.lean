module
public import PropertyF.Ground.Centre.Embeddings
public import Mathlib.CategoryTheory.Monoidal.Linear
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero
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

section Unit
variable [BraidedCategory C]
open CategoryTheory.Functor.Monoidal

/-- Every endomorphism of the tensor unit lifts canonically to the centre. -/
def liftUnitHom (f : 𝟙_ C ⟶ 𝟙_ C) :
    𝟙_ (CategoryTheory.Center C) ⟶ 𝟙_ (CategoryTheory.Center C) :=
  (εIso (CategoryTheory.Center.ofBraided C)).hom ≫
    (CategoryTheory.Center.ofBraided C).map f ≫
      (εIso (CategoryTheory.Center.ofBraided C)).inv

omit [Preadditive C] [MonoidalPreadditive C] in
@[simp] theorem liftUnitHom_f (f : 𝟙_ C ⟶ 𝟙_ C) : (liftUnitHom f).f = f := by
  simp only [liftUnitHom, CategoryTheory.Center.comp_f, εIso_hom, εIso_inv,
    CategoryTheory.Center.ofBraided_ε_f, CategoryTheory.Center.ofBraided_η_f,
    CategoryTheory.Center.ofBraided_map_f]
  change 𝟙 (𝟙_ C) ≫ f ≫ 𝟙 (𝟙_ C) = f
  simp

omit [Preadditive C] [MonoidalPreadditive C] in
/-- Forgetting the half-braiding bijects the endomorphisms of the tensor unit. -/
theorem forget_unit_hom_bijective :
    Function.Bijective (fun f : (𝟙_ (CategoryTheory.Center C) ⟶ 𝟙_ (CategoryTheory.Center C)) => f.f) := by
  constructor
  · intro f g h
    exact CategoryTheory.Center.ext f g h
  · intro f
    exact ⟨liftUnitHom f, liftUnitHom_f f⟩

/-- The bijection on unit endomorphisms is linear over the coefficient field. -/
def unitHomLinearEquiv (K : Type*) [Field K] [Linear K C] [MonoidalLinear K C] :
    (𝟙_ (CategoryTheory.Center C) ⟶ 𝟙_ (CategoryTheory.Center C)) ≃ₗ[K]
      (𝟙_ C ⟶ 𝟙_ C) :=
  LinearEquiv.ofBijective
    (show (𝟙_ (CategoryTheory.Center C) ⟶ 𝟙_ (CategoryTheory.Center C)) →ₗ[K]
      (𝟙_ C ⟶ 𝟙_ C) from (CategoryTheory.Center.forget C).mapLinearMap K)
    forget_unit_hom_bijective

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

/-! The zero object of the Drinfeld centre. -/
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
