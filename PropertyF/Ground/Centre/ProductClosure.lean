module
public import PropertyF.Ground.Centre.ProductImages
public import PropertyF.Ground.Centre.Abelian

/-! Closure properties of retracts of the canonical product functor's images. -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
namespace PropertyF.Ground.Centre
universe v u
variable {C : Type u} [Category.{v} C] [Preadditive C] [MonoidalCategory C]
  [MonoidalPreadditive C] [HasBinaryBiproducts C] [BraidedCategory C]

/-- Objects isomorphic to retracts of canonical product images. -/
def ProductRetract (Z : CategoryTheory.Center C) : Prop :=
  ∃ X Y : C, Nonempty (Retract Z (productFunctor.obj (X,Y)))

omit [Preadditive C] [MonoidalPreadditive C] [HasBinaryBiproducts C] in
/-- The class is closed under retracts. -/
theorem productRetract_of_retract {Z W : CategoryTheory.Center C}
    (r : Retract Z W) (h : ProductRetract W) : ProductRetract Z :=
  match h with
  | ⟨X, Y, ⟨s⟩⟩ => ⟨X, Y, ⟨r.trans s⟩⟩

omit [Preadditive C] [MonoidalPreadditive C] [HasBinaryBiproducts C] in
/-- Every positive canonical image is a product retract. -/
theorem positive_productRetract (X : C) : ProductRetract ((CategoryTheory.Center.ofBraided C).obj X) :=
  ⟨X, 𝟙_ C, ⟨Retract.ofIso (positiveProductIso X).symm⟩⟩

omit [Preadditive C] [MonoidalPreadditive C] [HasBinaryBiproducts C] in
/-- Every negative canonical image is a product retract. -/
theorem negative_productRetract (X : C) : ProductRetract ((negative C).obj X) :=
  ⟨𝟙_ C, X, ⟨Retract.ofIso (negativeProductIso X).symm⟩⟩

omit [Preadditive C] [MonoidalPreadditive C] [HasBinaryBiproducts C] in
/-- The tensor unit of the centre is a product retract. -/
theorem unit_productRetract : ProductRetract (𝟙_ (CategoryTheory.Center C)) :=
  ⟨𝟙_ C, 𝟙_ C, ⟨Retract.ofIso (CategoryTheory.Functor.Monoidal.εIso productFunctor)⟩⟩

omit [Preadditive C] [MonoidalPreadditive C] [HasBinaryBiproducts C] in
/-- Tensor products preserve retracts in the centre. -/
def tensorRetract {A B A' B' : CategoryTheory.Center C}
    (r : Retract A A') (s : Retract B B') : Retract (A ⊗ B) (A' ⊗ B') where
  i := r.i ⊗ₘ s.i
  r := r.r ⊗ₘ s.r
  retract := by simp [tensorHom_comp_tensorHom]

omit [Preadditive C] [MonoidalPreadditive C] [HasBinaryBiproducts C] in
/-- The class is closed under tensor products, using the product functor's tensorator. -/
theorem productRetract_tensor {Z W : CategoryTheory.Center C}
    (hZ : ProductRetract Z) (hW : ProductRetract W) : ProductRetract (Z ⊗ W) :=
  match hZ, hW with
  | ⟨X, Y, ⟨r⟩⟩, ⟨X', Y', ⟨s⟩⟩ =>
    ⟨X ⊗ X', Y ⊗ Y', ⟨(tensorRetract r s).trans
      (Retract.ofIso (CategoryTheory.Functor.Monoidal.μIso productFunctor (X,Y) (X',Y')))⟩⟩

omit [Preadditive C] [MonoidalPreadditive C] [HasBinaryBiproducts C] in
/-- Property F holds on every product retract when the base category has property F. -/
theorem productRetract_propertyF {Z : CategoryTheory.Center C}
    (hZ : ProductRetract Z) (hC : HasPropertyF C) : ObjectPropertyF Z :=
  match hZ with
  | ⟨X, Y, ⟨r⟩⟩ => productFunctor_retract_objectPropertyF X Y Z r (hC X) (hC Y)

end PropertyF.Ground.Centre

/-! Finite sums of retracts of product images. -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
namespace PropertyF.Ground.Centre
universe v u
variable {C : Type u} [Category.{v} C] [Preadditive C] [MonoidalCategory C]
  [MonoidalPreadditive C] [HasBinaryBiproducts C] [HasZeroObject C]
  [HasFiniteBiproducts C] [BraidedCategory C]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- A finite direct sum of product images retracts from a single product image. -/
def productFunctorFiniteSumRetract {J : Type} [Fintype J] (X Y : J → C) :
    Retract (⨁ fun j => productFunctor.obj (X j, Y j))
      (productFunctor.obj (⨁ X, ⨁ Y)) where
  i := biproduct.desc fun j => productFunctor.map (biproduct.ι X j, biproduct.ι Y j)
  r := biproduct.lift fun j => productFunctor.map (biproduct.π X j, biproduct.π Y j)
  retract := by
    apply biproduct.hom_ext'
    intro j
    apply biproduct.hom_ext
    intro k
    simp only [Category.assoc, biproduct.ι_desc_assoc, biproduct.lift_π,
      Category.id_comp]
    apply CategoryTheory.Center.ext
    by_cases h : j = k
    · subst k
      simp [productFunctor, negative, tensorHom_comp_tensorHom]
    · simp [productFunctor, negative, tensorHom_comp_tensorHom, biproduct.ι_π_ne _ h]
      rfl

/-- A finite direct sum of product retracts is a product retract. -/
theorem productRetract_finiteBiproduct {J : Type} [Fintype J]
    (Z : J → CategoryTheory.Center C) (h : ∀ j, ProductRetract (Z j)) :
    ProductRetract (⨁ Z) := by
  classical
  choose X Y hxy using h
  let r : ∀ j, Retract (Z j) (productFunctor.obj (X j, Y j)) := fun j => (hxy j).some
  let rr : Retract (⨁ Z) (⨁ fun j => productFunctor.obj (X j, Y j)) :=
    { i := biproduct.map fun j => (r j).i
      r := biproduct.map fun j => (r j).r
      retract := by
        apply biproduct.hom_ext
        intro j
        simp [Category.assoc, (r j).retract] }
  exact ⟨⨁ X, ⨁ Y, ⟨rr.trans (productFunctorFiniteSumRetract X Y)⟩⟩

omit [Preadditive C] [MonoidalPreadditive C] [HasBinaryBiproducts C]
  [HasZeroObject C] [HasFiniteBiproducts C] in
/-- Product retracts contain every tensor power of each of their objects. -/
theorem productRetract_tensorPower {Z : CategoryTheory.Center C} (hZ : ProductRetract Z)
    (n : ℕ) : ProductRetract (tensorPower Z n) :=
  Nat.rec unit_productRetract (fun _ ih ↦ productRetract_tensor hZ ih) n

end PropertyF.Ground.Centre

/-! Closure of product retracts under generated objects in the actual centre. -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
namespace PropertyF.Ground.Centre
universe v u
variable {C : Type u} [Category.{v} C] [Abelian C] [MonoidalCategory C]
  [MonoidalPreadditive C] [RigidCategory C] [BraidedCategory C]
attribute [local instance] Abelian.hasFiniteBiproducts

/-- Every object generated by a product retract is again a product retract. -/
theorem productRetract_generatedBy {Z W : CategoryTheory.Center C}
    (hZ : ProductRetract Z) (hW : GeneratedBy Z W) : ProductRetract W :=
  match hW with
  | ⟨_, k, ⟨r⟩⟩ => productRetract_of_retract r
      (productRetract_finiteBiproduct _ (fun i ↦ productRetract_tensorPower hZ (k i)))

end PropertyF.Ground.Centre
