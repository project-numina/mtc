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

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- A direct sum of two product images is a retract of a single product image.
The ambient product contains the two extra cross terms. -/
def productFunctor_sumRetract (X Y X' Y' : C) :
    Retract ((productFunctor.obj (X,Y)) ⊞ (productFunctor.obj (X',Y')))
      (productFunctor.obj (X ⊞ X', Y ⊞ Y')) where
  i := biprod.desc (productFunctor.map (biprod.inl, biprod.inl))
    (productFunctor.map (biprod.inr, biprod.inr))
  r := biprod.lift (productFunctor.map (biprod.fst, biprod.fst))
    (productFunctor.map (biprod.snd, biprod.snd))
  retract := by
    apply biprod.hom_ext'
    · apply biprod.hom_ext
      · simp only [Category.assoc, biprod.inl_desc_assoc, biprod.lift_fst]
        apply CategoryTheory.Center.ext
        simp [productFunctor, negative, tensorHom_comp_tensorHom]
      · simp only [Category.assoc, biprod.inl_desc_assoc, biprod.lift_snd]
        apply CategoryTheory.Center.ext
        simp [productFunctor, negative, tensorHom_comp_tensorHom]; rfl
    · apply biprod.hom_ext
      · simp only [Category.assoc, biprod.inr_desc_assoc, biprod.lift_fst]
        apply CategoryTheory.Center.ext
        simp [productFunctor, negative, tensorHom_comp_tensorHom]; rfl
      · simp only [Category.assoc, biprod.inr_desc_assoc, biprod.lift_snd]
        apply CategoryTheory.Center.ext
        simp [productFunctor, negative, tensorHom_comp_tensorHom]

/-- The direct sum of two retracts is a retract of the direct sum. -/
def biprodRetract {A B A' B' : CategoryTheory.Center C}
    (r : Retract A A') (s : Retract B B') : Retract (A ⊞ B) (A' ⊞ B') where
  i := biprod.map r.i s.i
  r := biprod.map r.r s.r
  retract := by
    apply biprod.hom_ext'
    · simp
    · simp

/-- Objects isomorphic to retracts of canonical product images. -/
def ProductRetract (Z : CategoryTheory.Center C) : Prop :=
  ∃ X Y : C, Nonempty (Retract Z (productFunctor.obj (X,Y)))

omit [Preadditive C] [MonoidalPreadditive C] [HasBinaryBiproducts C] in
/-- The class is closed under retracts. -/
theorem productRetract_of_retract {Z W : CategoryTheory.Center C}
    (r : Retract Z W) (h : ProductRetract W) : ProductRetract Z := by
  obtain ⟨X, Y, ⟨s⟩⟩ := h
  exact ⟨X, Y, ⟨r.trans s⟩⟩

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

/-- The class is closed under finite binary sums. -/
theorem productRetract_biprod {Z W : CategoryTheory.Center C}
    (hZ : ProductRetract Z) (hW : ProductRetract W) : ProductRetract (Z ⊞ W) := by
  obtain ⟨X, Y, ⟨r⟩⟩ := hZ
  obtain ⟨X', Y', ⟨s⟩⟩ := hW
  exact ⟨X ⊞ X', Y ⊞ Y', ⟨(biprodRetract r s).trans (productFunctor_sumRetract X Y X' Y')⟩⟩

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
    (hZ : ProductRetract Z) (hW : ProductRetract W) : ProductRetract (Z ⊗ W) := by
  obtain ⟨X, Y, ⟨r⟩⟩ := hZ
  obtain ⟨X', Y', ⟨s⟩⟩ := hW
  let e : (productFunctor.obj (X,Y) ⊗ productFunctor.obj (X',Y')) ≅
      productFunctor.obj (X ⊗ X', Y ⊗ Y') :=
    CategoryTheory.Functor.Monoidal.μIso productFunctor (X,Y) (X',Y')
  exact ⟨X ⊗ X', Y ⊗ Y', ⟨(tensorRetract r s).trans (Retract.ofIso e)⟩⟩

omit [Preadditive C] [MonoidalPreadditive C] [HasBinaryBiproducts C] in
/-- Property F holds on every product retract when the base category has property F. -/
theorem productRetract_propertyF {Z : CategoryTheory.Center C}
    (hZ : ProductRetract Z) (hC : HasPropertyF C) : ObjectPropertyF Z := by
  obtain ⟨X, Y, ⟨r⟩⟩ := hZ
  exact productFunctor_retract_objectPropertyF X Y Z r (hC X) (hC Y)

/-- The tensor, biproduct and retract closure of the two canonical images.
Dual closure is deliberately not included until centre rigidity is constructed. -/
inductive ProductTensorClosure : CategoryTheory.Center C → Prop
  | positive (X : C) : ProductTensorClosure ((CategoryTheory.Center.ofBraided C).obj X)
  | negative (X : C) : ProductTensorClosure ((negative C).obj X)
  | unit : ProductTensorClosure (𝟙_ (CategoryTheory.Center C))
  | tensor {Z W} : ProductTensorClosure Z → ProductTensorClosure W → ProductTensorClosure (Z ⊗ W)
  | biprod {Z W} : ProductTensorClosure Z → ProductTensorClosure W → ProductTensorClosure (Z ⊞ W)
  | retract {Z W} : Retract Z W → ProductTensorClosure W → ProductTensorClosure Z

/-- Every object in the explicit tensor closure is a retract of one product image. -/
theorem productTensorClosure_retract {Z : CategoryTheory.Center C}
    (h : ProductTensorClosure Z) : ProductRetract Z := by
  induction h with
  | positive X => exact positive_productRetract X
  | negative X => exact negative_productRetract X
  | unit => exact unit_productRetract
  | tensor _ _ hZ hW => exact productRetract_tensor hZ hW
  | biprod _ _ hZ hW => exact productRetract_biprod hZ hW
  | retract r _ hW => exact productRetract_of_retract r hW

/-- Property F passes to the explicitly generated tensor-retract closure. -/
theorem productTensorClosure_propertyF {Z : CategoryTheory.Center C}
    (hZ : ProductTensorClosure Z) (hC : HasPropertyF C) : ObjectPropertyF Z :=
  productRetract_propertyF (productTensorClosure_retract hZ) hC

/-- Each object in the explicit tensor closure has the product-image quotient
presentation used in the paper. -/
theorem productTensorClosure_image_quotient {Z : CategoryTheory.Center C}
    (hZ : ProductTensorClosure Z) (n : ℕ) :
    ∃ X Y : C, ∃ H : Subgroup (braidImage X n × braidImage Y n),
      ∃ q : H →* braidImage Z n, Function.Surjective q := by
  obtain ⟨X, Y, ⟨r⟩⟩ := productTensorClosure_retract hZ
  obtain ⟨H, q, hq⟩ := productFunctor_retract_image_quotient X Y Z r n
  exact ⟨X, Y, H, q, hq⟩

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
def productFunctor_finiteSumRetract {J : Type} [Fintype J] (X Y : J → C) :
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
  exact ⟨⨁ X, ⨁ Y, ⟨rr.trans (productFunctor_finiteSumRetract X Y)⟩⟩

omit [Preadditive C] [MonoidalPreadditive C] [HasBinaryBiproducts C]
  [HasZeroObject C] [HasFiniteBiproducts C] in
/-- Product retracts contain every tensor power of each of their objects. -/
theorem productRetract_tensorPower {Z : CategoryTheory.Center C} (hZ : ProductRetract Z)
    (n : ℕ) : ProductRetract (tensorPower Z n) := by
  induction n with
  | zero => exact unit_productRetract
  | succ n ih => exact productRetract_tensor hZ ih

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
    (hZ : ProductRetract Z) (hW : GeneratedBy Z W) : ProductRetract W := by
  obtain ⟨count, k, ⟨r⟩⟩ := hW
  exact productRetract_of_retract r
    (productRetract_finiteBiproduct _ (fun i => productRetract_tensorPower hZ (k i)))

end PropertyF.Ground.Centre
