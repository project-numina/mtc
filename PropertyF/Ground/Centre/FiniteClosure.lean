module
public import PropertyF.Ground.Centre.ProductClosure

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
