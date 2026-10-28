module
public import PropertyF.Ground.Centre.GeneratedClosure
public import PropertyF.Ground.Cabling.GeneralDual
public import PropertyF.Ground.Fusion.GeneratedRigidity
public import PropertyF.Ground.Integrate.CenterBundle

/-! The generated centre product subcategory and its dual closure. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
namespace PropertyF.Ground.Centre
universe v u
variable {C : Type u} [Category.{v} C] [Abelian C] [MonoidalCategory C]
  [MonoidalPreadditive C] [RigidCategory C] [BraidedCategory C]
attribute [local instance] Abelian.hasFiniteBiproducts

omit [RigidCategory C] in
/-- Every product image is built from one positive and one negative image. -/
theorem productFunctor_tensorClosure (X Y : C) :
    ProductTensorClosure (productFunctor.obj (X,Y)) :=
  ProductTensorClosure.tensor (ProductTensorClosure.positive X) (ProductTensorClosure.negative Y)

/-- Product retracts are exactly the tensor, finite-sum and retract closure
of the two canonical centre embeddings. -/
theorem productRetract_iff_tensorClosure (Z : CategoryTheory.Center C) :
    ProductRetract Z ↔ ProductTensorClosure Z :=
  ⟨fun ⟨X, Y, ⟨r⟩⟩ ↦ ProductTensorClosure.retract r (productFunctor_tensorClosure X Y),
    productTensorClosure_retract⟩

/-- Once the actual centre is a rigid fusion category, duals of product
retracts are product retracts, using fusion-category generation. -/
theorem productRetract_rightDual (D : Ground.BraidedFusionCategory.{v,u})
    [RigidCategory (CategoryTheory.Center D.Obj)]
    [IsFusionCategory (CategoryTheory.Center D.Obj)]
    {Z : CategoryTheory.Center D.Obj} (hZ : ProductRetract Z) :
    ProductRetract (Zᘁ) :=
  productRetract_generatedBy hZ (Ground.generatedBy_rightDual (Integrate.bundledCenter D) Z)

/-- The same generated closure is stable under centre right duals. -/
theorem productTensorClosure_rightDual (D : Ground.BraidedFusionCategory.{v,u})
    [RigidCategory (CategoryTheory.Center D.Obj)]
    [IsFusionCategory (CategoryTheory.Center D.Obj)]
    {Z : CategoryTheory.Center D.Obj} (hZ : ProductTensorClosure Z) :
    ProductTensorClosure (Zᘁ) :=
  (productRetract_iff_tensorClosure _).mp
    (productRetract_rightDual D (productTensorClosure_retract hZ))

end PropertyF.Ground.Centre
