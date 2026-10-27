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
/-- Once the actual centre is a rigid fusion category, duals of product
retracts are product retracts, using fusion-category generation. -/
theorem productRetract_rightDual (D : Ground.BraidedFusionCategory.{v,u})
    [RigidCategory (CategoryTheory.Center D.Obj)]
    [IsFusionCategory (CategoryTheory.Center D.Obj)]
    {Z : CategoryTheory.Center D.Obj} (hZ : ProductRetract Z) :
    ProductRetract (Zᘁ) :=
  productRetract_generatedBy hZ (Ground.generatedBy_rightDual (Integrate.bundledCenter D) Z)

end PropertyF.Ground.Centre
