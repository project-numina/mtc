module
public import PropertyF.Ground.Cabling.FusionCycle
public import PropertyF.Ground.Fusion.GeneratedRigidity
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
@[expose] public noncomputable section
namespace PropertyF.Ground.Cabling
universe v u
attribute [local instance] Abelian.hasFiniteBiproducts

/-- Every generator has its right dual in its generated subcategory. -/
theorem generatedBy_rightDual (D : Ground.BraidedFusionCategory.{v,u}) (X : D.Obj) :
    GeneratedBy X (Xᘁ) :=
  Ground.generatedBy_rightDual D X

/-- Generated full subcategories of genuine braided fusion categories are rigid. -/
@[instance_reducible] def generatedCategoryRigid
    (D : Ground.BraidedFusionCategory.{v,u}) (X : D.Obj) :
    RigidCategory (generatedCategory X) :=
  generatedCategoryRigidOfGeneratorDual X (generatedBy_rightDual D X)
end PropertyF.Ground.Cabling
