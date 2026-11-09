module
public import MTC.Center.Normalization.ProductCategory
public import MTC.Center.Induction.PivotalFusion

open MTC.Fusion MTC.Braided MTC.CategoryTheory.Dimensions

/-! # Product-image fusion category from ambient pivotality -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace MTC.Center.Normalization
universe v u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable (C : BraidedFusionCategory.{v,u})

/-- The actual product-image fusion category, constructing all centre
instances from the given ambient pivotal structure. -/
def productCategoryOfPivotal (p : PivotalStructure (C := C.Obj)) : BraidedFusionCategory.{v,max u v} := by
  let _ : RigidCategory (Center C.Obj) := MTC.Center.Rigid.rigidCenter
  let _ : IsFusionCategory (Center C.Obj) := MTC.Center.Induction.center_fusion_of_pivotal p
  exact bundledProductCategory C

/-- The actual product-image fusion category has property F whenever the
ambient category has property F. -/
theorem productCategoryOfPivotal_propertyF (p : PivotalStructure (C := C.Obj))
    (hF : HasPropertyF C.Obj) : HasPropertyF (productCategoryOfPivotal C p).Obj := by
  let _ : RigidCategory (Center C.Obj) := MTC.Center.Rigid.rigidCenter
  let _ : IsFusionCategory (Center C.Obj) := MTC.Center.Induction.center_fusion_of_pivotal p
  exact productCategory_propertyF C hF

end MTC.Center.Normalization
end
