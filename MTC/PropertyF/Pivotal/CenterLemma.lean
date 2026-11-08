module
public import MTC.Center.Normalization.CenterLemma
public import MTC.Center.Rigid
public import MTC.Center.Induction.PivotalFusion

/-! # The centre lemma for a pivotal base category -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
open MTC.Fusion MTC.Braided MTC.CategoryTheory.Dimensions
namespace MTC.PropertyF.Pivotal
universe v u

/-- The actual product-generated and transparent-image classes in the
Drinfeld centre are mutual centralizers, and property F transfers to every
actual product-generated object. Centre rigidity, fusion and pivotality are
constructed from the given pivotal base category. -/
theorem centerLemma_of_pivotal (C : BraidedFusionCategory.{v,u})
    (p : PivotalStructure (C := C.Obj)) :
    (∀ W : Center C.Obj,
      (∀ P : Center C.Obj, MTC.Center.ProductRetract P → MTC.Center.Centralizes W P) ↔
        ∃ X : C.Obj, MTC.Center.Transparent X ∧
          Nonempty (W ≅ (Center.ofBraided C.Obj).obj X)) ∧
    (∀ W : Center C.Obj, MTC.Center.ProductRetract W ↔
      ∀ E : Center C.Obj, (∃ X : C.Obj, MTC.Center.Transparent X ∧
        Nonempty (E ≅ (Center.ofBraided C.Obj).obj X)) → MTC.Center.Centralizes W E) ∧
    (HasPropertyF C.Obj → ∀ W : Center C.Obj, MTC.Center.ProductRetract W → ObjectPropertyF W) := by
  letI : RigidCategory (Center C.Obj) := MTC.Center.Rigid.rigidCenter
  letI : IsFusionCategory (Center C.Obj) := MTC.Center.Induction.center_fusion_of_pivotal p
  let pZ := MTC.Center.Induction.liftedPivotalStructure p
    (MTC.Center.Induction.pivotalComponentsCentral_proved p)
  exact MTC.Center.Normalization.center_product_centralizer_and_propertyF C pZ

end MTC.PropertyF.Pivotal
end
