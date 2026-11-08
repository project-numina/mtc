module
public import MTC.Center.Normalization.ActualDoubleCentralizer
public import MTC.PropertyF.Pivotal.NondegeneracyRelative

open MTC.Fusion MTC.Braided MTC.Center.Braid MTC.CategoryTheory.Dimensions
open MTC.PropertyF.Reduction MTC.Modular

/-! # Actual centre centralizers

The two centralizer identities are proved on every actual centre object. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace MTC.Center.Normalization
universe v u
variable (C : BraidedFusionCategory.{v,u})
  [RigidCategory (Center C.Obj)] [IsFusionCategory (Center C.Obj)]
local notation "Z" => bundledCenter C

/-- The centralizer of the actual transparent positive image consists
exactly of the actual product retracts. -/
theorem productRetract_iff_centralizes_transparentPositive
    (pZ : PivotalStructure (C := Center C.Obj)) (W : Center C.Obj) :
    MTC.Center.ProductRetract W ↔
      ∀ E : Center C.Obj, (∃ X : C.Obj, MTC.Center.Transparent X ∧
        Nonempty (E ≅ (Center.ofBraided C.Obj).obj X)) → MTC.Center.Centralizes W E :=
  productRetract_iff_centralizes_transparentPositive_of_relative C pZ
    (MTC.PropertyF.Pivotal.relative_fusionSubring_numerical_centrality Z pZ) W

/-- The product-retract and transparent-positive-image classes are mutual
actual objectwise centralizers. Every product retract has property F when the
base category does. -/
theorem center_product_centralizer_and_propertyF
    (pZ : PivotalStructure (C := Center C.Obj)) :
    (∀ W : Center C.Obj,
      (∀ P : Center C.Obj, MTC.Center.ProductRetract P → MTC.Center.Centralizes W P) ↔
        ∃ X : C.Obj, MTC.Center.Transparent X ∧
          Nonempty (W ≅ (Center.ofBraided C.Obj).obj X)) ∧
    (∀ W : Center C.Obj, MTC.Center.ProductRetract W ↔
      ∀ E : Center C.Obj, (∃ X : C.Obj, MTC.Center.Transparent X ∧
        Nonempty (E ≅ (Center.ofBraided C.Obj).obj X)) → MTC.Center.Centralizes W E) ∧
    (HasPropertyF C.Obj → ∀ W : Center C.Obj, MTC.Center.ProductRetract W → ObjectPropertyF W) := by
  refine ⟨fun W => productRetractCentralizer_iff W, ?_, ?_⟩
  · exact fun W => productRetract_iff_centralizes_transparentPositive C pZ W
  · intro hF W hW
    exact MTC.Center.productRetract_propertyF hW hF

end MTC.Center.Normalization
end
