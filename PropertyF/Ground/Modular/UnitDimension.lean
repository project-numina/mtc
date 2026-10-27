module
public import PropertyF.Ground.Modular.DimensionNonzero
public import PropertyF.Ground.Dimensions.DualCoherence

/-! The unit axiom of a pivotal structure normalizes the tensor-unit trace. -/
open CategoryTheory CategoryTheory.MonoidalCategory
open PropertyF.Ground.Dimensions
@[expose] public noncomputable section
namespace PropertyF.Ground.Modular
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]

/-- The dimension of the simple representative of the tensor unit is one. -/
theorem simpleDimension_unit (C : Ground.BraidedFusionCategory.{v,u})
    (p : PivotalStructure (C := C.Obj)) : simpleDimension C p (unitIndex C) = 1 := by
  obtain ⟨e⟩ := unitIndex_iso C
  unfold simpleDimension
  rw [p.rightTrace_id_iso e, Dimensions.rightTrace_unit, map_one]

end PropertyF.Ground.Modular
