module
public import MTC.Braided.Trace.SaturationSquare
public import MTC.PropertyF.Pivotal.SlopeTrace

/-! # General pivotal saturation

The actual pivotal tensor-square phase supplies the last hypothesis of the
complex-weight trace argument. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
open MTC.Fusion MTC.Braided MTC.Braided.Trace MTC.CategoryTheory.Dimensions
namespace MTC.PropertyF.Pivotal
universe v u

/-- For an actual simple object with finite braid images, maximal normalized
self-monodromy trace forces its pivotal dimension to attain the FP bound. -/
theorem pivotal_saturation (C : BraidedFusionCategory.{v,u})
    (p : PivotalStructure (C := C.Obj)) {X : C.Obj} [Simple X]
    (hfinite : ObjectPropertyF X)
    (hmax : ‖scalarTrace p (unitScalarEquiv C) (selfMonodromy X) /
      pivotalDimension C p X‖ = fpDimension C X) :
    ‖pivotalDimension C p X‖ = fpDimension C X :=
  saturation_of_square_slope C p hfinite (fun Y _ ⟨f, hf⟩ ↦
    pivotalDimension_tensor_square_phase C p X Y f hf) hmax

end MTC.PropertyF.Pivotal
