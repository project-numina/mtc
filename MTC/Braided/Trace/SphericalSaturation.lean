module
public import MTC.Braided.Trace.MonodromyReciprocity
public import MTC.CategoryTheory.Dimensions.DoubleDualPairing

/-!
# Spherical specialization of pivotal saturation

Spherical dimensions are real, so the general complex-weight trace argument
applies even if some block weights vanish or have mixed signs.
-/

open MTC.Algebra MTC.Fusion MTC.Braided MTC.CategoryTheory.Dimensions
open CategoryTheory CategoryTheory.MonoidalCategory

@[expose] public noncomputable section
namespace MTC.Braided.Trace
universe v u

/-- In a spherical braided fusion category, maximal normalized monodromy trace
and finite braid images imply equality of absolute and FP dimensions. No
positivity or nonvanishing assumption on braid-block weights is needed. -/
theorem spherical_saturation
    (C : BraidedFusionCategory.{v,u}) (p : PivotalStructure (C := C.Obj))
    (hp : p.IsSpherical) {X : C.Obj} [Simple X] (hfinite : ObjectPropertyF X)
    (hmax : ‖scalarTrace p (MTC.Fusion.unitScalarEquiv C) (selfMonodromy X) /
      pivotalDimension C p X‖ = MTC.Fusion.fpDimension C X) :
    ‖pivotalDimension C p X‖ = MTC.Fusion.fpDimension C X := by
  apply saturation_of_constituent_phase C p hfinite 1 (by simp) ?_ hmax
  intro i _
  simpa using ((pivotal_spherical_iff_simple_dimensions_real C p).mp hp i).symm

end MTC.Braided.Trace
