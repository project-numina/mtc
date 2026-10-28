module
public import PropertyF.Ground.Modular.SMatrix
public import PropertyF.Ground.Fusion.Reciprocity
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Nonvanishing of simple pivotal dimensions

Rigidity identifies the Hom space from X ⊗ X* to the tensor unit with End(X),
which is one-dimensional by Schur. Semisimplicity splits coevaluation; the
nonzero evaluation must be a nonzero multiple of that splitting. Consequently
the pivotal dimension of a simple object cannot vanish.
-/
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open PropertyF.Ground.Dimensions
@[expose] public noncomputable section
namespace PropertyF.Ground.Modular
universe v u

/-- A simple object has nonzero pivotal trace of the identity. -/
theorem pivotalTrace_simple_ne_zero (C : Ground.BraidedFusionCategory.{v,u})
    (p : PivotalStructure (C := C.Obj)) (X : C.Obj) [Simple X] :
    p.rightTrace (𝟙 X) ≠ 0 := by
  simpa only [Dimensions.rightTrace_id] using
    Dimensions.rightQuantumTrace_simple_ne_zero C X (p.iso X)

/-- The scalar pivotal trace of a simple object is nonzero. -/
theorem unitScalar_rightTrace_ne_zero (C : Ground.BraidedFusionCategory.{v,u})
    (p : PivotalStructure (C := C.Obj)) (X : C.Obj) [Simple X] :
    groundUnitScalarEquiv C (p.rightTrace (𝟙 X)) ≠ 0 := by
  simpa only [map_zero] using
    (groundUnitScalarEquiv C).injective.ne (pivotalTrace_simple_ne_zero C p X)

/-- Every simple categorical dimension is nonzero, without pseudo-unitarity. -/
theorem simpleDimension_ne_zero (C : Ground.BraidedFusionCategory.{v,u})
    (p : PivotalStructure (C := C.Obj)) (i : Fin (rank C)) :
    simpleDimension C p i ≠ 0 := by
  let _ : Simple (simples C i) := simples_simple C i
  simpa only [simpleDimension, ← Ground.unitScalar_eq_equiv, ← groundUnitScalarEquiv_apply] using
    unitScalar_rightTrace_ne_zero C p (simples C i)

end PropertyF.Ground.Modular
