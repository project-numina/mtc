module
public import PropertyF.Ground.Dimensions.SphericalArithmetic
public import PropertyF.Ground.Fusion.Reciprocity
public import Mathlib.CategoryTheory.Monoidal.Rigid.Braided

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
namespace PropertyF.Ground.Dimensions
universe v u

/-- In a braided fusion category the right dual of a simple object is simple. -/
theorem simple_rightDual (C : Ground.BraidedFusionCategory.{v,u}) (X : C.Obj) [Simple X] :
    Simple (Xᘁ) := Ground.simple_rightDual C X

/-- A simple object has nonzero left quantum trace for any double-dual
isomorphism, by applying the right-trace result to its simple dual. -/
theorem leftQuantumTrace_simple_ne_zero (C : Ground.BraidedFusionCategory.{v,u})
    (X : C.Obj) [Simple X] (j : X ≅ (Xᘁ)ᘁ) : leftQuantumTrace j ≠ 0 := by
  let : Simple (Xᘁ) := Ground.simple_rightDual C X
  rw [leftQuantumTrace_eq_rightDual]
  exact rightQuantumTrace_simple_ne_zero C (Xᘁ) (rightDualIsoMap j).symm

/-- The intrinsic squared norm of every simple is nonzero, without assuming
any pivotal or spherical structure. -/
theorem target_squaredNorm_ne_zero (C : Ground.BraidedFusionCategory.{v,u})
    (X : C.Obj) [Simple X] : Ground.squaredNorm C X ≠ 0 := by
  unfold Ground.squaredNorm
  have hr := rightQuantumTrace_simple_ne_zero C X (Ground.doubleDualIso C X)
  have hl := leftQuantumTrace_simple_ne_zero C X (Ground.doubleDualIso C X)
  have hsr : Ground.unitScalar C (rightQuantumTrace (Ground.doubleDualIso C X)) ≠ 0 := by
    rw [Ground.unitScalar_eq_equiv]
    simpa using (Ground.unitScalarEquiv C).injective.ne hr
  have hsl : Ground.unitScalar C (leftQuantumTrace (Ground.doubleDualIso C X)) ≠ 0 := by
    rw [Ground.unitScalar_eq_equiv]
    simpa using (Ground.unitScalarEquiv C).injective.ne hl
  exact mul_ne_zero hsr hsl

/-- Dualizing a double-dual component twice exchanges its left and right
quantum traces. -/
theorem leftQuantumTrace_dual_component {C : Type u} [Category.{v} C] [MonoidalCategory C]
    [RigidCategory C] {X : C} (j : X ≅ (Xᘁ)ᘁ) :
    leftQuantumTrace (rightDualIsoMap j).symm = rightQuantumTrace j := by
  rw [leftQuantumTrace_eq_rightDual]
  have hdual : (rightDualIsoMap (rightDualIsoMap j).symm).symm =
      rightDualIsoMap (rightDualIsoMap j) := by
    apply Iso.ext
    rfl
  rw [hdual]
  exact (rightQuantumTrace_iso j (rightDualIsoMap (rightDualIsoMap j)) j (by rfl)).symm

/-- The intrinsic squared norm is invariant under right duality, without any
pivotal or spherical structure. -/
theorem target_squaredNorm_rightDual (C : Ground.BraidedFusionCategory.{v,u})
    (X : C.Obj) [Simple X] : Ground.squaredNorm C (Xᘁ) = Ground.squaredNorm C X := by
  let : Simple (Xᘁ) := Ground.simple_rightDual C X
  let j := Ground.doubleDualIso C X
  rw [target_squaredNorm_choice_independent C (Xᘁ) (rightDualIsoMap j).symm,
    target_squaredNorm_choice_independent C X j]
  rw [← leftQuantumTrace_eq_rightDual j, leftQuantumTrace_dual_component]
  exact mul_comm _ _

/-- In a spherical fusion category, a simple and its dual have the same
squared pivotal dimension. -/
theorem spherical_pivotalDimension_rightDual_sq (C : Ground.BraidedFusionCategory.{v,u})
    (p : PivotalStructure (C := C.Obj)) (hp : p.IsSpherical) (X : C.Obj) [Simple X] :
    pivotalDimension C p (Xᘁ) ^ 2 = pivotalDimension C p X ^ 2 := by
  let : Simple (Xᘁ) := Ground.simple_rightDual C X
  have h := target_squaredNorm_rightDual C X
  rw [target_squaredNorm_eq_dimension_sq C p hp (Xᘁ),
    target_squaredNorm_eq_dimension_sq C p hp X] at h
  simpa [pivotalDimension, rightTrace_id] using h

end PropertyF.Ground.Dimensions
