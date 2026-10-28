module
public import PropertyF.Ground.Fusion.Agreement
public import PropertyF.Ground.Dimensions.DimensionCharacter
public import PropertyF.Ground.Dimensions.GroundNorm
public import PropertyF.Ground.Integrate.CharacterReality
public import PropertyF.Ground.Modular.SMatrix
public import PropertyF.Ground.Fusion.Reciprocity
public import Mathlib.CategoryTheory.Monoidal.Rigid.Braided

/-! # Nonzero simple dimensions

Squared norms respect right duals.
-/
open scoped BigOperators

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
namespace PropertyF.Ground.Dimensions
universe v u

variable (C : BraidedFusionCategory.{v,u})
/-- Dualizing a double-dual component twice exchanges its left and right
quantum traces. -/
theorem leftQuantumTrace_dual_component {C : Type u} [Category.{v} C] [MonoidalCategory C]
    [RigidCategory C] {X : C} (j : X ≅ (Xᘁ)ᘁ) :
    leftQuantumTrace (rightDualIsoMap j).symm = rightQuantumTrace j := by
  rw [leftQuantumTrace_eq_rightDual]
  exact (rightQuantumTrace_iso (j := j) (k := rightDualIsoMap (rightDualIsoMap j)) j (by rfl)).symm

/-- The intrinsic squared norm is invariant under right duality, without any
pivotal or spherical structure. -/
theorem target_squaredNorm_rightDual
    (X : C.Obj) [Simple X] : squaredNorm C (Xᘁ) = squaredNorm C X := by
  let : Simple (Xᘁ) := simple_rightDual C X
  let j := doubleDualIso C X
  rw [target_squaredNorm_choice_independent C (rightDualIsoMap j).symm,
    target_squaredNorm_choice_independent C j]
  rw [← leftQuantumTrace_eq_rightDual j, leftQuantumTrace_dual_component]
  exact mul_comm _ _

end PropertyF.Ground.Dimensions

end
