module
public import PropertyF.Ground.Dimensions.SphericalArithmetic
public import PropertyF.Ground.Fusion.Reciprocity
public import Mathlib.CategoryTheory.Monoidal.Rigid.Braided

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
namespace PropertyF.Ground.Dimensions
universe v u

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

end PropertyF.Ground.Dimensions
