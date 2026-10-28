module
public import PropertyF.Ground.Dimensions.DimensionCharacter
public import PropertyF.Ground.Dimensions.GlobalInequality
public import PropertyF.Ground.Integrate.CharacterReality
public import PropertyF.Ground.Modular.SMatrix
public import PropertyF.Ground.Fusion.Reciprocity
public import Mathlib.CategoryTheory.Monoidal.Rigid.Braided

open scoped BigOperators

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.Dimensions

/-- Simple pivotal dimensions are nonzero, by rigidity, semisimplicity and Schur. -/
theorem pivotalDimension_simple_ne_zero (C : Ground.BraidedFusionCategory)
    (p : PivotalStructure (C := C.Obj)) (i : Fin (Ground.rank C)) :
    pivotalDimension C p (Ground.simples C i) ≠ 0 := by
  have h := Ground.Modular.simpleDimension_ne_zero C p i
  simpa [Ground.Modular.simpleDimension, pivotalDimension, Ground.unitScalar_eq_equiv] using h

end PropertyF.Ground.Dimensions

end

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
namespace PropertyF.Ground.Dimensions
universe v u

variable (C : Ground.BraidedFusionCategory.{v,u})
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
theorem target_squaredNorm_rightDual
    (X : C.Obj) [Simple X] : Ground.squaredNorm C (Xᘁ) = Ground.squaredNorm C X := by
  let : Simple (Xᘁ) := Ground.simple_rightDual C X
  let j := Ground.doubleDualIso C X
  rw [target_squaredNorm_choice_independent C (Xᘁ) (rightDualIsoMap j).symm,
    target_squaredNorm_choice_independent C X j]
  rw [← leftQuantumTrace_eq_rightDual j, leftQuantumTrace_dual_component]
  exact mul_comm _ _

end PropertyF.Ground.Dimensions

end
