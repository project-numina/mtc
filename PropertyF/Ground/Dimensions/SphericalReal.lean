module
public import PropertyF.Ground.Dimensions.PivotalDual
public import PropertyF.Ground.Dimensions.RootDualPairing
public import PropertyF.Ground.Dimensions.IntrinsicNonzero
public import PropertyF.Ground.Dimensions.PivotalTwist
public import PropertyF.Ground.Fusion.Agreement
public import PropertyF.Ground.Dimensions.PositiveCanonical
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
open scoped BigOperators
namespace PropertyF.Ground.Dimensions
universe v u
set_option backward.isDefEq.respectTransparency false in
/-- The left dimension is the right dimension of the dual object. -/
theorem pivotal_leftTrace_id_eq_rightTrace_dual {C : Type u} [Category.{v} C]
    [MonoidalCategory C] [RigidCategory C] (p : PivotalStructure (C := C)) (X : C) :
    p.leftTrace (𝟙 X) = p.rightTrace (𝟙 (Xᘁ)) := by
  rw [leftTrace_id, rightTrace_id, pivotal_dual, leftQuantumTrace_eq_rightDual]

/-- A pivotal fusion category is spherical exactly when all simple dimensions are real. -/
theorem pivotal_spherical_iff_simple_dimensions_real (C : Ground.BraidedFusionCategory.{v,u})
    (p : PivotalStructure (C := C.Obj)) :
    p.IsSpherical ↔ ∀ i, star (pivotalDimension C p (Ground.simples C i)) =
      pivotalDimension C p (Ground.simples C i) := by
  have hdual (i : Fin (Ground.rank C)) :
      Ground.unitScalar C (p.leftTrace (𝟙 (Ground.simples C i))) =
        star (pivotalDimension C p (Ground.simples C i)) := by
    rw [pivotal_leftTrace_id_eq_rightTrace_dual]
    change pivotalDimension C p ((Ground.simples C i)ᘁ) = _
    rw [pivotalDimension_iso C p (rightDualLabelIso C i), pivotalDimension_dual_eq_conj]
  rw [isSpherical_iff_simple_dimensions]
  constructor
  · intro h i
    rw [← hdual, h i]
    rfl
  · intro h i
    apply (Ground.unitScalarEquiv C).injective
    simpa only [← Ground.unitScalar_eq_equiv, pivotalDimension] using
      (hdual i).trans (h i)
end PropertyF.Ground.Dimensions
