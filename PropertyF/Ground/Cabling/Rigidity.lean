module
public import PropertyF.Ground.Cabling.Generated
public import Mathlib.CategoryTheory.Monoidal.Rigid.OfEquivalence
public import Mathlib.CategoryTheory.Monoidal.Rigid.Braided

/-! Rigidity of the generated subcategory from closure under right duals. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [Abelian C] [MonoidalPreadditive C] [RigidCategory C]

/-- If the generated objects are closed under ambient right duals, the full
subcategory is right rigid, with the evaluation and coevaluation lifted along
the fully faithful monoidal inclusion. -/
@[instance_reducible] def generatedCategoryRightRigidOfDualClosure (X : C)
    (hdual : ∀ Y : C, GeneratedBy X Y → GeneratedBy X (Yᘁ)) :
    RightRigidCategory (generatedCategory X) where
  rightDual Y := {
    rightDual := ⟨Y.objᘁ, hdual Y.obj Y.property⟩
    exact := by
      let _ : ExactPairing ((generatedInclusion X).obj Y)
          ((generatedInclusion X).obj ⟨Y.objᘁ, hdual Y.obj Y.property⟩) :=
        inferInstanceAs (ExactPairing Y.obj Y.objᘁ)
      exact ExactPairing.ofFullyFaithful (generatedInclusion X) _ _
  }

/-- Braiding turns right rigidity into full rigidity. -/
@[instance_reducible] def generatedCategoryRigidOfDualClosure (X : C)
    (hdual : ∀ Y : C, GeneratedBy X Y → GeneratedBy X (Yᘁ)) :
    RigidCategory (generatedCategory X) := by
  let _ := generatedCategoryRightRigidOfDualClosure X hdual
  exact BraidedCategory.rigidCategoryOfRightRigidCategory

end PropertyF
