module
public import MTC.PropertyF.Pivotal.MonoidalDual
public import MTC.CategoryTheory.Dimensions.DualCoherence

/-! # Comparing transported and chosen duals -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.Functor.LaxMonoidal CategoryTheory.Functor.OplaxMonoidal
open MTC.CategoryTheory.Dimensions
namespace MTC.PropertyF.Pivotal
universe v u v' u'
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
variable {D : Type u'} [Category.{v'} D] [MonoidalCategory D] [RightRigidCategory D]

/-- The comparison from the functor image of a chosen right dual to the
chosen right dual of its image. -/
def monoidalFunctorDualIso (F : C ⥤ D) [F.Monoidal] (X : C) :
    F.obj (Xᘁ) ≅ (F.obj X)ᘁ :=
  rightDualIso (exactPairingOfMonoidalFunctor F X (Xᘁ)) HasRightDual.exact

/-- The dual comparison carries the transported coevaluation to the chosen
coevaluation. -/
theorem monoidalFunctorDual_coevaluation (F : C ⥤ D) [F.Monoidal] (X : C) :
    (ε F ≫ F.map (η_ X (Xᘁ)) ≫ δ F X (Xᘁ)) ≫
      F.obj X ◁ (monoidalFunctorDualIso F X).hom = η_ (F.obj X) ((F.obj X)ᘁ) := by
  have h := coevaluation_rightDualIso (exactPairingOfMonoidalFunctor F X (Xᘁ))
    (HasRightDual.exact (X := F.obj X))
  change (ε F ≫ F.map (η_ X (Xᘁ)) ≫ δ F X (Xᘁ)) ≫
    F.obj X ◁ (monoidalFunctorDualIso F X).hom = _ at h
  exact h

/-- The chosen evaluation carries the dual comparison to the transported
evaluation. -/
theorem monoidalFunctorDual_evaluation (F : C ⥤ D) [F.Monoidal] (X : C) :
    ((monoidalFunctorDualIso F X).hom ▷ F.obj X) ≫ ε_ (F.obj X) ((F.obj X)ᘁ) =
      μ F (Xᘁ) X ≫ F.map (ε_ X (Xᘁ)) ≫ η F := by
  have h := rightDualIso_evaluation (exactPairingOfMonoidalFunctor F X (Xᘁ))
    (HasRightDual.exact (X := F.obj X))
  change ((monoidalFunctorDualIso F X).hom ▷ F.obj X) ≫ _ =
    μ F (Xᘁ) X ≫ F.map (ε_ X (Xᘁ)) ≫ η F at h
  exact h

end MTC.PropertyF.Pivotal
end
