module
public import MTC.PropertyF.Pivotal.GaloisDual
public import MTC.CategoryTheory.Dimensions.DualCoherence

/-! # Exact duality pairings under strong monoidal functors -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.Functor.LaxMonoidal CategoryTheory.Functor.OplaxMonoidal
open CategoryTheory.Functor.Monoidal
open MTC.CategoryTheory.Dimensions
namespace MTC.PropertyF.Pivotal
set_option linter.style.haveILetI false
universe v u v' u'
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
variable {D : Type u'} [Category.{v'} D] [MonoidalCategory D]

/-- A strong monoidal functor carries an actual exact pairing to an actual
exact pairing, with the usual monoidal unit and tensor comparisons. -/
@[instance_reducible] def exactPairingOfMonoidalFunctor
    (F : C ⥤ D) [F.Monoidal] (X Y : C) [ExactPairing X Y] :
    ExactPairing (F.obj X) (F.obj Y) where
  coevaluation' := ε F ≫ F.map (η_ X Y) ≫ δ F X Y
  evaluation' := μ F Y X ≫ F.map (ε_ X Y) ≫ η F
  coevaluation_evaluation' := by
    simp only [whiskerLeft_comp, comp_whiskerRight, Category.assoc, map_associator_inv',
      whiskerLeft_δ_μ_assoc, whiskerRight_δ_μ_assoc]
    rw [μ_natural_right_assoc, δ_natural_left_assoc, ← F.map_comp_assoc, ← F.map_comp_assoc]
    simp only [Category.assoc, ExactPairing.coevaluation_evaluation, F.map_comp]
    rw [← Functor.LaxMonoidal.right_unitality_assoc, ← Functor.OplaxMonoidal.left_unitality]
  evaluation_coevaluation' := by
    simp only [whiskerLeft_comp, comp_whiskerRight, Category.assoc, map_associator',
      whiskerLeft_δ_μ_assoc, whiskerRight_δ_μ_assoc]
    rw [μ_natural_left_assoc, δ_natural_right_assoc, ← F.map_comp_assoc, ← F.map_comp_assoc]
    simp only [Category.assoc, ExactPairing.evaluation_coevaluation, F.map_comp]
    rw [← Functor.LaxMonoidal.left_unitality_assoc, ← Functor.OplaxMonoidal.right_unitality]

/-- Evaluation of the transported pairing is the image of the original
  evaluation with its canonical monoidal comparisons. -/
theorem monoidalFunctor_pairing_evaluation
    (F : C ⥤ D) [F.Monoidal] (X Y : C) [ExactPairing X Y] :
    letI := exactPairingOfMonoidalFunctor F X Y
    F.map (ε_ X Y) = δ F Y X ≫ ε_ (F.obj X) (F.obj Y) ≫ ε F := by
  letI := exactPairingOfMonoidalFunctor F X Y
  change F.map (ε_ X Y) = δ F Y X ≫ (μ F Y X ≫ F.map (ε_ X Y) ≫ η F) ≫ ε F
  simp [Category.assoc]

/-- Coevaluation of the transported pairing is the image of the original
  coevaluation with its canonical monoidal comparisons. -/
theorem monoidalFunctor_pairing_coevaluation
    (F : C ⥤ D) [F.Monoidal] (X Y : C) [ExactPairing X Y] :
    letI := exactPairingOfMonoidalFunctor F X Y
    F.map (η_ X Y) = η F ≫ η_ (F.obj X) (F.obj Y) ≫ μ F X Y := by
  letI := exactPairingOfMonoidalFunctor F X Y
  change F.map (η_ X Y) = η F ≫ (ε F ≫ F.map (η_ X Y) ≫ δ F X Y) ≫ μ F X Y
  simp [Category.assoc]

/-- A strong monoidal functor carries the right closed duality diagram to the
closed diagram built from the transported pairings. -/
theorem monoidalFunctor_rightClosedDiagram (F : C ⥤ D) [F.Monoidal]
    (X Y Z : C) [ExactPairing X Y] [ExactPairing Y Z] (f : X ⟶ Z) :
    (ε F ≫ F.map (η_ X Y ≫ (f ⊗ₘ 𝟙 Y) ≫ ε_ Y Z) ≫ η F) =
      (ε F ≫ F.map (η_ X Y) ≫ δ F X Y) ≫
        (F.map f ⊗ₘ 𝟙 (F.obj Y)) ≫ (μ F Z Y ≫ F.map (ε_ Y Z) ≫ η F) := by
  simp only [Functor.map_comp, map_tensor, F.map_id, Category.assoc]

/-- A strong monoidal functor carries the left closed duality diagram to the
closed diagram built from the transported pairings. -/
theorem monoidalFunctor_leftClosedDiagram (F : C ⥤ D) [F.Monoidal]
    (X Y Z : C) [ExactPairing X Y] [ExactPairing Y Z] (g : Z ⟶ X) :
    (ε F ≫ F.map (η_ Y Z ≫ (𝟙 Y ⊗ₘ g) ≫ ε_ X Y) ≫ η F) =
      (ε F ≫ F.map (η_ Y Z) ≫ δ F Y Z) ≫
        (𝟙 (F.obj Y) ⊗ₘ F.map g) ≫ (μ F Y X ≫ F.map (ε_ X Y) ≫ η F) := by
  simp only [Functor.map_comp, map_tensor, F.map_id, Category.assoc]

variable [RightRigidCategory C] [RightRigidCategory D]

/-- The comparison from the functor image of a chosen right dual to the
chosen right dual of its image. -/
def monoidalFunctorDualIso (F : C ⥤ D) [F.Monoidal] (X : C) :
    F.obj (Xᘁ) ≅ (F.obj X)ᘁ :=
  rightDualIso (exactPairingOfMonoidalFunctor F X (Xᘁ)) HasRightDual.exact

/-- The dual comparison carries the transported coevaluation to the chosen
coevaluation. -/
theorem monoidalFunctorDual_coevaluation
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
    {D : Type u'} [Category.{v'} D] [MonoidalCategory D] [RightRigidCategory D]
    (F : C ⥤ D) [F.Monoidal] (X : C) :
    (ε F ≫ F.map (η_ X (Xᘁ)) ≫ δ F X (Xᘁ)) ≫
      F.obj X ◁ (monoidalFunctorDualIso F X).hom = η_ (F.obj X) ((F.obj X)ᘁ) := by
  have h := coevaluation_rightDualIso (exactPairingOfMonoidalFunctor F X (Xᘁ))
    (HasRightDual.exact (X := F.obj X))
  change (ε F ≫ F.map (η_ X (Xᘁ)) ≫ δ F X (Xᘁ)) ≫
    F.obj X ◁ (monoidalFunctorDualIso F X).hom = _ at h
  exact h

/-- The chosen evaluation carries the dual comparison to the transported
evaluation. -/
theorem monoidalFunctorDual_evaluation
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
    {D : Type u'} [Category.{v'} D] [MonoidalCategory D] [RightRigidCategory D]
    (F : C ⥤ D) [F.Monoidal] (X : C) :
    ((monoidalFunctorDualIso F X).hom ▷ F.obj X) ≫ ε_ (F.obj X) ((F.obj X)ᘁ) =
      μ F (Xᘁ) X ≫ F.map (ε_ X (Xᘁ)) ≫ η F := by
  have h := rightDualIso_evaluation (exactPairingOfMonoidalFunctor F X (Xᘁ))
    (HasRightDual.exact (X := F.obj X))
  change ((monoidalFunctorDualIso F X).hom ▷ F.obj X) ≫ _ =
    μ F (Xᘁ) X ≫ F.map (ε_ X (Xᘁ)) ≫ η F at h
  exact h

end MTC.PropertyF.Pivotal
end
