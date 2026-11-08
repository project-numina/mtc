module
public import MTC.PropertyF.Pivotal.GaloisDual

/-! # Exact duality pairings under strong monoidal functors -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.Functor.LaxMonoidal CategoryTheory.Functor.OplaxMonoidal
open CategoryTheory.Functor.Monoidal
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

end MTC.PropertyF.Pivotal
end
