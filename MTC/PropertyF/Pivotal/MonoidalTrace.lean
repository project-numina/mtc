module
public import MTC.PropertyF.Pivotal.MonoidalDual

/-! # Closed duality diagrams under strong monoidal functors -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.Functor.LaxMonoidal CategoryTheory.Functor.OplaxMonoidal
open CategoryTheory.Functor.Monoidal
namespace MTC.PropertyF.Pivotal
universe v u v' u'
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
variable {D : Type u'} [Category.{v'} D] [MonoidalCategory D]

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

end MTC.PropertyF.Pivotal
end
