module
public import PropertyF.Ground.Calculus.PartialTraceGround

/-! The graphical recurrence for two overlapping endomorphisms. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.Calculus
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [Preadditive C] [Linear ℂ C]

/-- Embed a fresh endomorphism after a left spectator, with the associator
explicit. -/
def overlapFresh (A X Y : C) (u : End (X ⊗ Y)) : End ((A ⊗ X) ⊗ Y) :=
  End.of ((α_ A X Y).hom ≫ (A ◁ u.asHom) ≫ (α_ A X Y).inv)

/-- Multiply an old endomorphism by a new one sharing the middle factor. -/
def overlapEndProduct (A X Y : C) (v : End (A ⊗ X)) (u : End (X ⊗ Y)) :
    End ((A ⊗ X) ⊗ Y) := insertRightIdentity (A ⊗ X) Y v * overlapFresh A X Y u

/-- Tracing the new strands of the overlap gives the old operator times the
normalized trace of the fresh operator. -/
theorem rightPartialTrace_overlap (C : Ground.BraidedFusionCategory.{v,u})
    (A X Y : C.Obj) [Simple X] (p : Dimensions.PivotalStructure (C := C.Obj))
    (scalar : End (𝟙_ C.Obj) ≃ₐ[ℂ] ℂ) (v : End (A ⊗ X)) (u : End (X ⊗ Y)) :
    rightPartialTrace p (A ⊗ X) Y (overlapEndProduct A X Y v u) =
      (scalar (p.rightTrace u.asHom) / scalar (p.rightTrace (𝟙 X))) • v := by
  rw [overlapEndProduct, rightPartialTrace_left, overlapFresh, rightPartialTrace_whiskerLeft,
    rightPartialTrace_simple_ground C X Y p scalar u]
  apply End.ext
  simp

/-- The categorical trace obeys the overlap recurrence with no braid-span
closure assumption on arbitrary partial traces. -/
theorem pivotalTrace_overlap (C : Ground.BraidedFusionCategory.{v,u})
    (A X Y : C.Obj) [Simple X] (p : Dimensions.PivotalStructure (C := C.Obj))
    (scalar : End (𝟙_ C.Obj) ≃ₐ[ℂ] ℂ) (v : End (A ⊗ X)) (u : End (X ⊗ Y)) :
    scalar (p.rightTrace (overlapEndProduct A X Y v u).asHom) =
      scalar (p.rightTrace v.asHom) *
        (scalar (p.rightTrace u.asHom) / scalar (p.rightTrace (𝟙 X))) := by
  rw [← Dimensions.rightTrace_partialTrace p (A ⊗ X) Y (overlapEndProduct A X Y v u)]
  rw [rightPartialTrace_overlap C A X Y p scalar v u]
  simp [Dimensions.PivotalStructure.rightTrace_smul, mul_comm]

end PropertyF.Ground.Calculus
