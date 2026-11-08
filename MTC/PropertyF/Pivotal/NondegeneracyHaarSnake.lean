module
public import MTC.PropertyF.Pivotal.NondegeneracyHaarMate

open MTC.Fusion MTC.Modular MTC.CategoryTheory.Dimensions MTC.Center.Induction MTC.Center.Trace
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
namespace MTC.PropertyF.Pivotal
universe v u
variable (C : BraidedFusionCategory.{v,u}) (p : PivotalStructure (C := C.Obj))

/-- First snake for the pivotal left dual, written with the actual pivotal
coevaluation and evaluation maps. -/
theorem pivotalLeftPairing_snake_right (X : C.Obj) :
    X ◁ (η_ (Xᘁ) ((Xᘁ)ᘁ) ≫ (Xᘁ) ◁ (p.iso X).inv) ≫
      (α_ X (Xᘁ) X).inv ≫
        (((p.iso X).hom ▷ (Xᘁ : C.Obj)) ≫ ε_ (Xᘁ) ((Xᘁ)ᘁ)) ▷ X =
          (ρ_ X).hom ≫ (λ_ X).inv := by
  let : ExactPairing (Xᘁ) X := pivotalLeftPairing C p X
  simpa only [pivotalLeftPairing_coevaluation, pivotalLeftPairing_evaluation] using
    (ExactPairing.coevaluation_evaluation (Xᘁ) X)

/-- Second snake for the pivotal left dual, in the same actual structure. -/
theorem pivotalLeftPairing_snake_left (X : C.Obj) :
    (η_ (Xᘁ) ((Xᘁ)ᘁ) ≫ (Xᘁ) ◁ (p.iso X).inv) ▷ (Xᘁ) ≫
      (α_ (Xᘁ : C.Obj) X (Xᘁ : C.Obj)).hom ≫
        (Xᘁ) ◁ (((p.iso X).hom ▷ (Xᘁ : C.Obj)) ≫ ε_ (Xᘁ) ((Xᘁ)ᘁ)) =
          (λ_ (Xᘁ)).hom ≫ (ρ_ (Xᘁ : C.Obj)).inv := by
  let : ExactPairing (Xᘁ) X := pivotalLeftPairing C p X
  simpa only [pivotalLeftPairing_coevaluation, pivotalLeftPairing_evaluation] using
    (ExactPairing.evaluation_coevaluation (Xᘁ) X)

/-- The first pivotal snake, with unitors closed, is the identity. -/
theorem pivotalLeftPairing_snake_right_id (X : C.Obj) :
    (ρ_ X).inv ≫
      (X ◁ (η_ (Xᘁ) ((Xᘁ)ᘁ) ≫ (Xᘁ) ◁ (p.iso X).inv)) ≫
      (α_ X (Xᘁ) X).inv ≫
      (((p.iso X).hom ▷ (Xᘁ : C.Obj) ≫ ε_ (Xᘁ : C.Obj) ((Xᘁ)ᘁ)) ▷ X) ≫
      (λ_ X).hom = 𝟙 X := by
  have h := congrArg (fun t ↦ (ρ_ X).inv ≫ t ≫ (λ_ X).hom)
    (pivotalLeftPairing_snake_right C p X)
  simpa only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id] using h

/-- The second pivotal snake, with unitors closed, is the identity. -/
theorem pivotalLeftPairing_snake_left_id (X : C.Obj) :
    (λ_ (Xᘁ : C.Obj)).inv ≫
      ((η_ (Xᘁ) ((Xᘁ)ᘁ) ≫ (Xᘁ) ◁ (p.iso X).inv) ▷ (Xᘁ : C.Obj)) ≫
      (α_ (Xᘁ : C.Obj) X (Xᘁ : C.Obj)).hom ≫
      ((Xᘁ : C.Obj) ◁ ((p.iso X).hom ▷ (Xᘁ : C.Obj) ≫ ε_ (Xᘁ : C.Obj) ((Xᘁ)ᘁ))) ≫
      (ρ_ (Xᘁ : C.Obj)).hom = 𝟙 (Xᘁ : C.Obj) := by
  have h := congrArg (fun t ↦ (λ_ (Xᘁ : C.Obj)).inv ≫ t ≫ (ρ_ (Xᘁ : C.Obj)).hom)
    (pivotalLeftPairing_snake_left C p X)
  simpa only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id] using h

/-- The first pivotal snake also cancels with an arbitrary spectator strand. -/
theorem pivotalLeftPairing_snake_right_whisker (X Z : C.Obj) :
    ((ρ_ X).inv ▷ Z) ≫
      ((X ◁ (η_ (Xᘁ) ((Xᘁ)ᘁ) ≫ (Xᘁ) ◁ (p.iso X).inv)) ▷ Z) ≫
      ((α_ X (Xᘁ) X).inv ▷ Z) ≫
      ((((p.iso X).hom ▷ (Xᘁ : C.Obj) ≫ ε_ (Xᘁ : C.Obj) ((Xᘁ)ᘁ)) ▷ X) ▷ Z) ≫
      ((λ_ X).hom ▷ Z) = 𝟙 (X ⊗ Z) := by
  simpa only [comp_whiskerRight, id_whiskerRight] using
    congrArg (fun f ↦ f ▷ Z) (pivotalLeftPairing_snake_right_id C p X)

/-- The second pivotal snake also cancels with an arbitrary spectator strand. -/
theorem pivotalLeftPairing_snake_left_whisker (X Z : C.Obj) :
    ((λ_ (Xᘁ : C.Obj)).inv ▷ Z) ≫
      (((η_ (Xᘁ) ((Xᘁ)ᘁ) ≫ (Xᘁ) ◁ (p.iso X).inv) ▷ (Xᘁ : C.Obj)) ▷ Z) ≫
      ((α_ (Xᘁ : C.Obj) X (Xᘁ : C.Obj)).hom ▷ Z) ≫
      (((Xᘁ : C.Obj) ◁ ((p.iso X).hom ▷ (Xᘁ : C.Obj) ≫ ε_ (Xᘁ : C.Obj) ((Xᘁ)ᘁ))) ▷ Z) ≫
      ((ρ_ (Xᘁ : C.Obj)).hom ▷ Z) = 𝟙 ((Xᘁ : C.Obj) ⊗ Z) := by
  simpa only [comp_whiskerRight, id_whiskerRight] using
    congrArg (fun f ↦ f ▷ Z) (pivotalLeftPairing_snake_left_id C p X)

set_option backward.isDefEq.respectTransparency false in
/-- The inclusion Frobenius mate is the standard cup, fusion morphism,
and cap diagram, with all coherence maps supplied canonically. -/
theorem haarInclusionMate_diagram (X Y U : C.Obj) (f : X ⟶ Y ⊗ U) :
    haarInclusionMate C X Y U f =
      𝟙 (Yᘁ : C.Obj) ⊗≫ ((Yᘁ) ◁ η_ X (Xᘁ)) ⊗≫
        ((Yᘁ) ◁ (f ▷ (Xᘁ))) ⊗≫ (ε_ Y (Yᘁ) ▷ (U ⊗ (Xᘁ))) ⊗≫ 𝟙 _ := by
  dsimp [haarInclusionMate, tensorLeftHomLinearEquiv, tensorRightHomLinearEquiv,
    tensorLeftHomEquiv, tensorRightHomEquiv]
  monoidal

set_option backward.isDefEq.respectTransparency false in
/-- The projection Frobenius mate is the analogous diagram with the actual
pivotal left-dual cup and cap. -/
theorem haarProjectionMate_diagram (X Y U : C.Obj) (g : Y ⊗ U ⟶ X) :
    haarProjectionMate C p X Y U g =
      𝟙 (U ⊗ (Xᘁ)) ⊗≫
        ((η_ (Yᘁ) ((Yᘁ)ᘁ) ≫ (Yᘁ) ◁ (p.iso Y).inv) ▷ (U ⊗ (Xᘁ))) ⊗≫
        ((Yᘁ) ◁ (g ▷ (Xᘁ))) ⊗≫
        ((Yᘁ) ◁ ((p.iso X).hom ▷ (Xᘁ) ≫ ε_ (Xᘁ) ((Xᘁ)ᘁ))) ⊗≫ 𝟙 _ := by
  dsimp [haarProjectionMate, tensorLeftHomLinearEquiv, tensorRightHomLinearEquiv,
    tensorLeftHomEquiv, tensorRightHomEquiv]
  rw [pivotalLeftPairing_coevaluation C p Y, pivotalLeftPairing_evaluation C p X]
  monoidal

end MTC.PropertyF.Pivotal
end
