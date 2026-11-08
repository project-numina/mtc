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

/-- Uncurry the inclusion mate to recover its first Frobenius transpose.
This is the first exact-pairing snake before expanding any coherence maps. -/
theorem haarInclusionMate_uncurry (X Y U : C.Obj) (f : X ⟶ Y ⊗ U) :
    (tensorRightHomLinearEquiv (k := ℂ) (Yᘁ) X (Xᘁ) U).symm
      (haarInclusionMate C X Y U f) =
        (tensorLeftHomLinearEquiv (k := ℂ) X Y (Yᘁ) U).symm f := by
  simp [haarInclusionMate]

/-- Curry the projection mate to recover the pivotal left-dual transpose.
This is the second exact-pairing snake in the mate construction. -/
theorem haarProjectionMate_curry (X Y U : C.Obj) (g : Y ⊗ U ⟶ X) :
    let : ExactPairing (Yᘁ) Y := pivotalLeftPairing C p Y
    letI : ExactPairing (Xᘁ) X := pivotalLeftPairing C p X
    tensorRightHomLinearEquiv (k := ℂ) U (Xᘁ) X (Yᘁ)
      (haarProjectionMate C p X Y U g) =
        tensorLeftHomLinearEquiv (k := ℂ) U (Yᘁ) Y X g := by
  simp [haarProjectionMate]

set_option backward.isDefEq.respectTransparency false in
/-- A fusion morphism passes through a coevaluation/evaluation pair; this is
the first boxed snake needed to regroup the Haar trace diagram. -/
theorem haar_yank_inclusion (X Y U : C.Obj) (f : X ⟶ Y ⊗ U) :
    𝟙 X ⊗≫ (η_ Y (Yᘁ) ▷ X) ⊗≫
      (Y ◁ (𝟙 ((Yᘁ) ⊗ X) ⊗≫ ((Yᘁ) ◁ f) ⊗≫
        (ε_ Y (Yᘁ) ▷ U) ⊗≫ 𝟙 U)) ⊗≫ 𝟙 (Y ⊗ U) = f := by
  have h := (tensorLeftHomEquiv X Y (Yᘁ) U).apply_symm_apply f
  dsimp [tensorLeftHomEquiv] at h
  convert h using 1; monoidal

set_option backward.isDefEq.respectTransparency false in
/-- A projection passes through the transported pivotal cup and cap; this is
the second boxed snake needed for the Haar trace contraction. -/
theorem haar_yank_projection (X Y U : C.Obj) (g : Y ⊗ U ⟶ X) :
    𝟙 (Y ⊗ U) ⊗≫
      (Y ◁ (𝟙 U ⊗≫
        ((η_ (Yᘁ) ((Yᘁ)ᘁ) ≫ (Yᘁ) ◁ (p.iso Y).inv) ▷ U) ⊗≫
        ((Yᘁ) ◁ g) ⊗≫ 𝟙 ((Yᘁ) ⊗ X))) ⊗≫
      (((p.iso Y).hom ▷ (Yᘁ) ≫ ε_ (Yᘁ) ((Yᘁ)ᘁ)) ▷ X) ⊗≫ 𝟙 X = g := by
  let : ExactPairing (Yᘁ) Y := pivotalLeftPairing C p Y
  have h := (tensorLeftHomEquiv U (Yᘁ) Y X).symm_apply_apply g
  dsimp [tensorLeftHomEquiv] at h
  rw [pivotalLeftPairing_coevaluation C p Y, pivotalLeftPairing_evaluation C p Y] at h
  convert h using 1; monoidal

set_option backward.isDefEq.respectTransparency false in
/-- Two independent duality cups exchange without changing their pairing.
This is the first interchange used to bring the two Haar snakes together. -/
theorem haar_coevaluation_exchange (X Y : C.Obj) :
    η_ X (Xᘁ) ⊗≫ (η_ Y (Yᘁ) ▷ (X ⊗ (Xᘁ))) =
      η_ Y (Yᘁ) ⊗≫ ((Y ⊗ (Yᘁ)) ◁ η_ X (Xᘁ)) := by
  calc
    _ = 𝟙 (𝟙_ C.Obj) ⊗≫
        ((𝟙_ C.Obj ◁ η_ X (Xᘁ)) ≫ (η_ Y (Yᘁ) ▷ (X ⊗ (Xᘁ)))) ⊗≫ 𝟙 _ := by
          monoidal
    _ = 𝟙 (𝟙_ C.Obj) ⊗≫
        ((η_ Y (Yᘁ) ▷ (𝟙_ C.Obj)) ≫ ((Y ⊗ (Yᘁ)) ◁ η_ X (Xᘁ))) ⊗≫ 𝟙 _ := by
          rw [← whisker_exchange]
    _ = _ := by monoidal

/-- A pivotal component slides past any morphism on an independent strand. -/
theorem pivotalComponent_whisker_exchange (Y A B : C.Obj) (h : A ⟶ B) :
    ((p.iso Y).hom ▷ A) ≫ (((Yᘁ)ᘁ) ◁ h) =
      (Y ◁ h) ≫ ((p.iso Y).hom ▷ B) := by
  exact (whisker_exchange (p.iso Y).hom h).symm

set_option backward.isDefEq.respectTransparency false in
/-- Two independent duality caps exchange. This supplies the final planar
interchange in the two-mate trace rotation. -/
theorem haar_evaluation_exchange (X Y : C.Obj) :
    (((Yᘁ : C.Obj) ⊗ Y) ◁ ε_ X (Xᘁ)) ⊗≫ ε_ Y (Yᘁ) =
      (ε_ Y (Yᘁ) ▷ ((Xᘁ : C.Obj) ⊗ X)) ⊗≫ ε_ X (Xᘁ) := by
  calc
    _ = 𝟙 (((Yᘁ : C.Obj) ⊗ Y) ⊗ ((Xᘁ : C.Obj) ⊗ X)) ⊗≫ ((((Yᘁ : C.Obj) ⊗ Y) ◁ ε_ X (Xᘁ)) ≫ (ε_ Y (Yᘁ) ▷ (𝟙_ C.Obj))) ⊗≫
        𝟙 (𝟙_ C.Obj) := by monoidal
    _ = 𝟙 (((Yᘁ : C.Obj) ⊗ Y) ⊗ ((Xᘁ : C.Obj) ⊗ X)) ⊗≫ ((ε_ Y (Yᘁ) ▷ ((Xᘁ : C.Obj) ⊗ X)) ≫ ((𝟙_ C.Obj) ◁ ε_ X (Xᘁ))) ⊗≫
        𝟙 (𝟙_ C.Obj) := by rw [whisker_exchange]
    _ = _ := by monoidal

set_option backward.isDefEq.respectTransparency false in
/-- A pivotal component can be moved through an arbitrary boxed morphism
on an independent strand, in the association used by the Haar proof. -/
theorem haar_pivotal_box_exchange (Y W : C.Obj) (a : (Yᘁ) ⊗ W ⟶ (Yᘁ) ⊗ W) :
    (((p.iso Y).hom ▷ (Yᘁ)) ▷ W) ⊗≫ (((Yᘁ)ᘁ) ◁ a) =
      𝟙 ((Y ⊗ (Yᘁ)) ⊗ W) ⊗≫ (Y ◁ a) ⊗≫
        (((p.iso Y).hom ▷ (Yᘁ)) ▷ W) ⊗≫ 𝟙 (((Yᘁ)ᘁ) ⊗ ((Yᘁ) ⊗ W)) := by
  simp only [monoidalComp, Category.id_comp, Category.comp_id]
  monoidal; simp
  rw [associator_naturality_left_assoc, ← associator_inv_naturality_left_assoc]
  simp only [Iso.inv_hom_id, Category.comp_id]
  rw [← whisker_exchange]

set_option backward.isDefEq.respectTransparency false in
/-- A pivotal component slides past the other duality cup in the association
used by the two-mate trace diagram. -/
theorem haar_pivotal_cup_exchange (X Y : C.Obj) :
    ((p.iso Y).hom ▷ (Yᘁ)) ⊗≫ ((((Yᘁ)ᘁ) ⊗ (Yᘁ)) ◁ η_ X (Xᘁ)) =
      𝟙 (Y ⊗ (Yᘁ)) ⊗≫ ((Y ⊗ (Yᘁ)) ◁ η_ X (Xᘁ)) ⊗≫
        (((p.iso Y).hom ▷ (Yᘁ)) ▷ (X ⊗ (Xᘁ))) ⊗≫
          𝟙 (((Yᘁ)ᘁ ⊗ (Yᘁ)) ⊗ (X ⊗ (Xᘁ))) := by
  calc
    _ = 𝟙 _ ⊗≫ (((p.iso Y).hom ▷ (Yᘁ)) ▷ (𝟙_ C.Obj) ≫
        ((((Yᘁ)ᘁ) ⊗ (Yᘁ)) ◁ η_ X (Xᘁ))) ⊗≫ 𝟙 _ := by monoidal
    _ = 𝟙 _ ⊗≫ (((Y ⊗ (Yᘁ)) ◁ η_ X (Xᘁ)) ≫
        (((p.iso Y).hom ▷ (Yᘁ)) ▷ (X ⊗ (Xᘁ)))) ⊗≫ 𝟙 _ := by
          rw [whisker_exchange]
    _ = _ := by monoidal

end MTC.PropertyF.Pivotal
end
