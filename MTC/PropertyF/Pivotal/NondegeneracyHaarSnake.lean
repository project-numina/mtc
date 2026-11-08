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

set_option backward.isDefEq.respectTransparency false in
/-- Move the outer pivotal component across the second cup and an arbitrary
inner box in a closed two-strand diagram. -/
theorem haar_pivotal_closed_slide (X Y : C.Obj)
    (a : (Yᘁ) ⊗ (X ⊗ (Xᘁ)) ⟶ (Yᘁ) ⊗ (X ⊗ (Xᘁ))) :
    η_ Y (Yᘁ) ⊗≫ ((p.iso Y).hom ▷ (Yᘁ)) ⊗≫
      ((((Yᘁ)ᘁ) ⊗ (Yᘁ)) ◁ η_ X (Xᘁ)) ⊗≫ (((Yᘁ)ᘁ) ◁ a) ⊗≫
      (ε_ (Yᘁ) ((Yᘁ)ᘁ) ▷ (X ⊗ (Xᘁ))) ⊗≫
      ((p.iso X).hom ▷ (Xᘁ)) ⊗≫ ε_ (Xᘁ) ((Xᘁ)ᘁ) =
    η_ Y (Yᘁ) ⊗≫ ((Y ⊗ (Yᘁ)) ◁ η_ X (Xᘁ)) ⊗≫ (Y ◁ a) ⊗≫
      (((p.iso Y).hom ▷ (Yᘁ)) ▷ (X ⊗ (Xᘁ))) ⊗≫
      (ε_ (Yᘁ) ((Yᘁ)ᘁ) ▷ (X ⊗ (Xᘁ))) ⊗≫
      ((p.iso X).hom ▷ (Xᘁ)) ⊗≫ ε_ (Xᘁ) ((Xᘁ)ᘁ) := by
  monoidal <;> simp
  have hc : (p.iso Y).hom ▷ (Yᘁ) ≫ (ρ_ (((Yᘁ)ᘁ) ⊗ (Yᘁ))).inv ≫
      (α_ ((Yᘁ)ᘁ) (Yᘁ) (𝟙_ C.Obj)).hom ≫ (((Yᘁ)ᘁ) ◁ (Yᘁ) ◁ η_ X (Xᘁ)) =
      (ρ_ (Y ⊗ (Yᘁ))).inv ≫ (α_ Y (Yᘁ) (𝟙_ C.Obj)).hom ≫
        (Y ◁ (Yᘁ) ◁ η_ X (Xᘁ)) ≫
          ((p.iso Y).hom ▷ ((Yᘁ) ⊗ (X ⊗ (Xᘁ)))) := by
    rw [rightUnitor_inv_naturality_assoc, associator_naturality_left_assoc,
      ← whisker_exchange]
  slice_lhs 1 4 => rw [hc]
  simp only [Category.assoc]
  rw [← whisker_exchange_assoc, associator_inv_naturality_left_assoc,
    associator_inv_naturality_left_assoc]

set_option backward.isDefEq.respectTransparency false in
theorem haar_pivotal_cap_exchange (X Y : C.Obj) :
    ((((Yᘁ : C.Obj)ᘁ) ⊗ (Yᘁ : C.Obj)) ◁ ((p.iso X).hom ▷ (Xᘁ : C.Obj) ≫ ε_ (Xᘁ : C.Obj) ((Xᘁ : C.Obj)ᘁ))) ⊗≫
      ε_ (Yᘁ : C.Obj) ((Yᘁ : C.Obj)ᘁ) =
    (ε_ (Yᘁ : C.Obj) ((Yᘁ : C.Obj)ᘁ) ▷ (X ⊗ (Xᘁ : C.Obj))) ⊗≫
      ((p.iso X).hom ▷ (Xᘁ : C.Obj)) ⊗≫ ε_ (Xᘁ : C.Obj) ((Xᘁ : C.Obj)ᘁ) := by
  calc
    _ = 𝟙 ((((Yᘁ : C.Obj)ᘁ) ⊗ (Yᘁ : C.Obj)) ⊗ (X ⊗ (Xᘁ : C.Obj))) ⊗≫ (((((Yᘁ : C.Obj)ᘁ) ⊗ (Yᘁ : C.Obj)) ◁
        ((p.iso X).hom ▷ (Xᘁ : C.Obj) ≫ ε_ (Xᘁ : C.Obj) ((Xᘁ : C.Obj)ᘁ))) ≫
        (ε_ (Yᘁ : C.Obj) ((Yᘁ : C.Obj)ᘁ) ▷ (𝟙_ C.Obj))) ⊗≫ 𝟙 (𝟙_ C.Obj) := by monoidal
    _ = 𝟙 ((((Yᘁ : C.Obj)ᘁ) ⊗ (Yᘁ : C.Obj)) ⊗ (X ⊗ (Xᘁ : C.Obj))) ⊗≫ ((ε_ (Yᘁ : C.Obj) ((Yᘁ : C.Obj)ᘁ) ▷ (X ⊗ (Xᘁ : C.Obj))) ≫
        ((𝟙_ C.Obj) ◁ ((p.iso X).hom ▷ (Xᘁ : C.Obj) ≫ ε_ (Xᘁ : C.Obj) ((Xᘁ : C.Obj)ᘁ)))) ⊗≫ 𝟙 (𝟙_ C.Obj) := by
          rw [whisker_exchange]
    _ = _ := by monoidal

set_option backward.isDefEq.respectTransparency false in
/-- Rotate the composite of the actual two Frobenius mates into a boxed
fusion endomorphism surrounded by two pivotal cups and caps. -/
theorem haar_mate_trace_boxed (X Y U : C.Obj) (f : X ⟶ Y ⊗ U) (g : Y ⊗ U ⟶ X) :
    let a : (Yᘁ) ⊗ (X ⊗ (Xᘁ)) ⟶ (Yᘁ) ⊗ (X ⊗ (Xᘁ)) :=
      𝟙 _ ⊗≫ ((Yᘁ) ◁ (f ▷ Xᘁ)) ⊗≫ (ε_ Y (Yᘁ) ▷ (U ⊗ Xᘁ)) ⊗≫
       ((η_ (Yᘁ) ((Yᘁ)ᘁ) ≫ (Yᘁ) ◁ (p.iso Y).inv) ▷ (U ⊗ Xᘁ)) ⊗≫
       ((Yᘁ) ◁ (g ▷ Xᘁ)) ⊗≫ 𝟙 _
    p.leftTrace (haarInclusionMate C X Y U f ≫ haarProjectionMate C p X Y U g) =
      End.of (η_ Y (Yᘁ) ⊗≫ ((p.iso Y).hom ▷ (Yᘁ)) ⊗≫
      ((((Yᘁ)ᘁ) ⊗ (Yᘁ)) ◁ η_ X (Xᘁ)) ⊗≫ (((Yᘁ)ᘁ) ◁ a) ⊗≫
      (ε_ (Yᘁ) ((Yᘁ)ᘁ) ▷ (X ⊗ (Xᘁ))) ⊗≫
      ((p.iso X).hom ▷ (Xᘁ)) ⊗≫ ε_ (Xᘁ) ((Xᘁ)ᘁ)) := by
  dsimp only
  rw [haarInclusionMate_diagram, haarProjectionMate_diagram]
  apply End.ext
  simp only [PivotalStructure.leftTrace]
  monoidal <;> simp
  slice_lhs 1 2 => rw [pivotalDual_coevaluation_rotate C p Y]
  have hc : (((Yᘁ)ᘁ) ◁ (Yᘁ) ◁ ((p.iso X).hom ▷ (Xᘁ))) ≫
      (((Yᘁ)ᘁ) ◁ (Yᘁ) ◁ ε_ (Xᘁ) ((Xᘁ)ᘁ)) ≫
      (α_ ((Yᘁ)ᘁ) (Yᘁ) (𝟙_ C.Obj)).inv ≫ (ρ_ (((Yᘁ)ᘁ) ⊗ (Yᘁ))).hom ≫
      ε_ (Yᘁ) ((Yᘁ)ᘁ) =
      (α_ ((Yᘁ)ᘁ) (Yᘁ) (X ⊗ (Xᘁ))).inv ≫
      (α_ (((Yᘁ)ᘁ) ⊗ (Yᘁ)) X (Xᘁ)).inv ≫
      (ε_ (Yᘁ) ((Yᘁ)ᘁ) ▷ X ▷ (Xᘁ)) ≫ (α_ (𝟙_ C.Obj) X (Xᘁ)).hom ≫
      (λ_ (X ⊗ (Xᘁ))).hom ≫ (p.iso X).hom ▷ (Xᘁ) ≫ ε_ (Xᘁ) ((Xᘁ)ᘁ) := by
    have hh := congrArg (fun t ↦ (α_ ((Yᘁ)ᘁ) (Yᘁ) (X ⊗ (Xᘁ))).inv ≫ t)
      (haar_pivotal_cap_exchange C p X Y)
    convert hh using 1 <;> monoidal
  simp only [Category.assoc]
  rw [hc]

set_option backward.isDefEq.respectTransparency false in
/-- The other boxed closure is the right trace, by both boxed snakes and cup exchange. -/
theorem haar_right_trace_boxed (X Y U : C.Obj) (f : X ⟶ Y ⊗ U) (g : Y ⊗ U ⟶ X) :
    let a : (Yᘁ) ⊗ (X ⊗ (Xᘁ)) ⟶ (Yᘁ) ⊗ (X ⊗ (Xᘁ)) :=
      𝟙 _ ⊗≫ ((Yᘁ) ◁ (f ▷ Xᘁ)) ⊗≫ (ε_ Y (Yᘁ) ▷ (U ⊗ Xᘁ)) ⊗≫
       ((η_ (Yᘁ) ((Yᘁ)ᘁ) ≫ (Yᘁ) ◁ (p.iso Y).inv) ▷ (U ⊗ Xᘁ)) ⊗≫
       ((Yᘁ) ◁ (g ▷ Xᘁ)) ⊗≫ 𝟙 _
    End.of (η_ Y (Yᘁ) ⊗≫ ((Y ⊗ (Yᘁ)) ◁ η_ X (Xᘁ)) ⊗≫ (Y ◁ a) ⊗≫
      (((p.iso Y).hom ▷ (Yᘁ)) ▷ (X ⊗ (Xᘁ))) ⊗≫
      (ε_ (Yᘁ) ((Yᘁ)ᘁ) ▷ (X ⊗ (Xᘁ))) ⊗≫
      ((p.iso X).hom ▷ (Xᘁ)) ⊗≫ ε_ (Xᘁ) ((Xᘁ)ᘁ)) =
      p.rightTrace (f ≫ g) := by
  dsimp only
  conv_rhs => rw [← haar_yank_inclusion C X Y U f, ← haar_yank_projection C p X Y U g]
  apply End.ext
  simp only [PivotalStructure.rightTrace, rightTraceWith]
  monoidal <;> simp
  have hc : η_ Y (Yᘁ) ≫ (ρ_ (Y ⊗ (Yᘁ))).inv ≫
      (α_ Y (Yᘁ) (𝟙_ C.Obj)).hom ≫ Y ◁ (Yᘁ) ◁ η_ X (Xᘁ) =
      η_ X (Xᘁ) ≫ (λ_ (X ⊗ (Xᘁ))).inv ≫ (α_ (𝟙_ C.Obj) X (Xᘁ)).inv ≫
      (η_ Y (Yᘁ) ▷ X ▷ (Xᘁ)) ≫ (α_ (Y ⊗ (Yᘁ)) X (Xᘁ)).hom ≫
      (α_ Y (Yᘁ) (X ⊗ (Xᘁ))).hom := by
    have hh := congrArg (fun t ↦ t ≫ (α_ Y (Yᘁ) (X ⊗ (Xᘁ))).hom)
      (haar_coevaluation_exchange C X Y)
    convert hh.symm using 1 <;> monoidal
  slice_lhs 1 4 => rw [hc]
  simp only [Category.assoc]
  have h₁ : (Yᘁ) ◁ (α_ Y U (Xᘁ)).hom ≫ (α_ (Yᘁ) Y (U ⊗ (Xᘁ))).inv ≫
      (α_ ((Yᘁ) ⊗ Y) U (Xᘁ)).inv =
      (α_ (Yᘁ) (Y ⊗ U) (Xᘁ)).inv ≫ (α_ (Yᘁ) Y U).inv ▷ (Xᘁ) := by monoidal
  have h₂ : (α_ (Yᘁ) (Y ⊗ U) (Xᘁ)).inv ≫ (α_ (Yᘁ) Y U).inv ▷ (Xᘁ) ≫
      (α_ ((Yᘁ) ⊗ Y) U (Xᘁ)).hom ≫ (α_ (Yᘁ) Y (U ⊗ (Xᘁ))).hom ≫
      (Yᘁ) ◁ (α_ Y U (Xᘁ)).inv = 𝟙 _ := by monoidal
  simp only [← whiskerLeft_comp_assoc]
  conv_lhs =>
    pattern (Yᘁ ◁ (f ▷ Xᘁ ≫ (α_ Y U (Xᘁ)).hom))
    rw [whiskerLeft_comp]
  simp only [Category.assoc, reassoc_of% h₁, reassoc_of% h₂, Category.id_comp]

/-- The two Frobenius mates preserve the pivotal trace pairing. -/
theorem haarMate_trace_pairing (X Y U : C.Obj) (f : X ⟶ Y ⊗ U) (g : Y ⊗ U ⟶ X) :
    p.leftTrace (haarInclusionMate C X Y U f ≫ haarProjectionMate C p X Y U g) =
      p.rightTrace (f ≫ g) := by
  rw [haar_mate_trace_boxed C p X Y U f g]
  rw [haar_pivotal_closed_slide C p X Y]
  exact haar_right_trace_boxed C p X Y U f g

/-- Mating the normalized fusion basis preserves its pivotal trace duality. -/
theorem haar_mated_trace_dual_basis (Y U : C.Obj) (i : Fin (rank C))
    (a b : Fin (Module.finrank ℂ (simples C i ⟶ Y ⊗ U))) :
    unitScalar C (p.leftTrace
      (haarInclusionMate C (simples C i) Y U (simpleInclusion C (Y ⊗ U) i a) ≫
       haarProjectionMate C p (simples C i) Y U (pivotalTraceDualProjection C p (Y ⊗ U) i b))) =
      if a = b then 1 else 0 := by
  rw [haarMate_trace_pairing]
  exact pivotalTrace_dual_basis C p (Y ⊗ U) i a b

end MTC.PropertyF.Pivotal
end
