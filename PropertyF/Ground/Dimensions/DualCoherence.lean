module
public import PropertyF.Ground.Dimensions.Pivotal

/-! # Duality coherence

Evaluation and coevaluation identities relate changes of duals and the associated traces.

## Main results

* `rightDualIso_evaluation`: describes the canonical isomorphism between two right duals through evaluation.
* `unitDoubleDual_trace`: computes the trace of the unit double-dual isomorphism.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.Dimensions
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

set_option backward.isDefEq.respectTransparency false in
/-- Coevaluation is transported by an isomorphism and its inverse right dual. -/
theorem coevaluation_iso_map {C : Type u} [Category.{v} C] [MonoidalCategory C]
    [RightRigidCategory C] {X Y : C} (a : X ≅ Y) :
    η_ X (Xᘁ) ≫ (a.hom ⊗ₘ (a.invᘁ)) = η_ Y (Yᘁ) := by
  rw [tensorHom_def, ← whisker_exchange, ← Category.assoc,
    coevaluation_comp_rightAdjointMate, Category.assoc, ← comp_whiskerRight,
    Iso.inv_hom_id, id_whiskerRight, Category.comp_id]


section
variable {X Y Z : C}

/-- The canonical isomorphism between two right duals transports coevaluation. -/
@[reassoc]
theorem coevaluation_rightDualIso (p : ExactPairing X Y) (q : ExactPairing X Z) :
    @ExactPairing.coevaluation C _ _ X Y p ≫ X ◁ (rightDualIso p q).hom =
      @ExactPairing.coevaluation C _ _ X Z q := by
  let hp : HasRightDual X := { rightDual := Y, exact := p }
  let hq : HasRightDual X := { rightDual := Z, exact := q }
  simpa only [id_whiskerRight, Category.comp_id] using
    (show (@ExactPairing.coevaluation C _ _ X Y p ≫ X ◁ (rightDualIso p q).hom) =
      (@ExactPairing.coevaluation C _ _ X Z q ≫ (𝟙 X) ▷ Z) from
        @coevaluation_comp_rightAdjointMate C _ _ X X hq hp (𝟙 X))

/-- The canonical isomorphism between two right duals transports evaluation. -/
theorem rightDualIso_evaluation (p : ExactPairing X Y) (q : ExactPairing X Z) :
    (rightDualIso p q).hom ▷ X ≫ @ExactPairing.evaluation C _ _ X Z q =
      @ExactPairing.evaluation C _ _ X Y p := by
  let hp : HasRightDual X := { rightDual := Y, exact := p }
  let hq : HasRightDual X := { rightDual := Z, exact := q }
  simpa only [whiskerLeft_id, Category.id_comp] using
    (show (rightDualIso p q).hom ▷ X ≫ @ExactPairing.evaluation C _ _ X Z q =
      Y ◁ (𝟙 X) ≫ @ExactPairing.evaluation C _ _ X Y p from
        @rightAdjointMate_comp_evaluation C _ _ X X hq hp (𝟙 X))

/-- Evaluation is preserved by the canonical tensor comparison for right duals. -/
theorem rightDualTensorIso_evaluation [RightRigidCategory C] (X Y : C) :
    (rightDualTensorIso X Y).hom ▷ (X ⊗ Y) ≫ ε_ (X ⊗ Y) ((Yᘁ) ⊗ (Xᘁ)) =
      ε_ (X ⊗ Y) ((X ⊗ Y)ᘁ) :=
  rightDualIso_evaluation
    (@HasRightDual.exact C _ _ (X ⊗ Y) (RightRigidCategory.rightDual _))
    (ExactPairing.tensor (X₁ := X) (X₂ := Y) (Y₁ := Xᘁ) (Y₂ := Yᘁ))

set_option backward.isDefEq.respectTransparency false in
/-- Evaluation of tensor pairings respects a change of the first dual. -/
theorem tensorPairing_evaluation_whiskerLeft {A B U V W : C} [p : ExactPairing A U]
    [q : ExactPairing A V] [r : ExactPairing B W] (f : U ⟶ V)
    (hf : f ▷ A ≫ ε_ A V = ε_ A U) :
    (W ◁ f) ▷ (A ⊗ B) ≫ ε_ (A ⊗ B) (W ⊗ V) = ε_ (A ⊗ B) (W ⊗ U) := by
  rw [@ExactPairing.tensor_evaluation C _ _ A B V W q r,
    @ExactPairing.tensor_evaluation C _ _ A B U W p r]
  calc
    _ = 𝟙 _ ⊗≫ (W : C) ◁ ((f ▷ A ≫ ε_ A V) ▷ B) ⊗≫ ε_ B W := by
      simp only [comp_whiskerRight, whiskerLeft_comp]
      monoidal
    _ = _ := by rw [hf]

set_option backward.isDefEq.respectTransparency false in
/-- Evaluation of tensor pairings respects a change of the second dual. -/
theorem tensorPairing_evaluation_whiskerRight {A B U V W : C} [p : ExactPairing A U]
    [q : ExactPairing B V] [r : ExactPairing B W] (f : V ⟶ W)
    (hf : f ▷ B ≫ ε_ B W = ε_ B V) :
    (f ▷ U) ▷ (A ⊗ B) ≫ ε_ (A ⊗ B) (W ⊗ U) = ε_ (A ⊗ B) (V ⊗ U) := by
  rw [@ExactPairing.tensor_evaluation C _ _ A B U W p r,
    @ExactPairing.tensor_evaluation C _ _ A B U V p q]
  calc
    _ = 𝟙 _ ⊗≫ ((f ▷ ((U ⊗ A) ⊗ B)) ≫ (W : C) ◁ (ε_ A U ▷ B)) ⊗≫ ε_ B W := by monoidal
    _ = 𝟙 _ ⊗≫ ((V : C) ◁ (ε_ A U ▷ B) ≫ f ▷ ((𝟙_ C) ⊗ B)) ⊗≫ ε_ B W := by
        rw [← whisker_exchange]
    _ = 𝟙 _ ⊗≫ (V : C) ◁ (ε_ A U ▷ B) ⊗≫ (f ▷ B ≫ ε_ B W) := by monoidal
    _ = _ := by rw [hf]

/-- The inverse dual comparison transports coevaluation in the reverse direction. -/
theorem coevaluation_rightDualIso_inv (p : ExactPairing X Y) (q : ExactPairing X Z) :
    @ExactPairing.coevaluation C _ _ X Z q ≫ X ◁ (rightDualIso p q).inv =
      @ExactPairing.coevaluation C _ _ X Y p :=
  coevaluation_rightDualIso q p

/-- The inverse dual comparison transports evaluation in the reverse direction. -/
theorem rightDualIso_inv_evaluation (p : ExactPairing X Y) (q : ExactPairing X Z) :
    (rightDualIso p q).inv ▷ X ≫ @ExactPairing.evaluation C _ _ X Y p =
      @ExactPairing.evaluation C _ _ X Z q :=
  rightDualIso_evaluation q p

/-- Closing a morphism does not change when its right dual is replaced by a
canonically isomorphic one and the morphism is transported by the dual map. -/
theorem trace_change_rightDual [RightRigidCategory C] {X Y Z : C}
    (p : ExactPairing X Y) (q : ExactPairing X Z) (u : X ⟶ Zᘁ) :
    @ExactPairing.coevaluation C _ _ X Y p ≫
      ((u ≫ ((rightDualIso p q).hom)ᘁ) ⊗ₘ 𝟙 Y) ≫ ε_ Y (Yᘁ) =
    @ExactPairing.coevaluation C _ _ X Z q ≫ (u ⊗ₘ 𝟙 Z) ≫ ε_ Z (Zᘁ) := by
  simp only [tensorHom_def, whiskerLeft_id, Category.comp_id, comp_whiskerRight, Category.assoc]
  rw [rightAdjointMate_comp_evaluation, ← whisker_exchange_assoc, coevaluation_rightDualIso_assoc]

end

set_option backward.isDefEq.respectTransparency false in
/-- The canonical double-dual unit isomorphism has unit evaluation trace. -/
theorem unitDoubleDual_trace [RightRigidCategory C] :
    letI : HasRightDual (𝟙_ C) := RightRigidCategory.rightDual _
    letI : HasRightDual ((𝟙_ C)ᘁ) := RightRigidCategory.rightDual _
    η_ (𝟙_ C) ((𝟙_ C)ᘁ) ≫
      ((doubleDualUnitIso (C := C)).hom ⊗ₘ 𝟙 ((𝟙_ C)ᘁ)) ≫
      ε_ ((𝟙_ C)ᘁ) (((𝟙_ C)ᘁ)ᘁ) = 𝟙 (𝟙_ C) := by
  let hp : ExactPairing (𝟙_ C) (rightDualObject (𝟙_ C)) :=
    @HasRightDual.exact C _ _ (𝟙_ C) (RightRigidCategory.rightDual (𝟙_ C))
  let hq : ExactPairing (𝟙_ C) (𝟙_ C) := exactPairingUnit
  let r := rightDualIso hp hq
  change @ExactPairing.coevaluation C _ _ (𝟙_ C) (rightDualObject (𝟙_ C)) hp ≫
    ((r.inv ≫ @rightAdjointMate C _ _ (rightDualObject (𝟙_ C)) (𝟙_ C)
      (RightRigidCategory.rightDual _) (RightRigidCategory.rightDual _) r.hom) ⊗ₘ
        𝟙 (rightDualObject (𝟙_ C))) ≫
      @ExactPairing.evaluation C _ _ (rightDualObject (𝟙_ C))
        (rightDualObject (rightDualObject (𝟙_ C)))
        (@HasRightDual.exact C _ _ _ (RightRigidCategory.rightDual _)) = 𝟙 (𝟙_ C)
  apply (trace_change_rightDual hp hq r.inv).trans
  simp only [tensorHom_def, whiskerLeft_id, Category.comp_id]
  change @ExactPairing.coevaluation C _ _ (𝟙_ C) (𝟙_ C) hq ≫
    ((rightDualIso hp hq).inv ▷ (𝟙_ C) ≫
      @ExactPairing.evaluation C _ _ (𝟙_ C) (rightDualObject (𝟙_ C)) hp) = 𝟙 (𝟙_ C)
  rw [rightDualIso_inv_evaluation hp hq]
  exact Iso.inv_hom_id _


set_option backward.isDefEq.respectTransparency false in
/-- The pivotal dimension of the tensor unit is one. -/
theorem rightTrace_unit [RightRigidCategory C] (p : PivotalStructure (C := C)) :
    p.rightTrace (𝟙 (𝟙_ C)) = 1 := by
  apply End.homEquiv.injective
  simpa only [PivotalStructure.rightTrace, End.homEquiv_apply, End.one_asHom,
    Category.id_comp, p.unit] using (unitDoubleDual_trace (C := C))

end PropertyF.Ground.Dimensions
