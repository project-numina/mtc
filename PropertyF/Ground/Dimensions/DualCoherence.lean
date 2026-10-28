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
theorem coevaluation_iso_map {X Y : C} [HasRightDual X] [HasRightDual Y] (a : X ≅ Y) :
    η_ X (Xᘁ) ≫ (a.hom ⊗ₘ (a.invᘁ)) = η_ Y (Yᘁ) := by
  rw [tensorHom_def, ← whisker_exchange, ← Category.assoc,
    coevaluation_comp_rightAdjointMate, Category.assoc, ← comp_whiskerRight,
    Iso.inv_hom_id, id_whiskerRight, Category.comp_id]

/-- Evaluation is preserved when an object and its chosen right dual are transported
along an isomorphism. -/
theorem evaluation_iso_map {X Y : C} [HasRightDual X] [HasRightDual Y] (a : X ≅ Y) :
    ((a.invᘁ) ⊗ₘ a.hom) ≫ ε_ Y (Yᘁ) = ε_ X (Xᘁ) := by
  simp [tensorHom_def', rightAdjointMate_comp_evaluation, ← whiskerLeft_comp_assoc]

set_option backward.isDefEq.respectTransparency false in
/-- Comparing duals successively agrees with comparing them directly. -/
theorem rightDualIso_trans {X A B F : C}
    (p : ExactPairing X A) (q : ExactPairing X B) (r : ExactPairing X F) :
    (rightDualIso p q).hom ≫ (rightDualIso q r).hom = (rightDualIso p r).hom := by
  simp [rightDualIso, ← comp_rightAdjointMate]


section
variable {X Y Z : C}
variable (p : ExactPairing X Y) (q : ExactPairing X Z)

/-- The canonical isomorphism between two right duals transports coevaluation. -/
@[reassoc]
theorem coevaluation_rightDualIso :
    @ExactPairing.coevaluation C _ _ X Y p ≫ X ◁ (rightDualIso p q).hom =
      @ExactPairing.coevaluation C _ _ X Z q := by
  let hp : HasRightDual X := { rightDual := Y, exact := p }
  let hq : HasRightDual X := { rightDual := Z, exact := q }
  simpa only [id_whiskerRight, Category.comp_id] using
    (show (@ExactPairing.coevaluation C _ _ X Y p ≫ X ◁ (rightDualIso p q).hom) =
      (@ExactPairing.coevaluation C _ _ X Z q ≫ (𝟙 X) ▷ Z) from
        @coevaluation_comp_rightAdjointMate C _ _ X X hq hp (𝟙 X))

/-- The canonical isomorphism between two right duals transports evaluation. -/
theorem rightDualIso_evaluation :
    (rightDualIso p q).hom ▷ X ≫ @ExactPairing.evaluation C _ _ X Z q =
      @ExactPairing.evaluation C _ _ X Y p := by
  let hp : HasRightDual X := { rightDual := Y, exact := p }
  let hq : HasRightDual X := { rightDual := Z, exact := q }
  simpa only [whiskerLeft_id, Category.id_comp] using
    (show (rightDualIso p q).hom ▷ X ≫ @ExactPairing.evaluation C _ _ X Z q =
      Y ◁ (𝟙 X) ≫ @ExactPairing.evaluation C _ _ X Y p from
        @rightAdjointMate_comp_evaluation C _ _ X X hq hp (𝟙 X))

/-- Evaluation is preserved by the canonical tensor comparison for right duals. -/
theorem rightDualTensorIso_evaluation (X Y : C) [HasRightDual X] [HasRightDual Y]
    [HasRightDual (X ⊗ Y)] :
    (rightDualTensorIso X Y).hom ▷ (X ⊗ Y) ≫ ε_ (X ⊗ Y) ((Yᘁ) ⊗ (Xᘁ)) =
      ε_ (X ⊗ Y) ((X ⊗ Y)ᘁ) :=
  rightDualIso_evaluation HasRightDual.exact ExactPairing.tensor

variable {A B U V W : C}

set_option backward.isDefEq.respectTransparency false in
/-- Evaluation of tensor pairings respects a change of the first dual. -/
theorem tensorPairing_evaluation_whiskerLeft [p : ExactPairing A U]
    [q : ExactPairing A V] [r : ExactPairing B W] (f : U ⟶ V)
    (hf : f ▷ A ≫ ε_ A V = ε_ A U) :
    (W ◁ f) ▷ (A ⊗ B) ≫ ε_ (A ⊗ B) (W ⊗ V) = ε_ (A ⊗ B) (W ⊗ U) := by
  rw [ExactPairing.tensor_evaluation, ExactPairing.tensor_evaluation]
  calc
    _ = 𝟙 _ ⊗≫ (W : C) ◁ ((f ▷ A ≫ ε_ A V) ▷ B) ⊗≫ ε_ B W := by
      simp only [comp_whiskerRight, whiskerLeft_comp]
      monoidal
    _ = _ := by rw [hf]

set_option backward.isDefEq.respectTransparency false in
/-- Evaluation of tensor pairings respects a change of the second dual. -/
theorem tensorPairing_evaluation_whiskerRight [p : ExactPairing A U]
    [q : ExactPairing B V] [r : ExactPairing B W] (f : V ⟶ W)
    (hf : f ▷ B ≫ ε_ B W = ε_ B V) :
    (f ▷ U) ▷ (A ⊗ B) ≫ ε_ (A ⊗ B) (W ⊗ U) = ε_ (A ⊗ B) (V ⊗ U) := by
  rw [ExactPairing.tensor_evaluation, ExactPairing.tensor_evaluation]
  calc
    _ = 𝟙 _ ⊗≫ ((f ▷ ((U ⊗ A) ⊗ B)) ≫ (W : C) ◁ (ε_ A U ▷ B)) ⊗≫ ε_ B W := by monoidal
    _ = 𝟙 _ ⊗≫ ((V : C) ◁ (ε_ A U ▷ B) ≫ f ▷ ((𝟙_ C) ⊗ B)) ⊗≫ ε_ B W := by
        rw [← whisker_exchange]
    _ = 𝟙 _ ⊗≫ (V : C) ◁ (ε_ A U ▷ B) ⊗≫ (f ▷ B ≫ ε_ B W) := by monoidal
    _ = _ := by rw [hf]

/-- The inverse dual comparison transports coevaluation in the reverse direction. -/
theorem coevaluation_rightDualIso_inv :
    @ExactPairing.coevaluation C _ _ X Z q ≫ X ◁ (rightDualIso p q).inv =
      @ExactPairing.coevaluation C _ _ X Y p :=
  coevaluation_rightDualIso q p

/-- The inverse dual comparison transports evaluation in the reverse direction. -/
theorem rightDualIso_inv_evaluation :
    (rightDualIso p q).inv ▷ X ≫ @ExactPairing.evaluation C _ _ X Y p =
      @ExactPairing.evaluation C _ _ X Z q :=
  rightDualIso_evaluation q p

/-- Closing a morphism does not change when its right dual is replaced by a
canonically isomorphic one and the morphism is transported by the dual map. -/
theorem trace_change_rightDual {X Y Z : C} [HasRightDual Y] [HasRightDual Z]
    (p : ExactPairing X Y) (q : ExactPairing X Z) (u : X ⟶ Zᘁ) :
    @ExactPairing.coevaluation C _ _ X Y p ≫
      ((u ≫ ((rightDualIso p q).hom)ᘁ) ⊗ₘ 𝟙 Y) ≫ ε_ Y (Yᘁ) =
    @ExactPairing.coevaluation C _ _ X Z q ≫ (u ⊗ₘ 𝟙 Z) ≫ ε_ Z (Zᘁ) := by
  simp only [tensorHom_def, whiskerLeft_id, Category.comp_id, comp_whiskerRight, Category.assoc,
    rightAdjointMate_comp_evaluation, ← whisker_exchange_assoc, coevaluation_rightDualIso_assoc]

end

section
variable [RightRigidCategory C]
/-- The chosen right dual used in the unit coherence comparisons. -/
local instance coherenceUnitDual1 : HasRightDual (𝟙_ C) := RightRigidCategory.rightDual _
/-- The chosen right dual used in the unit coherence comparisons. -/
local instance coherenceUnitDual2 : HasRightDual ((𝟙_ C)ᘁ) := RightRigidCategory.rightDual _

set_option backward.isDefEq.respectTransparency false in
/-- The canonical double-dual unit isomorphism has unit evaluation trace. -/
theorem unitDoubleDual_trace :
    η_ (𝟙_ C) ((𝟙_ C)ᘁ) ≫
      ((doubleDualUnitIso (C := C)).hom ⊗ₘ 𝟙 ((𝟙_ C)ᘁ)) ≫
      ε_ ((𝟙_ C)ᘁ) (((𝟙_ C)ᘁ)ᘁ) = 𝟙 (𝟙_ C) := by
  let I := 𝟙_ C
  let hp : ExactPairing I Iᘁ := HasRightDual.exact
  let hq : ExactPairing I I := exactPairingUnit
  let r := rightDualIso hp hq
  apply (trace_change_rightDual hp hq r.inv).trans
  simp only [tensorHom_def, whiskerLeft_id, Category.comp_id]
  erw [rightDualIso_inv_evaluation hp hq, Iso.inv_hom_id]


set_option backward.isDefEq.respectTransparency false in
/-- The pivotal dimension of the tensor unit is one. -/
theorem rightTrace_unit (p : PivotalStructure (C := C)) :
    p.rightTrace (𝟙 (𝟙_ C)) = 1 :=
  End.homEquiv.injective (by
    simpa only [PivotalStructure.rightTrace, rightTraceWith, End.homEquiv_apply, End.one_asHom,
      Category.id_comp, p.unit] using (unitDoubleDual_trace (C := C)))

end

end PropertyF.Ground.Dimensions
