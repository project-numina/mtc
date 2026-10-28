module
public import PropertyF.Ground.Dimensions.Pivotal

/-! # Duality coherence

Evaluation and coevaluation identities relate changes of duals and the associated traces.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.Dimensions
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- The canonical isomorphism between two right duals transports coevaluation. -/
@[reassoc]
theorem coevaluation_rightDualIso {X Y Z : C} (p : ExactPairing X Y) (q : ExactPairing X Z) :
    @ExactPairing.coevaluation C _ _ X Y p ≫ X ◁ (rightDualIso p q).hom =
      @ExactPairing.coevaluation C _ _ X Z q := by
  let hp : HasRightDual X := { rightDual := Y, exact := p }
  let hq : HasRightDual X := { rightDual := Z, exact := q }
  simpa only [id_whiskerRight, Category.comp_id] using
    (show (@ExactPairing.coevaluation C _ _ X Y p ≫ X ◁ (rightDualIso p q).hom) =
      (@ExactPairing.coevaluation C _ _ X Z q ≫ (𝟙 X) ▷ Z) from
        @coevaluation_comp_rightAdjointMate C _ _ X X hq hp (𝟙 X))

/-- The canonical isomorphism between two right duals transports evaluation. -/
theorem rightDualIso_evaluation {X Y Z : C} (p : ExactPairing X Y) (q : ExactPairing X Z) :
    (rightDualIso p q).hom ▷ X ≫ @ExactPairing.evaluation C _ _ X Z q =
      @ExactPairing.evaluation C _ _ X Y p := by
  let hp : HasRightDual X := { rightDual := Y, exact := p }
  let hq : HasRightDual X := { rightDual := Z, exact := q }
  simpa only [whiskerLeft_id, Category.id_comp] using
    (show (rightDualIso p q).hom ▷ X ≫ @ExactPairing.evaluation C _ _ X Z q =
      Y ◁ (𝟙 X) ≫ @ExactPairing.evaluation C _ _ X Y p from
        @rightAdjointMate_comp_evaluation C _ _ X X hq hp (𝟙 X))

/-- The inverse dual comparison transports coevaluation in the reverse direction. -/
theorem coevaluation_rightDualIso_inv {X Y Z : C} (p : ExactPairing X Y) (q : ExactPairing X Z) :
    @ExactPairing.coevaluation C _ _ X Z q ≫ X ◁ (rightDualIso p q).inv =
      @ExactPairing.coevaluation C _ _ X Y p :=
  coevaluation_rightDualIso q p

/-- The inverse dual comparison transports evaluation in the reverse direction. -/
theorem rightDualIso_inv_evaluation {X Y Z : C} (p : ExactPairing X Y) (q : ExactPairing X Z) :
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
  rw [rightAdjointMate_comp_evaluation]
  rw [← whisker_exchange_assoc]
  rw [coevaluation_rightDualIso_assoc]

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
  have hfinal : @ExactPairing.coevaluation C _ _ (𝟙_ C) (𝟙_ C) hq ≫
      (r.inv ⊗ₘ 𝟙 (𝟙_ C)) ≫
      @ExactPairing.evaluation C _ _ (𝟙_ C) (rightDualObject (𝟙_ C)) hp = 𝟙 (𝟙_ C) := by
    simp only [tensorHom_def, whiskerLeft_id, Category.comp_id]
    change @ExactPairing.coevaluation C _ _ (𝟙_ C) (𝟙_ C) hq ≫
      ((rightDualIso hp hq).inv ▷ (𝟙_ C) ≫
        @ExactPairing.evaluation C _ _ (𝟙_ C) (rightDualObject (𝟙_ C)) hp) = 𝟙 (𝟙_ C)
    rw [(rightDualIso_inv_evaluation hp hq)]
    change (ρ_ (𝟙_ C)).inv ≫ (ρ_ (𝟙_ C)).hom = 𝟙 (𝟙_ C)
    exact Iso.inv_hom_id _
  exact (trace_change_rightDual hp hq r.inv).trans hfinal


set_option backward.isDefEq.respectTransparency false in
/-- The pivotal dimension of the tensor unit is one. -/
theorem rightTrace_unit [RightRigidCategory C] (p : PivotalStructure (C := C)) :
    p.rightTrace (𝟙 (𝟙_ C)) = 1 := by
  apply End.homEquiv.injective
  simpa only [PivotalStructure.rightTrace, End.homEquiv_apply, End.one_asHom,
    Category.id_comp, p.unit] using (unitDoubleDual_trace (C := C))

end PropertyF.Ground.Dimensions
