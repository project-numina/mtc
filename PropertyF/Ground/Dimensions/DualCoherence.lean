module
public import PropertyF.Ground.Dimensions.Pivotal

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
  have h := @coevaluation_comp_rightAdjointMate C _ _ X X hq hp (𝟙 X)
  change (@ExactPairing.coevaluation C _ _ X Y p ≫ X ◁ (rightDualIso p q).hom) =
    (@ExactPairing.coevaluation C _ _ X Z q ≫ (𝟙 X) ▷ Z) at h
  rw [id_whiskerRight, Category.comp_id] at h
  exact h

/-- The canonical isomorphism between two right duals transports evaluation. -/
theorem rightDualIso_evaluation {X Y Z : C} (p : ExactPairing X Y) (q : ExactPairing X Z) :
    (rightDualIso p q).hom ▷ X ≫ @ExactPairing.evaluation C _ _ X Z q =
      @ExactPairing.evaluation C _ _ X Y p := by
  let hp : HasRightDual X := { rightDual := Y, exact := p }
  let hq : HasRightDual X := { rightDual := Z, exact := q }
  have h := @rightAdjointMate_comp_evaluation C _ _ X X hq hp (𝟙 X)
  change (rightDualIso p q).hom ▷ X ≫ @ExactPairing.evaluation C _ _ X Z q =
    Y ◁ (𝟙 X) ≫ @ExactPairing.evaluation C _ _ X Y p at h
  rw [whiskerLeft_id, Category.id_comp] at h
  exact h

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

end PropertyF.Ground.Dimensions
