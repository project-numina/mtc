module
public import PropertyF.Ground.Dimensions.DualCoherence
public import PropertyF.Ground.Dimensions.GroundNorm

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.Dimensions
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RigidCategory C]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency false in
/-- The right quantum trace of the canonical unit double-dual map is one. -/
theorem rightQuantumTrace_unitIso : rightQuantumTrace (doubleDualUnitIso (C := C)) = 1 := by
  let hp : ExactPairing (𝟙_ C) (rightDualObject (𝟙_ C)) :=
    @HasRightDual.exact C _ _ (𝟙_ C) (RightRigidCategory.rightDual (𝟙_ C))
  let hq : ExactPairing (𝟙_ C) (𝟙_ C) := exactPairingUnit
  let r := rightDualIso hp hq
  have h := trace_change_rightDual hp hq r.inv
  have hev := rightDualIso_inv_evaluation hp hq
  apply End.homEquiv.injective
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
    rw [hev]
    change (ρ_ (𝟙_ C)).inv ≫ (ρ_ (𝟙_ C)).hom = 𝟙 (𝟙_ C)
    exact Iso.inv_hom_id _
  exact h.trans hfinal

end PropertyF.Ground.Dimensions
