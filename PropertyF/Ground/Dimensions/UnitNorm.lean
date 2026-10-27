module
public import PropertyF.Ground.Dimensions.DualCoherence
public import PropertyF.Ground.Dimensions.GroundNorm

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.Dimensions
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RigidCategory C]

set_option backward.isDefEq.respectTransparency false in
/-- The two quantum traces of the canonical unit double-dual map agree. -/
theorem leftQuantumTrace_unitIso : leftQuantumTrace (doubleDualUnitIso (C := C)) = rightQuantumTrace (doubleDualUnitIso (C := C)) := by
  rw [leftQuantumTrace_eq_rightDual]
  let j := doubleDualUnitIso (C := C)
  let r := rightDualUnitIso (C := C)
  have hnat : r.hom ≫ j.hom = (rightDualIsoMap j).symm.hom ≫ (rightDualIsoMap (rightDualIsoMap r)).hom := by
    dsimp [j, r, doubleDualUnitIso, rightDualIsoMap]
    simp only [Iso.hom_inv_id_assoc]
    let _ : HasRightDual (𝟙_ C) := RightRigidCategory.rightDual (𝟙_ C)
    let _ : HasRightDual (rightDualObject (𝟙_ C)) := RightRigidCategory.rightDual _
    rw [comp_rightAdjointMate]
    simp [← Category.assoc, ← comp_rightAdjointMate]

  exact rightQuantumTrace_iso (rightDualIsoMap j).symm j r hnat

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

/-- The intrinsic squared norm of the tensor unit is one, without any
pivotal or spherical structure. -/
theorem target_squaredNorm_unit (C : Ground.BraidedFusionCategory.{v,u}) :
    Ground.squaredNorm C (𝟙_ C.Obj) = 1 := by
  let : Simple (𝟙_ C.Obj) := Ground.IsFusionCategory.unit_simple
  rw [target_squaredNorm_choice_independent C (𝟙_ C.Obj) (doubleDualUnitIso (C := C.Obj))]
  rw [leftQuantumTrace_unitIso, rightQuantumTrace_unitIso]
  simp [Ground.unitScalar_eq_equiv]

end PropertyF.Ground.Dimensions
