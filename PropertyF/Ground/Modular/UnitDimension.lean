module
public import PropertyF.Ground.Modular.DimensionNonzero
public import PropertyF.Ground.Dimensions.DualCoherence

/-! The unit axiom of a pivotal structure normalizes the tensor-unit trace. -/
open CategoryTheory CategoryTheory.MonoidalCategory
open PropertyF.Ground.Dimensions
@[expose] public noncomputable section
namespace PropertyF.Ground.Modular
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]

set_option backward.isDefEq.respectTransparency false in
/-- The pivotal trace of the identity on the tensor unit is the unit scalar. -/
theorem trace_unit (p : PivotalStructure (C := C)) :
    p.rightTrace (𝟙 (𝟙_ C)) = 1 := by
  let _ : HasRightDual (𝟙_ C) := RightRigidCategory.rightDual (𝟙_ C)
  let _ : HasRightDual (rightDualObject (𝟙_ C)) :=
    RightRigidCategory.rightDual (rightDualObject (𝟙_ C))
  let _ : ExactPairing (rightDualObject (𝟙_ C)) (rightDualObject (rightDualObject (𝟙_ C))) :=
    @HasRightDual.exact C _ _ _ (RightRigidCategory.rightDual (rightDualObject (𝟙_ C)))
  let a := rightDualUnitIso (C := C)
  let p₀ : ExactPairing (𝟙_ C) (rightDualObject (𝟙_ C)) := HasRightDual.exact
  let q₀ : ExactPairing (𝟙_ C) (𝟙_ C) := inferInstance
  have ht := trace_change_rightDual p₀ q₀ a.symm.hom
  have ha : rightDualIso p₀ q₀ = a := rfl
  rw [ha] at ht
  have he := rightDualIso_inv_evaluation p₀ q₀
  rw [ha] at he
  apply End.homEquiv.injective
  change (η_ (𝟙_ C) (rightDualObject (𝟙_ C))) ≫
    ((𝟙 (𝟙_ C) ≫ (p.iso (𝟙_ C)).hom) ⊗ₘ 𝟙 (rightDualObject (𝟙_ C))) ≫
      ε_ (rightDualObject (𝟙_ C)) ((rightDualObject (rightDualObject (𝟙_ C)))) = 𝟙 (𝟙_ C)
  rw [Category.id_comp, p.unit]
  change @ExactPairing.coevaluation C _ _ _ _ p₀ ≫
    ((a.symm.hom ≫ a.homᘁ) ⊗ₘ 𝟙 (rightDualObject (𝟙_ C))) ≫
      ε_ (rightDualObject (𝟙_ C)) ((rightDualObject (rightDualObject (𝟙_ C)))) = 𝟙 (𝟙_ C)
  refine ht.trans ?_
  have he' := congrArg (fun f => @ExactPairing.coevaluation C _ _ _ _ q₀ ≫ f) he
  have hlast : @ExactPairing.coevaluation C _ _ _ _ q₀ ≫
      @ExactPairing.evaluation C _ _ _ _ q₀ = 𝟙 (𝟙_ C) := by
    change (ρ_ (𝟙_ C)).inv ≫ (ρ_ (𝟙_ C)).hom = _
    simp
  apply Eq.trans _ hlast
  dsimp only [rightDualObject] at he' ⊢
  simpa only [Category.assoc, tensorHom_id, Iso.symm_hom] using he'

/-- The dimension of the simple representative of the tensor unit is one. -/
theorem simpleDimension_unit (C : Ground.BraidedFusionCategory.{v,u})
    (p : PivotalStructure (C := C.Obj)) : simpleDimension C p (unitIndex C) = 1 := by
  obtain ⟨e⟩ := unitIndex_iso C
  unfold simpleDimension
  rw [p.rightTrace_id_iso e, trace_unit, map_one]

end PropertyF.Ground.Modular
