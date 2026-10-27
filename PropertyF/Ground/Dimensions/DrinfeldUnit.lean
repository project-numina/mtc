module
public import PropertyF.Ground.Dimensions.CoevaluationSliding

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.BraidedCategory
namespace PropertyF.Ground.Dimensions
universe v u
set_option backward.isDefEq.respectTransparency false in
/-- The braided double-dual map has the canonical component on the unit. -/
theorem drinfeld_unit (C : Ground.BraidedFusionCategory.{v,u}) :
    (Ground.doubleDualIso C (𝟙_ C.Obj)).hom = (doubleDualUnitIso (C := C.Obj)).hom := by
  let U : C.Obj := 𝟙_ C.Obj
  let : HasRightDual U := RightRigidCategory.rightDual U
  let : HasRightDual (Uᘁ) := RightRigidCategory.rightDual (Uᘁ)
  let r : Uᘁ ≅ U := by
    change rightDualObject (𝟙_ C.Obj) ≅ 𝟙_ C.Obj
    exact rightDualUnitIso
  have h : (r.inv ≫ (r.homᘁ)) ▷ (Uᘁ) ≫ ε_ (Uᘁ) ((Uᘁ)ᘁ) =
      (β_ U (Uᘁ)).hom ≫ ε_ U (Uᘁ) := by
    rw [comp_whiskerRight_assoc, rightAdjointMate_comp_evaluation]
    have hb : (β_ U U).hom = 𝟙 (U ⊗ U) := by
      change (β_ (𝟙_ C.Obj) (𝟙_ C.Obj)).hom = 𝟙 _
      rw [braiding_tensorUnit_left, unitors_equal, Iso.hom_inv_id]
    have hn := braiding_naturality_right U r.hom
    rw [hb, Category.comp_id] at hn
    have hc : U ◁ r.hom ≫ r.inv ▷ U = (β_ U (Uᘁ)).hom := by
      rw [hn, Category.assoc, ← comp_whiskerRight, Iso.hom_inv_id, id_whiskerRight, Category.comp_id]
    rw [← whisker_exchange_assoc, ← Category.assoc, hc]
  change (doubleDualUnitIso (C := C.Obj)).hom ▷ (Uᘁ) ≫ ε_ (Uᘁ) ((Uᘁ)ᘁ) = _ at h
  have he := (drinfeld_eval C U).trans h.symm
  have ht := congrArg (tensorRightHomEquiv U (Uᘁ) ((Uᘁ)ᘁ) U) he
  have hh := @tensorRightHomEquiv_whiskerRight_comp_evaluation C.Obj _ _ (Uᘁ) U this
    (Ground.doubleDualIso C U).hom
  have hh' := @tensorRightHomEquiv_whiskerRight_comp_evaluation C.Obj _ _ (Uᘁ) U this
    (doubleDualUnitIso (C := C.Obj)).hom
  rw [hh, hh'] at ht
  exact (cancel_mono (λ_ ((Uᘁ)ᘁ)).inv).1 ht
end PropertyF.Ground.Dimensions
