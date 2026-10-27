module
public import PropertyF.Ground.CentreRigid.WindingTensor
public import PropertyF.Ground.Dimensions.DualCoherence

/-! Nested pivotal partial traces for arbitrary surviving objects. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.ExactPairing
namespace PropertyF.Ground.CentreRigid
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
/-- The pivotal cap used to close a right tensor factor. -/
def cap (p : Dimensions.PivotalStructure (C := C)) (T : C) : T ⊗ Tᘁ ⟶ 𝟙_ C :=
  ((p.iso T).hom ▷ Tᘁ) ≫ ε_ (Tᘁ) ((Tᘁ)ᘁ)
set_option backward.isDefEq.respectTransparency false in
/-- The pivotal cap on a tensor product is the nested pair of caps. -/
theorem cap_tensor (p : Dimensions.PivotalStructure (C := C)) (T U : C) :
    ((T ⊗ U) ◁ (rightDualTensorIso T U).inv) ≫ cap p (T ⊗ U) =
      𝟙 ((T ⊗ U) ⊗ (Uᘁ ⊗ Tᘁ)) ⊗≫ (T ◁ cap p U ▷ Tᘁ) ⊗≫ cap p T := by
  let e := rightDualTensorIso T U
  let t := rightDualTensorIso (Uᘁ) (Tᘁ)
  let q : ExactPairing ((Uᘁ) ⊗ (Tᘁ)) (((Tᘁ)ᘁ) ⊗ ((Uᘁ)ᘁ)) := ExactPairing.tensor
  have he := rightAdjointMate_comp_evaluation e.hom
  have ht := Dimensions.rightDualIso_inv_evaluation
    (@HasRightDual.exact C _ _ ((Uᘁ) ⊗ (Tᘁ)) (RightRigidCategory.rightDual _)) q
  change (t.inv ▷ ((Uᘁ) ⊗ (Tᘁ))) ≫ ε_ ((Uᘁ) ⊗ (Tᘁ)) (((Uᘁ) ⊗ (Tᘁ))ᘁ) =
    @ExactPairing.evaluation C _ _ ((Uᘁ) ⊗ (Tᘁ)) (((Tᘁ)ᘁ) ⊗ ((Uᘁ)ᘁ)) q at ht
  have hp := p.tensor T U
  dsimp only [cap]
  rw [hp]
  dsimp only [Dimensions.doubleDualTensorIso, Iso.trans_hom, Iso.symm_hom, Dimensions.rightDualIsoMap]
  change (T ⊗ U) ◁ e.inv ≫
    (((p.iso T).hom ⊗ₘ (p.iso U).hom) ≫ t.inv ≫ e.homᘁ) ▷ (T ⊗ U)ᘁ ≫
      ε_ ((T ⊗ U)ᘁ) (((T ⊗ U)ᘁ)ᘁ) = _
  calc
    _ = 𝟙 _ ⊗≫ (((p.iso T).hom ⊗ₘ (p.iso U).hom) ▷ (Uᘁ ⊗ Tᘁ)) ⊗≫
      (t.inv ▷ (Uᘁ ⊗ Tᘁ)) ⊗≫ ((((Uᘁ ⊗ Tᘁ)ᘁ) ◁ e.inv) ≫
        (e.homᘁ ▷ (T ⊗ U)ᘁ)) ⊗≫ ε_ ((T ⊗ U)ᘁ) (((T ⊗ U)ᘁ)ᘁ) := by
      simp only [comp_whiskerRight, Category.assoc]
      rw [whisker_exchange_assoc]
      rw [whisker_exchange_assoc]
      monoidal
    _ = 𝟙 _ ⊗≫ (((p.iso T).hom ⊗ₘ (p.iso U).hom) ▷ (Uᘁ ⊗ Tᘁ)) ⊗≫
      (t.inv ▷ (Uᘁ ⊗ Tᘁ)) ⊗≫ ((((Uᘁ ⊗ Tᘁ)ᘁ) ◁ e.inv) ≫
        (e.homᘁ ▷ (T ⊗ U)ᘁ) ≫ ε_ ((T ⊗ U)ᘁ) (((T ⊗ U)ᘁ)ᘁ)) := by monoidal
    _ = 𝟙 _ ⊗≫ (((p.iso T).hom ⊗ₘ (p.iso U).hom) ▷ (Uᘁ ⊗ Tᘁ)) ⊗≫
      (t.inv ▷ (Uᘁ ⊗ Tᘁ)) ⊗≫ ((((Uᘁ ⊗ Tᘁ)ᘁ) ◁ e.inv) ≫
        (((Uᘁ ⊗ Tᘁ)ᘁ) ◁ e.hom) ≫ ε_ ((Uᘁ ⊗ Tᘁ)) (((Uᘁ ⊗ Tᘁ))ᘁ)) := by rw [he]
    _ = 𝟙 _ ⊗≫ (((p.iso T).hom ⊗ₘ (p.iso U).hom) ▷ (Uᘁ ⊗ Tᘁ)) ⊗≫
      (t.inv ▷ (Uᘁ ⊗ Tᘁ)) ⊗≫ ε_ ((Uᘁ ⊗ Tᘁ)) (((Uᘁ ⊗ Tᘁ))ᘁ) := by
      have hid : (((Uᘁ ⊗ Tᘁ)ᘁ) ◁ e.inv) ≫ (((Uᘁ ⊗ Tᘁ)ᘁ) ◁ e.hom) ≫
          ε_ ((Uᘁ ⊗ Tᘁ)) (((Uᘁ ⊗ Tᘁ))ᘁ) = ε_ ((Uᘁ ⊗ Tᘁ)) (((Uᘁ ⊗ Tᘁ))ᘁ) := by
        rw [← Category.assoc, ← whiskerLeft_comp, Iso.inv_hom_id, whiskerLeft_id, Category.id_comp]
      rw [hid]
    _ = 𝟙 _ ⊗≫ (((p.iso T).hom ⊗ₘ (p.iso U).hom) ▷ (Uᘁ ⊗ Tᘁ)) ⊗≫
      ((t.inv ▷ (Uᘁ ⊗ Tᘁ)) ≫ ε_ ((Uᘁ ⊗ Tᘁ)) (((Uᘁ ⊗ Tᘁ))ᘁ)) := by monoidal
    _ = 𝟙 _ ⊗≫ (((p.iso T).hom ⊗ₘ (p.iso U).hom) ▷ (Uᘁ ⊗ Tᘁ)) ⊗≫
      (@ExactPairing.evaluation C _ _ ((Uᘁ) ⊗ (Tᘁ)) (((Tᘁ)ᘁ) ⊗ ((Uᘁ)ᘁ)) q) := by rw [ht]
    _ = 𝟙 _ ⊗≫ (((((p.iso T).hom ▷ (U ⊗ Uᘁ)) ≫
        (((Tᘁ : C)ᘁ : C) ◁ (((p.iso U).hom ▷ Uᘁ) ≫ ε_ (Uᘁ : C) ((Uᘁ : C)ᘁ)))) ▷ (Tᘁ : C))) ⊗≫
          ε_ (Tᘁ) ((Tᘁ : C)ᘁ : C) := by
      change 𝟙 _ ⊗≫ (((p.iso T).hom ⊗ₘ (p.iso U).hom) ▷ (Uᘁ ⊗ Tᘁ)) ⊗≫
        (𝟙 _ ⊗≫ (((Tᘁ : C)ᘁ : C) ◁ (ε_ (Uᘁ : C) ((Uᘁ : C)ᘁ) ▷ (Tᘁ))) ⊗≫ ε_ (Tᘁ) ((Tᘁ : C)ᘁ : C)) = _
      simp only [tensorHom_def, comp_whiskerRight, whiskerLeft_comp]
      monoidal
    _ = 𝟙 _ ⊗≫ (((T ◁ (((p.iso U).hom ▷ Uᘁ) ≫ ε_ (Uᘁ : C) ((Uᘁ : C)ᘁ)) ≫
        ((p.iso T).hom ▷ (𝟙_ C))) ▷ (Tᘁ : C))) ⊗≫ ε_ (Tᘁ) ((Tᘁ : C)ᘁ : C) := by rw [whisker_exchange]
    _ = _ := by monoidal


set_option backward.isDefEq.respectTransparency false in
/-- The chosen tensor-product coevaluation agrees with the tensor dual pairing. -/
theorem coeval_tensor (T U : C) :
    η_ (T ⊗ U) ((T ⊗ U)ᘁ) ≫ ((T ⊗ U) ◁ (rightDualTensorIso T U).hom) =
      η_ T (Tᘁ) ⊗≫ (T ◁ η_ U (Uᘁ)) ▷ (Tᘁ) ⊗≫ 𝟙 ((T ⊗ U) ⊗ (Uᘁ ⊗ Tᘁ)) := by
  have h := Dimensions.coevaluation_rightDualIso
    (@HasRightDual.exact C _ _ (T ⊗ U) (RightRigidCategory.rightDual _))
    (show ExactPairing (T ⊗ U) (Uᘁ ⊗ Tᘁ) from ExactPairing.tensor)
  exact h


set_option backward.isDefEq.respectTransparency false in
/-- Closing a tensor product is successive partial tracing, for arbitrary surviving maps. -/
theorem partialTraceHom_nested [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
    (p : Dimensions.PivotalStructure (C := C)) (X Y T U : C)
    (g : X ⊗ (T ⊗ U) ⟶ Y ⊗ (T ⊗ U)) :
    CentreInduction.partialTraceHom p X Y (T ⊗ U) g =
      CentreInduction.partialTraceHom p X Y T
        (CentreInduction.partialTraceHom p (X ⊗ T) (Y ⊗ T) U
          ((α_ X T U).hom ≫ g ≫ (α_ Y T U).inv)) := by
  let e := rightDualTensorIso T U
  have hco := coeval_tensor T U
  have hcap := cap_tensor p T U
  change η_ (T ⊗ U) ((T ⊗ U)ᘁ) ≫ ((T ⊗ U) ◁ e.hom) = _ at hco
  change ((T ⊗ U) ◁ e.inv) ≫ cap p (T ⊗ U) = _ at hcap
  simp only [CentreInduction.partialTraceHom, LinearMap.coe_mk, AddHom.coe_mk]
  have hh : 𝟙 X ⊗≫ (X ◁ η_ (T ⊗ U) ((T ⊗ U)ᘁ)) ⊗≫
      (g ▷ ((T ⊗ U)ᘁ)) ⊗≫ (Y ◁ cap p (T ⊗ U)) ⊗≫ 𝟙 Y =
    𝟙 X ⊗≫ (X ◁ (η_ (T ⊗ U) ((T ⊗ U)ᘁ) ≫ ((T ⊗ U) ◁ e.hom))) ⊗≫
      (g ▷ (Uᘁ ⊗ Tᘁ)) ⊗≫ (Y ◁ (((T ⊗ U) ◁ e.inv) ≫ cap p (T ⊗ U))) ⊗≫ 𝟙 Y := by
    symm
    calc
      _ = 𝟙 X ⊗≫ (X ◁ η_ (T ⊗ U) ((T ⊗ U)ᘁ)) ⊗≫
        (((X ⊗ (T ⊗ U)) ◁ e.hom) ≫ (g ▷ (Uᘁ ⊗ Tᘁ))) ⊗≫
          (Y ◁ ((T ⊗ U) ◁ e.inv)) ⊗≫ (Y ◁ cap p (T ⊗ U)) ⊗≫ 𝟙 Y := by
        simp only [whiskerLeft_comp]
        monoidal
      _ = 𝟙 X ⊗≫ (X ◁ η_ (T ⊗ U) ((T ⊗ U)ᘁ)) ⊗≫
        ((g ▷ ((T ⊗ U)ᘁ)) ≫ ((Y ⊗ (T ⊗ U)) ◁ e.hom)) ⊗≫
          (Y ◁ ((T ⊗ U) ◁ e.inv)) ⊗≫ (Y ◁ cap p (T ⊗ U)) ⊗≫ 𝟙 Y := by rw [whisker_exchange]
      _ = 𝟙 X ⊗≫ (X ◁ η_ (T ⊗ U) ((T ⊗ U)ᘁ)) ⊗≫ (g ▷ ((T ⊗ U)ᘁ)) ⊗≫
        (Y ◁ ((T ⊗ U) ◁ (e.hom ≫ e.inv))) ⊗≫ (Y ◁ cap p (T ⊗ U)) ⊗≫ 𝟙 Y := by
        simp only [whiskerLeft_comp]
        monoidal
      _ = _ := by rw [Iso.hom_inv_id]; monoidal
  rw [hco, hcap] at hh
  calc
    _ = 𝟙 X ⊗≫ (X ◁ η_ (T ⊗ U) ((T ⊗ U)ᘁ)) ⊗≫
      (g ▷ ((T ⊗ U)ᘁ)) ⊗≫ (Y ◁ cap p (T ⊗ U)) ⊗≫ 𝟙 Y := by dsimp [cap]; monoidal
    _ = 𝟙 X ⊗≫ (X ◁ (η_ T (Tᘁ) ⊗≫ (T ◁ η_ U (Uᘁ)) ▷ (Tᘁ) ⊗≫ 𝟙 ((T ⊗ U) ⊗ (Uᘁ ⊗ Tᘁ)))) ⊗≫
      (g ▷ (Uᘁ ⊗ Tᘁ)) ⊗≫ (Y ◁ (𝟙 ((T ⊗ U) ⊗ (Uᘁ ⊗ Tᘁ)) ⊗≫ (T ◁ cap p U ▷ Tᘁ) ⊗≫ cap p T)) ⊗≫ 𝟙 Y := hh
    _ = _ := by dsimp [cap]; simp only [comp_whiskerRight, whiskerLeft_comp]; monoidal

end PropertyF.Ground.CentreRigid
