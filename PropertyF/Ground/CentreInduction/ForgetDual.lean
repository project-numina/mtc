module
public import PropertyF.Ground.CentreInduction.InducedTrace

/-! Transport duality through centre forget and reduce fusion to one component. -/
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
universe v u
@[expose] public noncomputable section
namespace PropertyF.Ground.CentreInduction
variable (C : BraidedFusionCategory.{v,u}) [RigidCategory (CategoryTheory.Center C.Obj)]

set_option backward.isDefEq.respectTransparency false in
/-- Forgetting a centre dual pair gives a dual pair in the base category. -/
@[instance_reducible] def forgetPairing (Z : CategoryTheory.Center C.Obj) : ExactPairing Z.1 ((Zᘁ).1) where
  coevaluation' := (η_ Z (Zᘁ)).f
  evaluation' := (ε_ Z (Zᘁ)).f
  coevaluation_evaluation' := by
    have h := congrArg CategoryTheory.Center.Hom.f (ExactPairing.coevaluation_evaluation Z (Zᘁ))
    simpa only [CategoryTheory.Center.comp_f, CategoryTheory.Center.whiskerLeft_f,
      CategoryTheory.Center.whiskerRight_f, CategoryTheory.Center.associator_inv_f,
      CategoryTheory.Center.associator_hom_f, CategoryTheory.Center.rightUnitor_hom_f,
      CategoryTheory.Center.rightUnitor_inv_f, CategoryTheory.Center.leftUnitor_hom_f,
      CategoryTheory.Center.leftUnitor_inv_f] using h
  evaluation_coevaluation' := by
    have h := congrArg CategoryTheory.Center.Hom.f (ExactPairing.evaluation_coevaluation Z (Zᘁ))
    simpa only [CategoryTheory.Center.comp_f, CategoryTheory.Center.whiskerLeft_f,
      CategoryTheory.Center.whiskerRight_f, CategoryTheory.Center.associator_inv_f,
      CategoryTheory.Center.associator_hom_f, CategoryTheory.Center.rightUnitor_hom_f,
      CategoryTheory.Center.rightUnitor_inv_f, CategoryTheory.Center.leftUnitor_hom_f,
      CategoryTheory.Center.leftUnitor_inv_f] using h

/-- Compare the underlying centre dual with the chosen base dual. -/
def forgetDualIso (Z : CategoryTheory.Center C.Obj) : ((Zᘁ).1) ≅ (Z.1ᘁ) :=
  rightDualIso (forgetPairing C Z) HasRightDual.exact

/-- Compare the underlying centre double dual with the chosen base double dual. -/
def forgetDoubleDualIso (Z : CategoryTheory.Center C.Obj) : (((Zᘁ)ᘁ).1) ≅ ((Z.1ᘁ)ᘁ) :=
  forgetDualIso C (Zᘁ) ≪≫ Dimensions.rightDualIsoMap (forgetDualIso C Z).symm

set_option backward.isDefEq.respectTransparency false in
/-- Compatible pivotal components have equal traces after forgetting. -/
theorem forget_trace_of_pivotal_component
    (p : Dimensions.PivotalStructure (C := C.Obj))
    (pZ : Dimensions.PivotalStructure (C := CategoryTheory.Center C.Obj))
    (Z : CategoryTheory.Center C.Obj)
    (hcompat : ((pZ.iso Z).hom.f) ≫ (forgetDoubleDualIso C Z).hom = (p.iso Z.1).hom) :
    (pZ.rightTrace (𝟙 Z)).asHom.f = (p.rightTrace (𝟙 Z.1)).asHom := by
  let e := forgetDualIso C Z
  let e' := forgetDualIso C (Zᘁ)
  let u : Z.1 ⟶ ((Zᘁ)ᘁ).1 := (pZ.iso Z).hom.f
  have hu : u ≫ e'.hom ≫ (e.invᘁ) = (p.iso Z.1).hom := by
    simpa [forgetDoubleDualIso, Dimensions.rightDualIsoMap, e, e', u, Category.assoc] using hcompat
  have htrans : u ≫ e'.hom = (p.iso Z.1).hom ≫ (e.homᘁ) := by
    rw [← hu]
    simp only [Category.assoc, ← comp_rightAdjointMate, Iso.hom_inv_id,
      rightAdjointMate_id, Category.comp_id]
  have heval := Dimensions.rightDualIso_evaluation (forgetPairing C (Zᘁ)) HasRightDual.exact
  change (e'.hom ▷ ((Zᘁ).1)) ≫ ε_ ((Zᘁ).1) (((Zᘁ).1)ᘁ) = (ε_ (Zᘁ) ((Zᘁ)ᘁ)).f at heval
  have ht := Dimensions.trace_change_rightDual (forgetPairing C Z) HasRightDual.exact (p.iso Z.1).hom
  change (η_ Z (Zᘁ)).f ≫ (((p.iso Z.1).hom ≫ (e.homᘁ)) ⊗ₘ 𝟙 ((Zᘁ).1)) ≫
      ε_ ((Zᘁ).1) (((Zᘁ).1)ᘁ) =
    η_ Z.1 (Z.1ᘁ) ≫ ((p.iso Z.1).hom ⊗ₘ 𝟙 (Z.1ᘁ)) ≫ ε_ (Z.1ᘁ) ((Z.1ᘁ)ᘁ) at ht
  have hn : (pZ.rightTrace (𝟙 Z)).asHom.f =
      (η_ Z (Zᘁ)).f ≫ ((u ≫ e'.hom) ⊗ₘ 𝟙 ((Zᘁ).1)) ≫
        ε_ ((Zᘁ).1) (((Zᘁ).1)ᘁ) := by
    dsimp [Dimensions.PivotalStructure.rightTrace]
    simp only [Category.id_comp, tensorHom_def, whiskerLeft_id, Category.comp_id,
      CategoryTheory.Center.comp_f, CategoryTheory.Center.whiskerRight_f]
    rw [← heval]
    simp [comp_whiskerRight, Category.assoc, u]
  rw [hn, htrans, ht]
  simp [Dimensions.PivotalStructure.rightTrace]






end PropertyF.Ground.CentreInduction
