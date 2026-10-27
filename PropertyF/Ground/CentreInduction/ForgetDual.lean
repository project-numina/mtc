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

set_option backward.isDefEq.respectTransparency false in
/-- The same trace transport needs only one compatible double-dual isomorphism. -/
theorem forget_trace_of_single_component
    (p : Dimensions.PivotalStructure (C := C.Obj))
    (Z : CategoryTheory.Center C.Obj) (j : Z ≅ ((Zᘁ)ᘁ))
    (hcompat : (j.hom.f) ≫ (forgetDoubleDualIso C Z).hom = (p.iso Z.1).hom) :
    (η_ Z (Zᘁ) ≫ (j.hom ⊗ₘ 𝟙 (Zᘁ)) ≫ ε_ (Zᘁ) ((Zᘁ)ᘁ)).f =
      (p.rightTrace (𝟙 Z.1)).asHom := by
  let e := forgetDualIso C Z
  let e' := forgetDualIso C (Zᘁ)
  let u : Z.1 ⟶ ((Zᘁ)ᘁ).1 := j.hom.f
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
  have hn : (η_ Z (Zᘁ) ≫ (j.hom ⊗ₘ 𝟙 (Zᘁ)) ≫ ε_ (Zᘁ) ((Zᘁ)ᘁ)).f =
      (η_ Z (Zᘁ)).f ≫ ((u ≫ e'.hom) ⊗ₘ 𝟙 ((Zᘁ).1)) ≫
        ε_ ((Zᘁ).1) (((Zᘁ).1)ᘁ) := by
    simp only [tensorHom_def, whiskerLeft_id, Category.comp_id,
      CategoryTheory.Center.comp_f, CategoryTheory.Center.whiskerRight_f]
    rw [← heval]
    simp [comp_whiskerRight, Category.assoc, u]
  rw [hn, htrans, ht]
  simp [Dimensions.PivotalStructure.rightTrace]

set_option backward.isDefEq.respectTransparency false in
/-- A compatible centre pivotal component implies fusion for a positive base. -/
theorem center_fusion_of_positive_pivotal_component
    (p : Dimensions.PivotalStructure (C := C.Obj)) (d : Fin (rank C) → ℝ)
    (hreal : ∀ i, Dimensions.pivotalDimension C p (simples C i) = (d i : ℂ))
    (hpos : ∀ i, 0 < d i)
    (pZ : Dimensions.PivotalStructure (C := CategoryTheory.Center C.Obj))
    (hcompat : ((pZ.iso ((induction C).obj (𝟙_ C.Obj))).hom.f) ≫
      (forgetDoubleDualIso C ((induction C).obj (𝟙_ C.Obj))).hom =
        (p.iso (underlying C (𝟙_ C.Obj))).hom) :
    IsFusionCategory (CategoryTheory.Center C.Obj) :=
  center_fusion_of_positive_compatible_pivotal C p d hreal hpos pZ
    (forget_trace_of_pivotal_component C p pZ ((induction C).obj (𝟙_ C.Obj)) hcompat)

set_option backward.isDefEq.respectTransparency false in
/-- A compatible isomorphism on the induced unit alone implies centre fusion. -/
theorem center_fusion_of_single_pivotal_iso
    (p : Dimensions.PivotalStructure (C := C.Obj)) (d : Fin (rank C) → ℝ)
    (hreal : ∀ i, Dimensions.pivotalDimension C p (simples C i) = (d i : ℂ))
    (hpos : ∀ i, 0 < d i)
    (j : (induction C).obj (𝟙_ C.Obj) ≅ ((((induction C).obj (𝟙_ C.Obj))ᘁ)ᘁ))
    (hcompat : j.hom.f ≫ (forgetDoubleDualIso C ((induction C).obj (𝟙_ C.Obj))).hom =
      (p.iso (underlying C (𝟙_ C.Obj))).hom) : IsFusionCategory (CategoryTheory.Center C.Obj) := by
  let J := (induction C).obj (𝟙_ C.Obj)
  let cap : J ⊗ Jᘁ ⟶ 𝟙_ (CategoryTheory.Center C.Obj) :=
    (j.hom ⊗ₘ 𝟙 (Jᘁ)) ≫ ε_ (Jᘁ) ((Jᘁ)ᘁ)
  have ht := forget_trace_of_single_component C p J j hcompat
  change (η_ J (Jᘁ) ≫ cap).f =
    (p.rightTrace (𝟙 (underlying C (𝟙_ C.Obj)))).asHom at ht
  have hsimple : ∀ i, Dimensions.pivotalDimension C p (simples C i) = (fpSimple C i : ℂ) := by
    intro i
    rw [hreal, Dimensions.positive_pivotalDimension_eq_fpSimple C p d hreal hpos]
  have hd := induced_unit_dimension C p hsimple
  have hpos' : 0 < globalFPDimension C := lt_of_lt_of_le zero_lt_one (one_le_globalFPDimension C)
  have hdim : Dimensions.pivotalDimension C p (underlying C (𝟙_ C.Obj)) ≠ 0 := by
    rw [hd]
    exact_mod_cast (ne_of_gt hpos')
  have hcap : η_ J (Jᘁ) ≫ cap ≠ 0 := by
    intro hz
    have hbase : (p.rightTrace (𝟙 (underlying C (𝟙_ C.Obj)))) = 0 := by
      apply End.ext
      rw [← ht]
      change (η_ J (Jᘁ) ≫ cap).f = 0
      rw [hz]
      rfl
    apply hdim
    unfold Dimensions.pivotalDimension
    rw [hbase, ← Dimensions.groundUnitScalarEquiv_apply]
    exact map_zero _
  exact center_fusion_of_nonzero_induced_cap C (𝟙_ C.Obj) cap hcap

set_option backward.isDefEq.respectTransparency false in
/-- Centre fusion follows from centrality of the base pivotal map on the induced unit. -/
theorem center_fusion_of_induced_pivotal_centrality
    (p : Dimensions.PivotalStructure (C := C.Obj)) (d : Fin (rank C) → ℝ)
    (hreal : ∀ i, Dimensions.pivotalDimension C p (simples C i) = (d i : ℂ))
    (hpos : ∀ i, 0 < d i)
    (hcomm : ∀ T : C.Obj,
      let J := (induction C).obj (𝟙_ C.Obj)
      let u := (p.iso (underlying C (𝟙_ C.Obj))).hom ≫ (forgetDoubleDualIso C J).inv
      (u ▷ T) ≫ (((Jᘁ)ᘁ).2.β T).hom = (J.2.β T).hom ≫ (T ◁ u)) :
    IsFusionCategory (CategoryTheory.Center C.Obj) := by
  let J := (induction C).obj (𝟙_ C.Obj)
  let u : J.1 ⟶ ((Jᘁ)ᘁ).1 := (p.iso (underlying C (𝟙_ C.Obj))).hom ≫ (forgetDoubleDualIso C J).inv
  let f : J ⟶ ((Jᘁ)ᘁ) := ⟨u, hcomm⟩
  letI : IsIso f.f := by change IsIso u; dsimp only [u]; infer_instance
  let j : J ≅ ((Jᘁ)ᘁ) := CategoryTheory.Center.isoMk f
  apply center_fusion_of_single_pivotal_iso C p d hreal hpos j
  change u ≫ (forgetDoubleDualIso C J).hom = (p.iso (underlying C (𝟙_ C.Obj))).hom
  simp [u, Category.assoc]

set_option backward.isDefEq.respectTransparency false in
/-- The single centrality condition need only be checked on base simples. -/
theorem center_fusion_of_simple_induced_pivotal_centrality
    (p : Dimensions.PivotalStructure (C := C.Obj)) (d : Fin (rank C) → ℝ)
    (hreal : ∀ i, Dimensions.pivotalDimension C p (simples C i) = (d i : ℂ))
    (hpos : ∀ i, 0 < d i)
    (hcomm : ∀ i : Fin (rank C),
      let J := (induction C).obj (𝟙_ C.Obj)
      let u := (p.iso (underlying C (𝟙_ C.Obj))).hom ≫ (forgetDoubleDualIso C J).inv
      (u ▷ simples C i) ≫ (((Jᘁ)ᘁ).2.β (simples C i)).hom =
        (J.2.β (simples C i)).hom ≫ (simples C i ◁ u)) :
    IsFusionCategory (CategoryTheory.Center C.Obj) := by
  apply center_fusion_of_induced_pivotal_centrality C p d hreal hpos
  let J := (induction C).obj (𝟙_ C.Obj)
  let u := (p.iso (underlying C (𝟙_ C.Obj))).hom ≫ (forgetDoubleDualIso C J).inv
  exact comm_of_simples C J ((Jᘁ)ᘁ) u hcomm

end PropertyF.Ground.CentreInduction
