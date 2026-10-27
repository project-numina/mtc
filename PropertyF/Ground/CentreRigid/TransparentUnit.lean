module
public import PropertyF.Ground.CentreInduction.CounitColumn
public import PropertyF.Ground.CentreInduction.Transparent
public import PropertyF.Ground.Centre.Embeddings

/-! Transparent simple centre objects are the unit. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits CategoryTheory.ExactPairing
namespace PropertyF.Ground.CentreRigid
universe v u
attribute [local instance] Abelian.hasFiniteBiproducts
set_option backward.isDefEq.respectTransparency false in
/-- The evaluation of a simple object is nonzero. -/
theorem simple_eval_ne_zero (C : BraidedFusionCategory.{v,u}) (X : C.Obj) [Simple X] :
    ε_ X Xᘁ ≠ 0 := by
  intro he
  have ht := evaluation_coevaluation'' X Xᘁ
  rw [he] at ht
  have hz : (ρ_ X).inv = 0 := by simpa [monoidalComp] using ht.symm
  have hi : 𝟙 X = 0 := by
    have h := congrArg (fun k => k ≫ (ρ_ X).hom) hz
    simpa using h
  exact id_nonzero X hi

set_option backward.isDefEq.respectTransparency false in
/-- The closed fusion map attached to an isomorphism of simple strands is nonzero. -/
theorem close_iso_ne_zero (C : BraidedFusionCategory.{v,u}) (T S R : C.Obj)
    [Simple T] [Simple S] (e : T ⊗ S ≅ R) :
    CentreInduction.closeFusionMap C T S R e.hom ≠ 0 := by
  letI : Simple (Sᘁ) := by
    letI : Simple (ᘁS) := simple_leftDual C S
    exact Simple.of_iso (leftDualIso HasLeftDual.exact
      (BraidedCategory.exactPairing_swap S (Sᘁ))).symm
  obtain ⟨a, b, hab⟩ := unit_retract_leftDual_tensor (Sᘁ)
  letI : (tensorLeft (Sᘁ)).Faithful := PropertyF.tensorLeft_faithful_of_unit_retract _ _ a b hab
  letI : IsIso (e.homᘁ) := (Dimensions.rightDualIsoMap e).isIso_hom
  intro hz
  have hs : (Sᘁ ◁ ε_ T Tᘁ) = 0 := by
    apply (cancel_epi ((e.homᘁ ▷ T) ≫ ((rightDualTensorIso T S).hom ▷ T) ≫ (α_ (Sᘁ) (Tᘁ) T).hom)).1
    apply (cancel_mono (ρ_ (Sᘁ)).hom).1
    simpa [CentreInduction.closeFusionMap, Category.assoc] using hz
  apply simple_eval_ne_zero C T
  apply (tensorLeft (Sᘁ)).map_injective
  simpa using hs

set_option backward.isDefEq.respectTransparency false in
/-- The diagonal unit-column induction crossing block is nonzero. -/
theorem diagonal_block_ne_zero (C : BraidedFusionCategory.{v,u}) (i : Fin (rank C)) :
    CentreInduction.crossingBlock C (𝟙_ C.Obj) (simples C i) (simples C i)
      (simples C (unitIndex C)) (CentreInduction.simpleTensorUnitIso C i).inv
        (CentreInduction.simpleTensorUnitIso C i).hom ≠ 0 := by
  let T := simples C i
  let S := simples C (unitIndex C)
  let e : T ⊗ S ≅ T := CentreInduction.simpleTensorUnitIso C i
  letI : Simple T := simples_simple C i
  letI : Simple S := simples_simple C (unitIndex C)
  letI : Simple (T ⊗ 𝟙_ C.Obj) := Simple.of_iso (ρ_ T)
  obtain ⟨a, b, hab⟩ := unit_retract_leftDual_tensor (T ⊗ 𝟙_ C.Obj)
  letI : (tensorLeft (T ⊗ 𝟙_ C.Obj)).Faithful :=
    PropertyF.tensorLeft_faithful_of_unit_retract _ _ a b hab
  let q := CentreInduction.closeFusionMap C T S T e.hom
  have hq : q ≠ 0 := close_iso_ne_zero C T S T e
  have hq' : (T ⊗ (𝟙_ C.Obj)) ◁ q ≠ 0 := by
    intro hz
    apply hq
    apply (tensorLeft (T ⊗ (𝟙_ C.Obj))).map_injective
    simpa using hz
  letI : IsIso (e.inv ▷ (𝟙_ C.Obj)) := by infer_instance
  change CentreInduction.crossingBlock C (𝟙_ C.Obj) T T S e.inv e.hom ≠ 0
  intro hz
  apply hq'
  dsimp only [CentreInduction.crossingBlock] at hz
  simp only [tensorHom_def', Category.assoc] at hz
  change (α_ (T ⊗ (𝟙_ C.Obj)) (Tᘁ) T).hom ≫
    ((T ⊗ (𝟙_ C.Obj)) ◁ q) ≫ ((e.inv ▷ (𝟙_ C.Obj)) ▷ (Sᘁ)) ≫ _ = 0 at hz
  apply (cancel_epi (α_ (T ⊗ (𝟙_ C.Obj)) (Tᘁ) T).hom).1
  apply (cancel_mono (((e.inv ▷ (𝟙_ C.Obj)) ▷ (Sᘁ)) ≫
      (α_ (T ⊗ S) (𝟙_ C.Obj) (Sᘁ)).hom ≫ (α_ T S ((𝟙_ C.Obj) ⊗ (Sᘁ))).hom ≫
      (T ◁ (α_ S (𝟙_ C.Obj) (Sᘁ)).inv))).1
  simpa [Category.assoc] using hz

set_option backward.isDefEq.respectTransparency false in
/-- Only the unit simple can make the induced-unit counit central on its strand. -/
theorem counit_comm_forces_unit (C : BraidedFusionCategory.{v,u}) (i : Fin (rank C))
    (hcomm : ((CentreInduction.underlyingCounit C).app (𝟙_ C.Obj) ▷ simples C i) ≫
        (λ_ (simples C i)).hom ≫ (ρ_ (simples C i)).inv =
      CentreInduction.crossingCandidate C (𝟙_ C.Obj) (simples C i) ≫
        (simples C i ◁ (CentreInduction.underlyingCounit C).app (𝟙_ C.Obj))) :
    i = unitIndex C := by
  classical
  by_contra hne
  let V : Fin (rank C) → C.Obj := fun k => (simples C k ⊗ (𝟙_ C.Obj)) ⊗ (simples C k)ᘁ
  have hz : biproduct.ι V i ≫ (CentreInduction.underlyingCounit C).app (𝟙_ C.Obj) = 0 := by
    change biproduct.ι V i ≫ (biproduct.π V (unitIndex C) ≫
      (CentreInduction.unitSummandIso C (𝟙_ C.Obj)).hom) = 0
    rw [← Category.assoc, biproduct.ι_π_ne V hne, zero_comp]
  have hdiag := CentreInduction.crossing_counit_diagonal C (𝟙_ C.Obj) i
  change (biproduct.ι V i ▷ simples C i) ≫ CentreInduction.crossingCandidate C (𝟙_ C.Obj) (simples C i) ≫
      (simples C i ◁ (CentreInduction.underlyingCounit C).app (𝟙_ C.Obj)) = _ at hdiag
  have hh := congrArg (fun k => (biproduct.ι V i ▷ simples C i) ≫ k) hcomm
  simp only [← Category.assoc, ← comp_whiskerRight, hz, MonoidalPreadditive.zero_whiskerRight, zero_comp] at hh
  have hn := diagonal_block_ne_zero C i
  have hn' : CentreInduction.crossingBlock C (𝟙_ C.Obj) (simples C i) (simples C i)
      (simples C (unitIndex C)) (CentreInduction.simpleTensorUnitIso C i).inv
        (CentreInduction.simpleTensorUnitIso C i).hom ≫
          (simples C i ◁ (CentreInduction.unitSummandIso C (𝟙_ C.Obj)).hom) ≠ 0 := by
    intro h
    apply hn
    apply (cancel_mono (simples C i ◁ (CentreInduction.unitSummandIso C (𝟙_ C.Obj)).hom)).1
    simpa using h
  apply hn'
  rw [← hdiag]
  simpa [Category.assoc] using hh.symm

set_option backward.isDefEq.respectTransparency false in
/-- A positive simple centralizing the induced unit is the unit-labelled simple. -/
theorem positive_centralizes_induced_unit (C : BraidedFusionCategory.{v,u}) (i : Fin (rank C))
    (h : Centre.Centralizes ((CategoryTheory.Center.ofBraided C.Obj).obj (simples C i))
      ((CentreInduction.induction C).obj (𝟙_ C.Obj))) : i = unitIndex C :=
  CentreInduction.positive_simple_centralizes_induced_unit C i (Centre.centralizes_symm h)

set_option backward.isDefEq.respectTransparency false in
/-- A simple centre object centralizing negative images and the induced unit is the unit. -/
theorem negative_and_induced_detect_unit (C : BraidedFusionCategory.{v,u}) (Z : Center C.Obj) [Simple Z]
    (hneg : ∀ T : C.Obj, Centre.Centralizes Z ((Centre.negative C.Obj).obj T))
    (hJ : Centre.Centralizes Z ((CentreInduction.induction C).obj (𝟙_ C.Obj))) :
    Nonempty (Z ≅ 𝟙_ (Center C.Obj)) := by
  let F := CategoryTheory.Center.ofBraided C.Obj
  let J := (CentreInduction.induction C).obj (𝟙_ C.Obj)
  letI : F.PreservesMonomorphisms := {
    preserves := fun f => by
      intro _
      apply (CategoryTheory.Center.forget C.Obj).mono_of_mono_map
      change Mono f
      infer_instance }
  let eZ := Centre.positiveIsoOfCentralizesNegative Z hneg
  letI : Simple (F.obj Z.1) := Simple.of_iso eZ.symm
  letI : Simple Z.1 := Functor.simple_of_simple_obj F Z.1
  obtain ⟨i, ⟨e⟩⟩ := exists_simple_iso C Z.1
  have hc : Centre.Centralizes (F.obj (simples C i)) J := by
    apply Centre.centralizes_of_iso_left (F.mapIso e).symm
    exact Centre.centralizes_of_iso_left eZ.symm hJ
  have hi := positive_centralizes_induced_unit C i hc
  subst i
  obtain ⟨u⟩ := unitIndex_iso C
  exact ⟨eZ ≪≫ F.mapIso e ≪≫ F.mapIso u ≪≫ (Functor.Monoidal.εIso F).symm⟩

set_option backward.isDefEq.respectTransparency false in
/-- Every transparent simple object of the actual Drinfeld centre is the unit. -/
theorem transparent_simple_is_unit (C : BraidedFusionCategory.{v,u}) (Z : Center C.Obj) [Simple Z]
    (h : ∀ W : Center C.Obj, Centre.Centralizes Z W) :
    Nonempty (Z ≅ 𝟙_ (Center C.Obj)) :=
  CentreInduction.center_transparent_simple_iso_unit C Z h

end PropertyF.Ground.CentreRigid
