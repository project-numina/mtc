module
public import PropertyF.Ground.CentreInduction.PivotalCentrality
public import PropertyF.Ground.CentreInduction.SecondTriangle
public import PropertyF.Ground.Centre.Basic

/-! The actual centre has no nontrivial transparent simple objects. -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.BraidedCategory CategoryTheory.Limits
namespace PropertyF.Ground.CentreInduction
universe v u
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Abelian.hasFiniteBiproducts
variable (C : BraidedFusionCategory.{v,u})

/-- A positive simple image centralizing the induced unit is the unit. -/
theorem positive_simple_centralizes_induced_unit (i : Fin (rank C))
    (hcentral : Centre.Centralizes
      ((induction C).obj (𝟙_ C.Obj)) ((CategoryTheory.Center.ofBraided C.Obj).obj (simples C i))) :
    i = unitIndex C := by
  classical
  by_contra hi
  let X := 𝟙_ C.Obj
  let S := simples C i
  let V : Fin (rank C) → C.Obj := fun k => (simples C k ⊗ X) ⊗ (simples C k)ᘁ
  have hz : biproduct.ι V i ≫ (underlyingCounit C).app X = 0 := by
    change biproduct.ι V i ≫ biproduct.π V (unitIndex C) ≫ (unitSummandIso C X).hom = 0
    rw [← Category.assoc, biproduct.ι_π_ne _ hi, zero_comp]
  have hm := congrArg CategoryTheory.Center.Hom.f hcentral
  change crossingCandidate C X S ≫ (β_ S (underlying C X)).hom = 𝟙 _ at hm
  have hb : crossingCandidate C X S = (β_ S (underlying C X)).inv :=
    by simpa only [IsIso.Iso.inv_hom] using IsIso.eq_inv_of_inv_hom_id hm
  have hzero : (biproduct.ι V i ▷ S) ≫ crossingCandidate C X S ≫
      (S ◁ (underlyingCounit C).app X) = 0 := by
    rw [hb]
    change (biproduct.ι V i ▷ S) ≫ (β_ S (⨁ V)).inv ≫
      (S ◁ (underlyingCounit C).app X) = 0
    rw [braiding_inv_naturality_left_assoc]
    simp only [← whiskerLeft_comp, hz, MonoidalPreadditive.whiskerLeft_zero,
      comp_zero]
  have h := unit_matrix_reduce C X i i
  change biproduct.ι V i ≫ unitComponent C ((induction C).obj X) i ≫
    ((S ◁ (underlyingCounit C).app X) ▷ (Sᘁ)) = _ at h
  rw [hzero] at h
  have hid : 𝟙 (V i) = 0 := by
    rw [← unit_diag C X i, h]
    simp [monoidalComp]
  let : Simple S := simples_simple C i
  let e : S ⊗ (Sᘁ) ≅ V i := whiskerRightIso (ρ_ S).symm (Sᘁ)
  have hcoe : η_ S (Sᘁ) = 0 :=
    (e.isZero_iff.mpr ((IsZero.iff_id_eq_zero _).2 hid)).eq_of_tgt _ _
  have ht := ExactPairing.evaluation_coevaluation S (Sᘁ)
  have hh := congrArg (fun f => (λ_ S).inv ≫ f ≫ (ρ_ S).hom) ht
  apply id_nonzero S
  simpa [hcoe] using hh.symm

/-- Every transparent simple of the actual centre is the unit. -/
theorem center_transparent_simple_iso_unit (Z : CategoryTheory.Center C.Obj) [Simple Z]
    (hcentral : ∀ W : CategoryTheory.Center C.Obj, Centre.Centralizes Z W) :
    Nonempty (Z ≅ 𝟙_ (CategoryTheory.Center C.Obj)) := by
  let F := CategoryTheory.Center.ofBraided C.Obj
  let e := Centre.positiveIsoOfCentralizesNegative Z (fun X => hcentral ((Centre.negative C.Obj).obj X))
  let : F.PreservesMonomorphisms := {
    preserves := fun f => by
      intro _
      apply (CategoryTheory.Center.forget C.Obj).mono_of_mono_map
      change Mono f
      infer_instance }
  let : Simple (F.obj Z.1) := Simple.of_iso e.symm
  let : Simple Z.1 := Functor.simple_of_simple_obj F Z.1
  obtain ⟨i, ⟨s⟩⟩ := exists_simple_iso C Z.1
  let e' : Z ≅ F.obj (simples C i) := e ≪≫ F.mapIso s
  have hc : Centre.Centralizes ((induction C).obj (𝟙_ C.Obj)) (F.obj (simples C i)) := by
    apply Centre.centralizes_symm
    exact Centre.centralizes_of_iso_left e'.symm (hcentral _)
  have hi := positive_simple_centralizes_induced_unit C i hc
  have es : simples C i ≅ 𝟙_ C.Obj := by
    subst i
    exact Classical.choice (unitIndex_iso C)
  exact ⟨e' ≪≫ F.mapIso es ≪≫ (CategoryTheory.Functor.Monoidal.εIso F).symm⟩

end PropertyF.Ground.CentreInduction
