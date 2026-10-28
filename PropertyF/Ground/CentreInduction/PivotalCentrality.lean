module
public import PropertyF.Ground.CentreInduction.PositivePivotal
public import PropertyF.Ground.CentreInduction.SecondTriangle
public import PropertyF.Ground.Centre.Basic
public import PropertyF.Ground.Dimensions.DualTensorNaturality
public import PropertyF.Ground.Dimensions.DualBraiding
public import PropertyF.Ground.Dimensions.DoubleDualMonoidal

/-! The pivotal structure of the base lifts to the rigid centre. -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.BraidedCategory
namespace PropertyF.Ground.CentreInduction
universe v u
set_option backward.isDefEq.respectTransparency false
variable {D : Type u} [Category.{v} D] [MonoidalCategory D] [RightRigidCategory D]
  [RigidCategory (CategoryTheory.Center D)]

/-- Transported pivotal components respect the braiding between centre objects. -/
private theorem transported_pivotal_braiding (p : Dimensions.PivotalStructure (C := D)) (Z B : CategoryTheory.Center D) :
    let u (W : CategoryTheory.Center D) : W.1 ⟶ ((Wᘁ)ᘁ).1 :=
      (p.iso W.1).hom ≫ (forgetDoubleDualIso W).inv
    (β_ Z B).hom.f ≫ (u B ⊗ₘ u Z) =
      (u Z ⊗ₘ u B) ≫ (β_ ((Zᘁ)ᘁ) ((Bᘁ)ᘁ)).hom.f := by
  dsimp only
  let u (W : CategoryTheory.Center D) : W.1 ⟶ ((Wᘁ)ᘁ).1 :=
    (p.iso W.1).hom ≫ (forgetDoubleDualIso W).inv
  have hu (X Y : CategoryTheory.Center D) :
      u (X ⊗ Y) = (u X ⊗ₘ u Y) ≫ (Dimensions.doubleDualTensorIso X Y).hom.f := by
    convert (transported_pivotal_tensor p X Y).symm using 1 <;> rfl
  let b := (β_ Z B).hom
  have hn : b.f ≫ u (B ⊗ Z) = u (Z ⊗ B) ≫ ((bᘁ)ᘁ).f :=
    by simpa [u, Category.assoc] using transported_pivotal_natural p b
  rw [hu, hu] at hn
  have hb := congrArg CategoryTheory.Center.Hom.f (Dimensions.doubleDualTensorIso_braiding Z B)
  simp only [CategoryTheory.Center.comp_f] at hb
  change (Dimensions.doubleDualTensorIso Z B).hom.f ≫ ((bᘁ)ᘁ).f =
    (β_ ((Zᘁ)ᘁ) ((Bᘁ)ᘁ)).hom.f ≫ (Dimensions.doubleDualTensorIso B Z).hom.f at hb
  simp only [Category.assoc] at hn
  rw [hb] at hn
  let : IsIso (Dimensions.doubleDualTensorIso B Z).hom.f := by
    change IsIso ((CategoryTheory.Center.forget D).map (Dimensions.doubleDualTensorIso B Z).hom)
    infer_instance
  apply (cancel_mono (Dimensions.doubleDualTensorIso B Z).hom.f).1
  simpa [Category.assoc] using hn

/-- Every transported base pivotal component is a morphism in the actual centre. -/
theorem pivotalComponentsCentral_proved [BraidedCategory D] (p : Dimensions.PivotalStructure (C := D)) :
    PivotalComponentsCentral p := by
  intro Z T
  let F := CategoryTheory.Center.ofBraided D
  let B := F.obj T
  let u (W : CategoryTheory.Center D) : W.1 ⟶ ((Wᘁ)ᘁ).1 :=
    (p.iso W.1).hom ≫ (forgetDoubleDualIso W).inv
  have hc := transported_pivotal_braiding p Z B
  change (β_ Z B).hom.f ≫ (u B ⊗ₘ u Z) =
    (u Z ⊗ₘ u B) ≫ (β_ ((Zᘁ)ᘁ) ((Bᘁ)ᘁ)).hom.f at hc
  let j := (positivePivotalComponent p T).hom
  have hj : j.f = u B := by
    change _ = (p.iso T).hom ≫ (forgetDoubleDualIso B).inv
    exact positivePivotalComponent_forget p T
  let : IsIso (u B) := by
    rw [← hj]
    change IsIso ((CategoryTheory.Center.forget D).map j)
    infer_instance
  have hbeta := ((Zᘁ)ᘁ).2.naturality (u B)
  change (u Z ▷ T) ≫ (((Zᘁ)ᘁ).2.β T).hom =
    (Z.2.β T).hom ≫ (T ◁ u Z)
  apply (cancel_mono ((u B) ▷ ((Zᘁ)ᘁ).1)).1
  rw [tensorHom_def' (u B) (u Z), tensorHom_def (u Z) (u B)] at hc
  change (Z.2.β T).hom ≫ ((T ◁ u Z) ≫ u B ▷ ((Zᘁ)ᘁ).1) =
    ((u Z ▷ T) ≫ ((Zᘁ)ᘁ).1 ◁ u B) ≫
      (((Zᘁ)ᘁ).2.β ((Bᘁ)ᘁ).1).hom at hc
  change ((Zᘁ)ᘁ).1 ◁ u B ≫ (((Zᘁ)ᘁ).2.β ((Bᘁ)ᘁ).1).hom =
    (((Zᘁ)ᘁ).2.β T).hom ≫ u B ▷ ((Zᘁ)ᘁ).1 at hbeta
  simp only [Category.assoc, hbeta] at hc ⊢
  exact hc.symm
end PropertyF.Ground.CentreInduction

namespace PropertyF.Ground.CentreInduction
universe v u
set_option backward.isDefEq.respectTransparency false
variable {C : BraidedFusionCategory.{v,u}}
local notation "𝒵" => CategoryTheory.Center C.Obj
local notation "𝒵ᶠ" => Integrate.bundledCenter C
open CategoryTheory.Limits
attribute [local instance] Abelian.hasFiniteBiproducts

/-- A positive simple image centralizing the induced unit is the unit. -/
theorem positive_simple_centralizes_induced_unit {i : Fin (rank C)}
    (hcentral : Centre.Centralizes
      ((induction C).obj (𝟙_ C.Obj)) ((CategoryTheory.Center.ofBraided C.Obj).obj (simples C i))) :
    i = unitIndex C := by
  classical
  by_contra hi
  let X := 𝟙_ C.Obj
  let S := simples C i
  let V := inductionSummand C X
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
  let : Simple (Sᘁ) := simple_rightDual C S
  exact (exactPairing_ne_zero S (Sᘁ) (id_nonzero (Sᘁ))).1
    ((e.isZero_iff.mpr ((IsZero.iff_id_eq_zero _).2 hid)).eq_of_tgt _ _)

/-- Every transparent simple of the actual centre is the unit. -/
theorem center_transparent_simple_iso_unit {Z : 𝒵} [Simple Z]
    (hcentral : ∀ W : 𝒵, Centre.Centralizes Z W) :
    Nonempty (Z ≅ 𝟙_ (𝒵)) := by
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
  obtain rfl := positive_simple_centralizes_induced_unit
    (Centre.centralizes_symm (Centre.centralizes_of_iso_left e'.symm (hcentral _)))
  exact ⟨e' ≪≫ F.mapIso (unitIndex_iso C).some ≪≫ (CategoryTheory.Functor.Monoidal.εIso F).symm⟩

end PropertyF.Ground.CentreInduction
