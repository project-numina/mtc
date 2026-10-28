module
public import PropertyF.Ground.CentreInduction.PositivePivotal
public import PropertyF.Ground.CentreInduction.SecondTriangle
public import PropertyF.Ground.Centre.Basic
public import PropertyF.Ground.Dimensions.DualTensorNaturality
public import PropertyF.Ground.Dimensions.DualBraiding
public import PropertyF.Ground.Dimensions.DoubleDualMonoidal

open PropertyF.Ground.Dimensions

/-! The pivotal structure of the base lifts to the rigid centre. -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.BraidedCategory
namespace PropertyF.Ground.CentreInduction
universe v u
set_option backward.isDefEq.respectTransparency false
variable {D : Type u} [Category.{v} D] [MonoidalCategory D] [RightRigidCategory D]
  [RigidCategory (Center D)]
local notation "𝒵" => Center D
variable (p : PivotalStructure (C := D))

/-- Transported pivotal components respect the braiding between centre objects. -/
private theorem transported_pivotal_braiding (Z B : 𝒵) :
    let u := transportedPivotalHom p
    (β_ Z B).hom.f ≫ (u B ⊗ₘ u Z) =
      (u Z ⊗ₘ u B) ≫ (β_ ((Zᘁ)ᘁ) ((Bᘁ)ᘁ)).hom.f := by
  dsimp only
  let u := transportedPivotalHom p
  have hu (X Y : 𝒵) :
      u (X ⊗ Y) = (u X ⊗ₘ u Y) ≫ (doubleDualTensorIso X Y).hom.f :=
    (transported_pivotal_tensor p X Y).symm
  let b := (β_ Z B).hom
  have hn : b.f ≫ u (B ⊗ Z) = u (Z ⊗ B) ≫ ((bᘁ)ᘁ).f :=
    transported_pivotal_natural p b
  rw [hu, hu] at hn
  have hb := congrArg Center.Hom.f (doubleDualTensorIso_braiding Z B)
  dsimp only [Center.comp_f] at hb
  change (doubleDualTensorIso Z B).hom.f ≫ ((bᘁ)ᘁ).f =
    (β_ ((Zᘁ)ᘁ) ((Bᘁ)ᘁ)).hom.f ≫ (doubleDualTensorIso B Z).hom.f at hb
  simp only [Category.assoc] at hn
  rw [hb] at hn
  let : IsIso (doubleDualTensorIso B Z).hom.f := by
    change IsIso ((Center.forget D).map (doubleDualTensorIso B Z).hom)
    infer_instance
  apply (cancel_mono (doubleDualTensorIso B Z).hom.f).1
  simpa [Category.assoc] using hn

/-- Every transported base pivotal component is a morphism in the actual centre. -/
theorem pivotalComponentsCentral_proved [BraidedCategory D] :
    PivotalComponentsCentral p := by
  intro Z T
  let F := Center.ofBraided D
  let B := F.obj T
  let u := transportedPivotalHom p
  have hc := transported_pivotal_braiding p Z B
  dsimp only at hc
  let j := (positivePivotalComponent p T).hom
  have hj : j.f = u B := positivePivotalComponent_forget p T
  let : IsIso (u B) := by
    rw [← hj]
    change IsIso ((Center.forget D).map j)
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
local notation "𝒵" => Center C.Obj
local notation "𝒵ᶠ" => Integrate.bundledCenter C
open CategoryTheory.Limits
attribute [local instance] Abelian.hasFiniteBiproducts

/-- A positive simple image centralizing the induced unit is the unit. -/
theorem positive_simple_centralizes_induced_unit {i : Fin (rank C)}
    (hcentral : Centre.Centralizes
      ((induction C).obj (𝟙_ C.Obj)) ((Center.ofBraided C.Obj).obj (simples C i))) :
    i = unitIndex C := by
  by_contra hi
  let X := 𝟙_ C.Obj
  let S := simples C i
  let V := inductionSummand C X
  have hz : biproduct.ι V i ≫ (underlyingCounit C).app X = 0 :=
    (biproduct.ι_π_ne_assoc V hi _).trans zero_comp
  have hb : crossingCandidate C X S = (β_ S (underlying C X)).inv :=
    (Iso.comp_hom_eq_id (β_ S (underlying C X))).1 (congrArg Center.Hom.f hcentral)
  have hid : 𝟙 (V i) = 0 := by
    rw [← unit_diag C X i, unit_matrix_reduce, hb]
    dsimp only [underlying]
    rw [braiding_inv_naturality_left_assoc, ← whiskerLeft_comp, hz]
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
  let F := Center.ofBraided C.Obj
  let e := Centre.positiveIsoOfCentralizesNegative Z (fun X => hcentral ((Centre.negative C.Obj).obj X))
  let : F.PreservesMonomorphisms := ⟨fun f _ =>
    (Center.forget C.Obj).mono_of_mono_map (show Mono f from inferInstance)⟩
  let : Simple (F.obj Z.1) := Simple.of_iso e.symm
  let : Simple Z.1 := Functor.simple_of_simple_obj F Z.1
  obtain ⟨i, ⟨s⟩⟩ := exists_simple_iso C Z.1
  let e' : Z ≅ F.obj (simples C i) := e ≪≫ F.mapIso s
  obtain rfl := positive_simple_centralizes_induced_unit
    (Centre.centralizes_symm (Centre.centralizes_of_iso_left e'.symm (hcentral _)))
  exact ⟨e' ≪≫ F.mapIso (unitIndex_iso C).some ≪≫ (CategoryTheory.Functor.Monoidal.εIso F).symm⟩

end PropertyF.Ground.CentreInduction
