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
  [RightRigidCategory (Center D)]
local notation "𝒵" => Center D
variable (p : PivotalStructure (C := D))
local notation "u" => transportedPivotalHom p

/-- Transported pivotal components respect the braiding between centre objects. -/
private theorem transported_pivotal_braiding (Z B : 𝒵) :
    (β_ Z B).hom.f ≫ (u B ⊗ₘ u Z) =
      (u Z ⊗ₘ u B) ≫ (β_ ((Zᘁ)ᘁ) ((Bᘁ)ᘁ)).hom.f :=
  (cancel_mono ((Center.forget D).map (doubleDualTensorIso B Z).hom)).1 <| by
    have hb := congrArg Center.Hom.f (doubleDualTensorIso_braiding Z B)
    simp only [Center.comp_f] at hb
    simpa [← transported_pivotal_tensor, Category.assoc, hb] using
      transported_pivotal_natural p (β_ Z B).hom

omit [RightRigidCategory D] [RightRigidCategory (Center D)] in
/-- A braiding equation against a positive centre object, transported along a
split monomorphism, detects centrality of a map in the base category. -/
theorem central_of_positive_braiding [BraidedCategory D] {Z W B : 𝒵} {T : D}
    (f : Z.1 ⟶ W.1) (g : T ⟶ B.1) [IsSplitMono g]
    (h : (β_ Z ((Center.ofBraided D).obj T)).hom.f ≫ (g ⊗ₘ f) =
      (f ⊗ₘ g) ≫ (β_ W B).hom.f) :
    (f ▷ T) ≫ (W.2.β T).hom = (Z.2.β T).hom ≫ (T ◁ f) :=
  letI : IsSplitMono (g ▷ W.1) := inferInstanceAs (IsSplitMono ((tensorRight W.1).map g))
  (cancel_mono (g ▷ W.1)).1 <| by
    rw [tensorHom_def' g f, tensorHom_def f g] at h
    change (Z.2.β T).hom ≫ ((T ◁ f) ≫ g ▷ W.1) =
      ((f ▷ T) ≫ W.1 ◁ g) ≫ (W.2.β B.1).hom at h
    simpa only [Category.assoc, W.2.naturality g] using h.symm

/-- Every transported base pivotal component is a morphism in the actual centre. -/
theorem pivotalComponentsCentral_proved [BraidedCategory D] :
    PivotalComponentsCentral p := fun Z T ↦
  central_of_positive_braiding (u Z) (u ((Center.ofBraided D).obj T))
    (transported_pivotal_braiding p Z _)

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
    rw [← unit_diag X i, unit_matrix_reduce, hb]
    dsimp only [underlying]
    rw [braiding_inv_naturality_left_assoc, ← whiskerLeft_comp, hz]
    simp [monoidalComp]
  let : Simple S := simples_simple C i
  let e : S ⊗ (Sᘁ) ≅ V i := whiskerRightIso (ρ_ S).symm (Sᘁ)
  let : Simple (Sᘁ) := simple_rightDual S
  exact (exactPairing_ne_zero S (id_nonzero (Sᘁ))).1
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
