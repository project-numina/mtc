module
public import Mathlib.CategoryTheory.Monoidal.Center
public import PropertyF.Ground.Dimensions.DualCoherence
public import PropertyF.Ground.Dimensions.Trace

open PropertyF.Ground.Dimensions

/-! # Forgetting centre duals

The centre forgetful functor transports dual pairings to the base category.
The resulting dual comparisons identify traces of compatible pivotal components.
-/
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
universe v u
@[expose] public noncomputable section
namespace PropertyF.Ground.CentreInduction
variable {D : Type u} [Category.{v} D] [MonoidalCategory D] [RightRigidCategory D]
  [RightRigidCategory (Center D)]
local notation "𝒵" => Center D

omit [RightRigidCategory D] [RightRigidCategory (Center D)] in
set_option backward.isDefEq.respectTransparency false in
/-- Forgetting a centre pairing gives a pairing in the base category. -/
@[instance_reducible] def forgetPairingOf {Z W : Center D} (p : ExactPairing Z W) :
    ExactPairing Z.1 W.1 :=
  letI := p
  { coevaluation' := (η_ Z W).f
    evaluation' := (ε_ Z W).f
    coevaluation_evaluation' := by
      simpa [-ExactPairing.coevaluation_evaluation] using
        congrArg Center.Hom.f (ExactPairing.coevaluation_evaluation Z W)
    evaluation_coevaluation' := by
      simpa [-ExactPairing.evaluation_coevaluation] using
        congrArg Center.Hom.f (ExactPairing.evaluation_coevaluation Z W) }

omit [RightRigidCategory D] in
/-- Forgetting a centre dual pair gives a dual pair in the base category. -/
@[instance_reducible] def forgetPairing (Z : 𝒵) : ExactPairing Z.1 ((Zᘁ).1) :=
  forgetPairingOf HasRightDual.exact

omit [RightRigidCategory D] [RightRigidCategory (Center D)] in
set_option backward.isDefEq.respectTransparency false in
/-- Forgetting commutes with comparing two pairings when their coevaluations agree. -/
theorem forget_rightDualIso {Z A B : Center D} (p : ExactPairing Z A) (q : ExactPairing Z B)
    (r : ExactPairing Z.1 B.1)
    (hc : (@ExactPairing.coevaluation (Center D) _ _ Z B q).f =
      @ExactPairing.coevaluation D _ _ Z.1 B.1 r) :
    (rightDualIso p q).hom.f = (rightDualIso (forgetPairingOf p) r).hom := by
  simp [rightDualIso, rightAdjointMate, hc]
  rfl

/-- Compare the underlying centre dual with the chosen base dual. -/
def forgetDualIso (Z : 𝒵) : ((Zᘁ).1) ≅ (Z.1ᘁ) :=
  rightDualIso (forgetPairing Z) HasRightDual.exact

/-- Compare the underlying centre double dual with the chosen base double dual. -/
def forgetDoubleDualIso (Z : 𝒵) : (((Zᘁ)ᘁ).1) ≅ ((Z.1ᘁ)ᘁ) :=
  forgetDualIso (Zᘁ) ≪≫ rightDualIsoMap (forgetDualIso Z).symm

/-- A centre pivotal component agrees with the base component after forgetting. -/
abbrev PivotalCompatibleAt (p : PivotalStructure (C := D))
    (pZ : PivotalStructure (C := 𝒵)) (Z : 𝒵) : Prop :=
  (pZ.iso Z).hom.f ≫ (forgetDoubleDualIso Z).hom = (p.iso Z.1).hom

set_option backward.isDefEq.respectTransparency false in
/-- Compatible double-dual isomorphisms have equal traces after forgetting. -/
theorem forget_rightTraceWith {Z : 𝒵} {j : Z.1 ≅ ((Z.1ᘁ)ᘁ)}
    {jZ : Z ≅ ((Zᘁ)ᘁ)}
    (hcompat : jZ.hom.f ≫ (forgetDoubleDualIso Z).hom = j.hom) (f : Z ⟶ Z) :
    (rightTraceWith jZ f).asHom.f = (rightTraceWith j f.f).asHom := by
  let e := forgetDualIso Z
  let e' := forgetDualIso (Zᘁ)
  let u : Z.1 ⟶ ((Zᘁ)ᘁ).1 := jZ.hom.f
  have htrans : u ≫ e'.hom = j.hom ≫ (e.homᘁ) := by
    apply (Iso.eq_comp_inv (rightDualIsoMap e.symm)).2
    simpa [forgetDoubleDualIso, rightDualIsoMap,
      e, e', u, Category.assoc] using hcompat
  have heval : (e'.hom ▷ ((Zᘁ).1)) ≫ ε_ ((Zᘁ).1) (((Zᘁ).1)ᘁ) = (ε_ (Zᘁ) ((Zᘁ)ᘁ)).f :=
    rightDualIso_evaluation (forgetPairing (Zᘁ)) HasRightDual.exact
  have hn : (rightTraceWith jZ f).asHom.f =
      (η_ Z (Zᘁ)).f ≫ ((f.f ≫ u ≫ e'.hom) ⊗ₘ 𝟙 ((Zᘁ).1)) ≫
        ε_ ((Zᘁ).1) (((Zᘁ).1)ᘁ) := by
    simp [rightTraceWith, tensorHom_def, ← heval,
      comp_whiskerRight, Category.assoc, u]
  rw [hn, htrans, ← Category.assoc f.f j.hom (e.homᘁ)]
  erw [trace_change_rightDual (forgetPairing Z) HasRightDual.exact (f.f ≫ j.hom)]
  rfl

end PropertyF.Ground.CentreInduction
