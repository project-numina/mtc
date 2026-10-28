module
public import PropertyF.Ground.CentreInduction.InjectiveFusion
public import PropertyF.Ground.Dimensions.DimensionCharacter
public import PropertyF.Ground.Integrate.CharacterReality
public import PropertyF.Ground.Modular.SMatrix

open PropertyF.Ground.Dimensions

section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open scoped BigOperators
universe v u
@[expose] public noncomputable section
namespace PropertyF.Ground.CentreInduction
variable (C : BraidedFusionCategory.{v,u})
local notation "𝒵" => Center C.Obj

/-- A pivotal structure has the Frobenius–Perron dimensions on simple objects. -/
abbrev PivotalHasFPDimensions (p : PivotalStructure (C := C.Obj)) : Prop :=
  ∀ i, pivotalDimension C p (simples C i) = (fpSimple C i : ℂ)

/-- Agreement with FP dimension on simples extends to all objects. -/
theorem pivotalDimension_eq_fp {C : BraidedFusionCategory.{v,u}} {p : PivotalStructure (C := C.Obj)}
    (hsimple : PivotalHasFPDimensions C p) (X : C.Obj) :
    pivotalDimension C p X = (fpDimension C X : ℂ) := by
  simpa only [fpDimension, Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_natCast,
    hsimple] using pivotalDimension_decomposition C p X


end PropertyF.Ground.CentreInduction

end
end

/-! Transport duality through centre forget and reduce fusion to one component. -/
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
universe v u
@[expose] public noncomputable section
namespace PropertyF.Ground.CentreInduction
variable {D : Type u} [Category.{v} D] [MonoidalCategory D] [RightRigidCategory D]
  [RigidCategory (Center D)]
local notation "𝒵" => Center D

omit [RightRigidCategory D] [RigidCategory (Center D)] in
set_option backward.isDefEq.respectTransparency false in
/-- Forgetting a centre pairing gives a pairing in the base category. -/
@[instance_reducible] def forgetPairingOf {Z W : Center D} (p : ExactPairing Z W) :
    ExactPairing Z.1 W.1 :=
  letI := p
  { coevaluation' := (η_ Z W).f
    evaluation' := (ε_ Z W).f
    coevaluation_evaluation' := by
      simpa only [Center.comp_f, Center.whiskerLeft_f,
        Center.whiskerRight_f, Center.associator_inv_f,
        Center.associator_hom_f, Center.rightUnitor_hom_f,
        Center.rightUnitor_inv_f, Center.leftUnitor_hom_f,
        Center.leftUnitor_inv_f] using
          congrArg Center.Hom.f (ExactPairing.coevaluation_evaluation Z W)
    evaluation_coevaluation' := by
      simpa only [Center.comp_f, Center.whiskerLeft_f,
        Center.whiskerRight_f, Center.associator_inv_f,
        Center.associator_hom_f, Center.rightUnitor_hom_f,
        Center.rightUnitor_inv_f, Center.leftUnitor_hom_f,
        Center.leftUnitor_inv_f] using
          congrArg Center.Hom.f (ExactPairing.evaluation_coevaluation Z W) }

omit [RightRigidCategory D] in
/-- Forgetting a centre dual pair gives a dual pair in the base category. -/
@[instance_reducible] def forgetPairing (Z : 𝒵) : ExactPairing Z.1 ((Zᘁ).1) :=
  forgetPairingOf HasRightDual.exact

omit [RightRigidCategory D] [RigidCategory (Center D)] in
set_option backward.isDefEq.respectTransparency false in
/-- Forgetting commutes with comparing two pairings when their coevaluations agree. -/
theorem forget_rightDualIso {Z A B : Center D} (p : ExactPairing Z A) (q : ExactPairing Z B)
    (r : ExactPairing Z.1 B.1)
    (hc : (@ExactPairing.coevaluation (Center D) _ _ Z B q).f =
      @ExactPairing.coevaluation D _ _ Z.1 B.1 r) :
    (rightDualIso p q).hom.f = (rightDualIso (forgetPairingOf p) r).hom := by
  unfold rightDualIso rightAdjointMate
  simp only [Center.comp_f, Center.rightUnitor_inv_f, Center.leftUnitor_hom_f,
    Center.whiskerLeft_f, Center.whiskerRight_f, Center.associator_inv_f, Center.id_f, hc]
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
/-- Compatible pivotal components have equal traces after forgetting. -/
theorem forget_trace_of_pivotal_component
    {p : PivotalStructure (C := D)} {pZ : PivotalStructure (C := 𝒵)} {Z : 𝒵}
    (hcompat : PivotalCompatibleAt p pZ Z) :
    (pZ.rightTrace (𝟙 Z)).asHom.f = (p.rightTrace (𝟙 Z.1)).asHom := by
  let e := forgetDualIso Z
  let e' := forgetDualIso (Zᘁ)
  let u : Z.1 ⟶ ((Zᘁ)ᘁ).1 := (pZ.iso Z).hom.f
  have htrans : u ≫ e'.hom = (p.iso Z.1).hom ≫ (e.homᘁ) := by
    apply (Iso.eq_comp_inv (rightDualIsoMap e.symm)).2
    simpa [PivotalCompatibleAt, forgetDoubleDualIso, rightDualIsoMap,
      e, e', u, Category.assoc] using hcompat
  have heval : (e'.hom ▷ ((Zᘁ).1)) ≫ ε_ ((Zᘁ).1) (((Zᘁ).1)ᘁ) = (ε_ (Zᘁ) ((Zᘁ)ᘁ)).f :=
    rightDualIso_evaluation (forgetPairing (Zᘁ)) HasRightDual.exact
  have ht : (η_ Z (Zᘁ)).f ≫ (((p.iso Z.1).hom ≫ (e.homᘁ)) ⊗ₘ 𝟙 ((Zᘁ).1)) ≫
      ε_ ((Zᘁ).1) (((Zᘁ).1)ᘁ) =
    η_ Z.1 (Z.1ᘁ) ≫ ((p.iso Z.1).hom ⊗ₘ 𝟙 (Z.1ᘁ)) ≫ ε_ (Z.1ᘁ) ((Z.1ᘁ)ᘁ) :=
    trace_change_rightDual (forgetPairing Z) HasRightDual.exact (p.iso Z.1).hom
  have hn : (pZ.rightTrace (𝟙 Z)).asHom.f =
      (η_ Z (Zᘁ)).f ≫ ((u ≫ e'.hom) ⊗ₘ 𝟙 ((Zᘁ).1)) ≫
        ε_ ((Zᘁ).1) (((Zᘁ).1)ᘁ) := by
    dsimp [PivotalStructure.rightTrace, rightTraceWith]
    simp only [Category.id_comp, tensorHom_def, whiskerLeft_id, Category.comp_id]
    rw [← heval]
    simp [comp_whiskerRight, Category.assoc, u]
  rw [hn, htrans, ht]
  simp [PivotalStructure.rightTrace, rightTraceWith]

section
variable (C : BraidedFusionCategory.{v,u})
local notation "𝒵ᶜ" => Center C.Obj

/-- The pivotal dimension of the underlying induced unit is the global FP dimension. -/
theorem pivotalDimension_underlying_unit {p : PivotalStructure (C := C.Obj)}
    (hsimple : PivotalHasFPDimensions C p) :
    pivotalDimension C p (underlying C (𝟙_ C.Obj)) = (globalFPDimension C : ℂ) := by
  rw [pivotalDimension_eq_fp hsimple, fpDimension_underlying, fpDimension_unit, mul_one]

/-- A compatible centre pivotal structure constructs centre fusion when the base
pivotal dimensions equal FP dimensions. -/
theorem center_fusion_of_compatible_pivotal {p : PivotalStructure (C := C.Obj)}
    (hsimple : PivotalHasFPDimensions C p) [RigidCategory 𝒵ᶜ]
    {pZ : PivotalStructure (C := 𝒵ᶜ)}
    (hcompat : PivotalCompatibleAt p pZ ((induction C).obj (𝟙_ C.Obj))) : IsFusionCategory 𝒵ᶜ := by
  apply center_fusion_of_nonzero_induced_trace C (𝟙_ C.Obj) pZ
  intro hz
  have ht := forget_trace_of_pivotal_component hcompat
  change (pZ.rightTrace (𝟙 ((induction C).obj (𝟙_ C.Obj)))).asHom.f =
    (p.rightTrace (𝟙 (underlying C (𝟙_ C.Obj)))).asHom at ht
  have hd := pivotalDimension_underlying_unit C hsimple
  change unitScalar C (p.rightTrace (𝟙 (underlying C (𝟙_ C.Obj)))) = _ at hd
  rw [show p.rightTrace (𝟙 (underlying C (𝟙_ C.Obj))) = 0 from
    End.ext (ht.symm.trans (congrArg (fun a => a.asHom.f) hz))] at hd
  exact (Complex.ofReal_ne_zero.mpr
    (ne_of_gt (lt_of_lt_of_le zero_lt_one (one_le_globalFPDimension C)))) <|
      by simpa only [Ground.unitScalar_eq_equiv, map_zero] using hd.symm

end

end PropertyF.Ground.CentreInduction
