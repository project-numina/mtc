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
theorem pivotalDimension_eq_fp {C : BraidedFusionCategory.{v,u}}
    {p : PivotalStructure (C := C.Obj)}
    (hsimple : PivotalHasFPDimensions C p)
    (X : C.Obj) : pivotalDimension C p X = (fpDimension C X : ℂ) := by
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

omit [RightRigidCategory D] in
set_option backward.isDefEq.respectTransparency false in
/-- Forgetting a centre dual pair gives a dual pair in the base category. -/
@[instance_reducible] def forgetPairing (Z : 𝒵) : ExactPairing Z.1 ((Zᘁ).1) where
  coevaluation' := (η_ Z (Zᘁ)).f
  evaluation' := (ε_ Z (Zᘁ)).f
  coevaluation_evaluation' := by
    have h := congrArg Center.Hom.f (ExactPairing.coevaluation_evaluation Z (Zᘁ))
    simpa only [Center.comp_f, Center.whiskerLeft_f,
      Center.whiskerRight_f, Center.associator_inv_f,
      Center.associator_hom_f, Center.rightUnitor_hom_f,
      Center.rightUnitor_inv_f, Center.leftUnitor_hom_f,
      Center.leftUnitor_inv_f] using h
  evaluation_coevaluation' := by
    have h := congrArg Center.Hom.f (ExactPairing.evaluation_coevaluation Z (Zᘁ))
    simpa only [Center.comp_f, Center.whiskerLeft_f,
      Center.whiskerRight_f, Center.associator_inv_f,
      Center.associator_hom_f, Center.rightUnitor_hom_f,
      Center.rightUnitor_inv_f, Center.leftUnitor_hom_f,
      Center.leftUnitor_inv_f] using h

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
    change u ≫ e'.hom = (p.iso Z.1).hom ≫ (rightDualIsoMap e.symm).inv
    apply (Iso.eq_comp_inv (rightDualIsoMap e.symm)).2
    simpa [PivotalCompatibleAt, forgetDoubleDualIso, rightDualIsoMap,
      e, e', u, Category.assoc] using hcompat
  have heval := rightDualIso_evaluation (forgetPairing (Zᘁ)) HasRightDual.exact
  change (e'.hom ▷ ((Zᘁ).1)) ≫ ε_ ((Zᘁ).1) (((Zᘁ).1)ᘁ) = (ε_ (Zᘁ) ((Zᘁ)ᘁ)).f at heval
  have ht := trace_change_rightDual (forgetPairing Z) HasRightDual.exact (p.iso Z.1).hom
  change (η_ Z (Zᘁ)).f ≫ (((p.iso Z.1).hom ≫ (e.homᘁ)) ⊗ₘ 𝟙 ((Zᘁ).1)) ≫
      ε_ ((Zᘁ).1) (((Zᘁ).1)ᘁ) =
    η_ Z.1 (Z.1ᘁ) ≫ ((p.iso Z.1).hom ⊗ₘ 𝟙 (Z.1ᘁ)) ≫ ε_ (Z.1ᘁ) ((Z.1ᘁ)ᘁ) at ht
  have hn : (pZ.rightTrace (𝟙 Z)).asHom.f =
      (η_ Z (Zᘁ)).f ≫ ((u ≫ e'.hom) ⊗ₘ 𝟙 ((Zᘁ).1)) ≫
        ε_ ((Zᘁ).1) (((Zᘁ).1)ᘁ) := by
    dsimp [PivotalStructure.rightTrace]
    simp only [Category.id_comp, tensorHom_def, whiskerLeft_id, Category.comp_id]
    rw [← heval]
    simp [comp_whiskerRight, Category.assoc, u]
  rw [hn, htrans, ht]
  simp [PivotalStructure.rightTrace]

section
variable (C : BraidedFusionCategory.{v,u})
local notation "𝒵ᶜ" => Center C.Obj

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
  have hbase : p.rightTrace (𝟙 (underlying C (𝟙_ C.Obj))) = 0 :=
    End.ext (by rw [← ht, hz]; rfl)
  have hd : pivotalDimension C p (underlying C (𝟙_ C.Obj)) =
      (globalFPDimension C : ℂ) := by
    rw [pivotalDimension_eq_fp hsimple, fpDimension_underlying, fpDimension_unit, mul_one]
  change unitScalar C (p.rightTrace (𝟙 (underlying C (𝟙_ C.Obj)))) = _ at hd
  rw [hbase] at hd
  have hne : (globalFPDimension C : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (lt_of_lt_of_le zero_lt_one (one_le_globalFPDimension C)))
  apply hne
  simpa only [Ground.unitScalar_eq_equiv, map_zero] using hd.symm

end

end PropertyF.Ground.CentreInduction
