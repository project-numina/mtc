module
public import PropertyF.Ground.CentreInduction.InjectiveFusion
public import PropertyF.Ground.Dimensions.IntrinsicNonzero

section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open scoped BigOperators
universe v u
@[expose] public noncomputable section
namespace PropertyF.Ground.CentreInduction
variable (C : BraidedFusionCategory.{v,u})
local notation "𝒵" => CategoryTheory.Center C.Obj

/-- A pivotal structure has the Frobenius–Perron dimensions on simple objects. -/
abbrev PivotalHasFPDimensions (p : Dimensions.PivotalStructure (C := C.Obj)) : Prop :=
  ∀ i, Dimensions.pivotalDimension C p (simples C i) = (fpSimple C i : ℂ)

/-- Agreement with FP dimension on simples extends to all objects. -/
theorem pivotalDimension_eq_fp {C : BraidedFusionCategory.{v,u}}
    {p : Dimensions.PivotalStructure (C := C.Obj)}
    (hsimple : PivotalHasFPDimensions C p)
    (X : C.Obj) : Dimensions.pivotalDimension C p X = (fpDimension C X : ℂ) := by
  rw [Dimensions.pivotalDimension_decomposition]
  simp only [fpDimension, Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_natCast, hsimple]

/-- The induction of the tensor unit has base pivotal dimension FPdim(C). -/
theorem induced_unit_dimension {C : BraidedFusionCategory.{v,u}}
    {p : Dimensions.PivotalStructure (C := C.Obj)}
    (hsimple : PivotalHasFPDimensions C p) :
    Dimensions.pivotalDimension C p (underlying C (𝟙_ C.Obj)) = (globalFPDimension C : ℂ) := by
  rw [pivotalDimension_eq_fp hsimple, fpDimension_underlying, fpDimension_unit, mul_one]

set_option backward.isDefEq.respectTransparency false in
/-- The displayed trace compatibility makes the induced unit trace nonzero. -/
theorem induced_center_trace_ne_zero_of_compatible {p : Dimensions.PivotalStructure (C := C.Obj)}
    (hsimple : PivotalHasFPDimensions C p)
    [RigidCategory (𝒵)]
    {pZ : Dimensions.PivotalStructure (C := 𝒵)}
    (hcompat : (pZ.rightTrace (𝟙 ((induction C).obj (𝟙_ C.Obj)))).asHom.f =
      (p.rightTrace (𝟙 (underlying C (𝟙_ C.Obj)))).asHom) :
    pZ.rightTrace (𝟙 ((induction C).obj (𝟙_ C.Obj))) ≠ 0 := by
  intro hz
  have hbase : (p.rightTrace (𝟙 (underlying C (𝟙_ C.Obj)))) = 0 := by
    apply End.ext
    rw [← hcompat, hz]
    rfl
  have hd := induced_unit_dimension hsimple
  change unitScalar C (p.rightTrace (𝟙 (underlying C (𝟙_ C.Obj)))) = _ at hd
  rw [hbase] at hd
  have hne : (globalFPDimension C : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (lt_of_lt_of_le zero_lt_one (one_le_globalFPDimension C)))
  apply hne
  simpa only [Ground.unitScalar_eq_equiv, map_zero] using hd.symm


set_option backward.isDefEq.respectTransparency false in
/-- A compatible centre pivotal structure constructs centre fusion when
base pivotal dimensions equal FP dimensions. -/
theorem center_fusion_of_compatible_pivotal {p : Dimensions.PivotalStructure (C := C.Obj)}
    (hsimple : PivotalHasFPDimensions C p)
    [RigidCategory (𝒵)]
    {pZ : Dimensions.PivotalStructure (C := 𝒵)}
    (hcompat : (pZ.rightTrace (𝟙 ((induction C).obj (𝟙_ C.Obj)))).asHom.f =
      (p.rightTrace (𝟙 (underlying C (𝟙_ C.Obj)))).asHom) :
    IsFusionCategory (𝒵) :=
  center_fusion_of_nonzero_induced_trace C (𝟙_ C.Obj) pZ
    (induced_center_trace_ne_zero_of_compatible C hsimple hcompat)



end PropertyF.Ground.CentreInduction

end
end

/-! Transport duality through centre forget and reduce fusion to one component. -/
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
universe v u
@[expose] public noncomputable section
namespace PropertyF.Ground.CentreInduction
variable {D : Type u} [Category.{v} D] [MonoidalCategory D] [RightRigidCategory D]
  [RigidCategory (CategoryTheory.Center D)]
local notation "𝒵" => CategoryTheory.Center D

omit [RightRigidCategory D] in
set_option backward.isDefEq.respectTransparency false in
/-- Forgetting a centre dual pair gives a dual pair in the base category. -/
@[instance_reducible] def forgetPairing (Z : 𝒵) : ExactPairing Z.1 ((Zᘁ).1) where
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
def forgetDualIso (Z : 𝒵) : ((Zᘁ).1) ≅ (Z.1ᘁ) :=
  rightDualIso (forgetPairing Z) HasRightDual.exact

/-- Compare the underlying centre double dual with the chosen base double dual. -/
def forgetDoubleDualIso (Z : 𝒵) : (((Zᘁ)ᘁ).1) ≅ ((Z.1ᘁ)ᘁ) :=
  forgetDualIso (Zᘁ) ≪≫ Dimensions.rightDualIsoMap (forgetDualIso Z).symm

set_option backward.isDefEq.respectTransparency false in
/-- Compatible pivotal components have equal traces after forgetting. -/
theorem forget_trace_of_pivotal_component
    {p : Dimensions.PivotalStructure (C := D)}
    {pZ : Dimensions.PivotalStructure (C := 𝒵)}
    {Z : 𝒵}
    (hcompat : ((pZ.iso Z).hom.f) ≫ (forgetDoubleDualIso Z).hom = (p.iso Z.1).hom) :
    (pZ.rightTrace (𝟙 Z)).asHom.f = (p.rightTrace (𝟙 Z.1)).asHom := by
  let e := forgetDualIso Z
  let e' := forgetDualIso (Zᘁ)
  let u : Z.1 ⟶ ((Zᘁ)ᘁ).1 := (pZ.iso Z).hom.f
  have hu : u ≫ e'.hom ≫ (e.invᘁ) = (p.iso Z.1).hom := by
    simpa [forgetDoubleDualIso, Dimensions.rightDualIsoMap, e, e', u, Category.assoc] using hcompat
  have htrans : u ≫ e'.hom = (p.iso Z.1).hom ≫ (e.homᘁ) := by
    rw [← hu]
    simp only [Category.assoc, ← comp_rightAdjointMate, Iso.hom_inv_id,
      rightAdjointMate_id, Category.comp_id]
  have heval := Dimensions.rightDualIso_evaluation (forgetPairing (Zᘁ)) HasRightDual.exact
  change (e'.hom ▷ ((Zᘁ).1)) ≫ ε_ ((Zᘁ).1) (((Zᘁ).1)ᘁ) = (ε_ (Zᘁ) ((Zᘁ)ᘁ)).f at heval
  have ht := Dimensions.trace_change_rightDual (forgetPairing Z) HasRightDual.exact (p.iso Z.1).hom
  change (η_ Z (Zᘁ)).f ≫ (((p.iso Z.1).hom ≫ (e.homᘁ)) ⊗ₘ 𝟙 ((Zᘁ).1)) ≫
      ε_ ((Zᘁ).1) (((Zᘁ).1)ᘁ) =
    η_ Z.1 (Z.1ᘁ) ≫ ((p.iso Z.1).hom ⊗ₘ 𝟙 (Z.1ᘁ)) ≫ ε_ (Z.1ᘁ) ((Z.1ᘁ)ᘁ) at ht
  have hn : (pZ.rightTrace (𝟙 Z)).asHom.f =
      (η_ Z (Zᘁ)).f ≫ ((u ≫ e'.hom) ⊗ₘ 𝟙 ((Zᘁ).1)) ≫
        ε_ ((Zᘁ).1) (((Zᘁ).1)ᘁ) := by
    dsimp [Dimensions.PivotalStructure.rightTrace]
    simp only [Category.id_comp, tensorHom_def, whiskerLeft_id, Category.comp_id]
    rw [← heval]
    simp [comp_whiskerRight, Category.assoc, u]
  rw [hn, htrans, ht]
  simp [Dimensions.PivotalStructure.rightTrace]






end PropertyF.Ground.CentreInduction
