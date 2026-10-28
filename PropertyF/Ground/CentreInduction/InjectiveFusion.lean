module
public import PropertyF.Ground.CentreInduction.FiniteSimples
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic

/-! An injective-retract route to centre semisimplicity and fusion. -/
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
universe v u
@[expose] public noncomputable section
namespace PropertyF.Ground.CentreInduction
variable {D : Type u} [Category.{v} D] [Abelian D] [MonoidalCategory D] [LeftRigidCategory D]

omit [Abelian D] in
/-- Tensoring with any object preserves injectives in a left-rigid category. -/
theorem tensor_preserves_injective (J U : D) [Injective J] : Injective (J ⊗ U) :=
  letI : (tensorRight (ᘁU)).IsRightAdjoint :=
    ⟨⟨tensorRight (ᘁ(ᘁU)), ⟨tensorRightAdjunction (ᘁ(ᘁU)) (ᘁU)⟩⟩⟩
  (tensorRightAdjunction (ᘁU) U).map_injective J inferInstance

omit [Abelian D] in
/-- A unit retract of a tensor product with an injective makes every object injective. -/
theorem all_injective_of_unit_retract {J U : D} [Injective J]
    (r : Retract (𝟙_ D) (J ⊗ U)) (X : D) : Injective X :=
  letI : Injective (J ⊗ U) := tensor_preserves_injective J U
  letI : Injective (𝟙_ D) := r.injective
  Injective.of_iso (λ_ X) (tensor_preserves_injective (𝟙_ D) X)

variable (C : BraidedFusionCategory.{v,u}) [RigidCategory (Center C.Obj)]
local notation "𝒵" => Center C.Obj
variable {X : C.Obj}

set_option backward.isDefEq.respectTransparency false in
/-- Under the unit-retract condition every centre object is a finite simple sum. -/
theorem center_finite_simple_sum_of_unit_retract {U : 𝒵}
    (r : Retract (𝟙_ (𝒵)) ((induction C).obj X ⊗ U))
    (Z : 𝒵) : FiniteSimpleSum (𝒵) Z :=
  letI (W : 𝒵) : IsArtinianObject W := center_artinian C W
  letI : Injective ((induction C).obj X) := (actualAdjunction C).map_injective X (object_injective X)
  letI (W : 𝒵) : Injective W := all_injective_of_unit_retract r W
  letI (A : 𝒵) : FiniteDimensional ℂ (A ⟶ A) :=
    letI : FiniteDimensional ℂ (A.1 ⟶ A.1) := IsFusionCategory.hom_finite _ _
    Centre.finiteDimensional_hom ℂ A A
  finiteSimpleSum_of_injective (k := ℂ) (fun {_} hW =>
    ⟨simpleSubobject hW, simpleSubobjectArrow hW, inferInstance, inferInstance⟩) Z

/-- Centre rigidity and the explicit unit retract imply centre fusion. -/
theorem center_fusion_of_unit_retract {U : 𝒵}
    (r : Retract (𝟙_ (𝒵)) ((induction C).obj X ⊗ U)) :
    IsFusionCategory (𝒵) :=
  let ⟨_, hsimple, hcover⟩ := finite_simple_labels C
  let ⟨n, S, hS, hinj, hcover⟩ := simple_representatives_of_finite_cover hsimple hcover
  CentreBundle.fusionOfFiniteSemisimple C ⟨n, S, hS, hinj, fun Z =>
    let ⟨_, V, hV, ⟨e⟩⟩ := finiteSimpleSum_biproduct (center_finite_simple_sum_of_unit_retract C r Z)
    let ⟨m, ⟨a⟩⟩ := regroup_biproduct (fun j => hcover (V j) (hV j))
    ⟨m, ⟨e ≪≫ a⟩⟩⟩

set_option backward.isDefEq.respectTransparency false in
/-- A cap with nonzero unit composite gives a unit retract. -/
def unitRetractOfNonzeroCap {D : Type u} [Category.{v} D] [MonoidalCategory D]
    [RightRigidCategory D] [Preadditive D] [HasKernels D] [Simple (𝟙_ D)]
    {J : D} (cap : J ⊗ Jᘁ ⟶ 𝟙_ D) (hne : η_ J (Jᘁ) ≫ cap ≠ 0) :
    Retract (𝟙_ D) (J ⊗ Jᘁ) :=
  letI : IsIso (η_ J (Jᘁ) ≫ cap) := isIso_of_hom_simple hne
  { i := η_ J (Jᘁ), r := cap ≫ inv (η_ J (Jᘁ) ≫ cap)
    retract := (Category.assoc _ _ _).symm.trans (IsIso.hom_inv_id _) }

set_option backward.isDefEq.respectTransparency false in
/-- A centre pivotal structure with nonzero trace on an induced object implies fusion. -/
theorem center_fusion_of_nonzero_induced_trace (X : C.Obj)
    (p : Dimensions.PivotalStructure (C := 𝒵))
    (hne : p.rightTrace (𝟙 ((induction C).obj X)) ≠ 0) :
    IsFusionCategory (𝒵) :=
  let J := (induction C).obj X
  let cap : J ⊗ Jᘁ ⟶ 𝟙_ (𝒵) :=
    ((p.iso J).hom ⊗ₘ 𝟙 (Jᘁ)) ≫ ε_ (Jᘁ) ((Jᘁ)ᘁ)
  letI : Simple (𝟙_ C.Obj) := IsFusionCategory.unit_simple
  letI : Simple (𝟙_ (𝒵)) := Centre.centerUnitSimple
  center_fusion_of_unit_retract C <| unitRetractOfNonzeroCap cap <| fun h =>
    hne (End.ext (by simpa [Dimensions.PivotalStructure.rightTrace, Dimensions.rightTraceWith,
      cap, J, Category.assoc] using h))

end PropertyF.Ground.CentreInduction
