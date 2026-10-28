module
public import PropertyF.Ground.CentreInduction.FiniteSimples
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic

/-! An injective-retract route to centre semisimplicity and fusion. -/
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
universe v u
@[expose] public noncomputable section
namespace PropertyF.Ground.CentreInduction
variable {D : Type u} [Category.{v} D] [Abelian D] [MonoidalCategory D] [RigidCategory D]

omit [Abelian D] in
/-- Tensoring with any object preserves injectives in a rigid category. -/
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

set_option backward.isDefEq.respectTransparency false in
/-- Under the unit-retract condition every centre object is a finite simple sum. -/
theorem center_finite_simple_sum_of_unit_retract {X : C.Obj} {U : 𝒵}
    (r : Retract (𝟙_ (𝒵)) ((induction C).obj X ⊗ U))
    (Z : 𝒵) : FiniteSimpleSum (𝒵) Z := by
  let (W : 𝒵) : IsArtinianObject W := center_artinian C W
  let : Injective ((induction C).obj X) := (actualAdjunction C).map_injective X (object_injective C X)
  let (W : 𝒵) : Injective W := all_injective_of_unit_retract r W
  let (A B : 𝒵) : FiniteDimensional ℂ (A ⟶ B) := by
    let : FiniteDimensional ℂ (A.1 ⟶ B.1) := IsFusionCategory.hom_finite _ _
    exact Centre.finiteDimensional_hom ℂ A B
  apply finiteSimpleSum_of_injective (k := ℂ) ?_ Z
  intro W hW
  obtain ⟨P, hP⟩ := exists_simple_subobject hW
  exact ⟨P, P.arrow, hP, inferInstance⟩

/-- Centre rigidity and the explicit unit retract imply centre fusion. -/
theorem center_fusion_of_unit_retract {X : C.Obj} {U : 𝒵}
    (r : Retract (𝟙_ (𝒵)) ((induction C).obj X ⊗ U)) :
    IsFusionCategory (𝒵) := by
  obtain ⟨labels, hsimple, hcover⟩ := finite_simple_labels C
  obtain ⟨n, S, hS, hinj, hcover⟩ := simple_representatives_of_finite_cover hsimple hcover
  refine CentreBundle.fusionOfFiniteSemisimple C ⟨n, S, hS, hinj, ?_⟩
  intro Z
  obtain ⟨k, V, hV, ⟨e⟩⟩ := finiteSimpleSum_biproduct (center_finite_simple_sum_of_unit_retract C r Z)
  obtain ⟨m, ⟨a⟩⟩ := regroup_biproduct (fun j => hcover (V j) (hV j))
  exact ⟨m, ⟨e ≪≫ a⟩⟩

set_option backward.isDefEq.respectTransparency false in
/-- A cap with nonzero unit composite gives a unit retract. -/
def unitRetractOfNonzeroCap {D : Type u} [Category.{v} D] [MonoidalCategory D]
    [RightRigidCategory D] [Preadditive D] [HasKernels D] [Simple (𝟙_ D)]
    {J : D} (cap : J ⊗ Jᘁ ⟶ 𝟙_ D) (hne : η_ J (Jᘁ) ≫ cap ≠ 0) :
    Retract (𝟙_ D) (J ⊗ Jᘁ) := by
  letI : IsIso (η_ J (Jᘁ) ≫ cap) := isIso_of_hom_simple hne
  refine { i := η_ J (Jᘁ), r := cap ≫ inv (η_ J (Jᘁ) ≫ cap), retract := ?_ }
  simp only [← Category.assoc, IsIso.hom_inv_id]

set_option backward.isDefEq.respectTransparency false in
/-- A centre pivotal structure with nonzero trace on an induced object implies fusion. -/
theorem center_fusion_of_nonzero_induced_trace (X : C.Obj)
    (p : Dimensions.PivotalStructure (C := 𝒵))
    (hne : p.rightTrace (𝟙 ((induction C).obj X)) ≠ 0) :
    IsFusionCategory (𝒵) := by
  let J := (induction C).obj X
  let cap : J ⊗ Jᘁ ⟶ 𝟙_ (𝒵) :=
    ((p.iso J).hom ⊗ₘ 𝟙 (Jᘁ)) ≫ ε_ (Jᘁ) ((Jᘁ)ᘁ)
  let : Simple (𝟙_ C.Obj) := IsFusionCategory.unit_simple
  let : Simple (𝟙_ (𝒵)) := Centre.centerUnitSimple
  apply center_fusion_of_unit_retract C
  apply unitRetractOfNonzeroCap cap
  intro h
  apply hne
  apply End.ext
  simpa [Dimensions.PivotalStructure.rightTrace, cap, J, Category.assoc] using h

end PropertyF.Ground.CentreInduction
