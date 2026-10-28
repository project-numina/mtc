module
public import PropertyF.Ground.CentreInduction.FiniteSimples
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic

section
open CategoryTheory CategoryTheory.Limits
universe v u
@[expose] public noncomputable section
namespace PropertyF.Ground.CentreInduction
variable (C : BraidedFusionCategory.{v,u})

/-- Induction sends every base object to an injective centre object. -/
theorem induction_injective (X : C.Obj) : Injective ((induction C).obj X) :=
  (actualAdjunction C).map_injective X (object_injective C X)



end PropertyF.Ground.CentreInduction

end
end

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
  letI : Injective ((𝟙_ D) ⊗ X) := tensor_preserves_injective (𝟙_ D) X
  Injective.of_iso (λ_ X) inferInstance



variable (C : BraidedFusionCategory.{v,u}) [RigidCategory (CategoryTheory.Center C.Obj)]
local notation "𝒵" => CategoryTheory.Center C.Obj

/-- A unit retract of an induced object makes every centre object injective. -/
theorem center_all_injective_of_unit_retract {X : C.Obj} {U : 𝒵}
    (r : Retract (𝟙_ (𝒵)) ((induction C).obj X ⊗ U))
    (Z : 𝒵) : Injective Z :=
  letI : Injective ((induction C).obj X) := induction_injective C X
  all_injective_of_unit_retract r Z

set_option backward.isDefEq.respectTransparency false in
/-- Under the unit-retract condition every centre object is a finite simple sum. -/
theorem center_finite_simple_sum_of_unit_retract {X : C.Obj} {U : 𝒵}
    (r : Retract (𝟙_ (𝒵)) ((induction C).obj X ⊗ U))
    (Z : 𝒵) : FiniteSimpleSum (𝒵) Z := by
  let (W : 𝒵) : IsArtinianObject W := center_artinian C W
  let (W : 𝒵) : Injective W := center_all_injective_of_unit_retract C r W
  let (A B : 𝒵) : FiniteDimensional ℂ (A ⟶ B) := by
    let : FiniteDimensional ℂ (A.1 ⟶ B.1) := IsFusionCategory.hom_finite _ _
    exact PropertyF.Ground.Centre.finiteDimensional_hom ℂ A B
  apply finiteSimpleSum_of_injective (k := ℂ) ?_ Z
  intro W hW
  obtain ⟨P, hP⟩ := exists_simple_subobject hW
  exact ⟨P, P.arrow, hP, inferInstance⟩



/-- Centre rigidity and the explicit unit retract imply centre fusion. -/
theorem center_fusion_of_unit_retract {X : C.Obj} {U : 𝒵}
    (r : Retract (𝟙_ (𝒵)) ((induction C).obj X ⊗ U)) :
    IsFusionCategory (𝒵) := by
  obtain ⟨n, S, hS, hinj, hcover⟩ := finite_simple_representatives C
  apply PropertyF.Ground.CentreBundle.fusionOfFiniteSemisimple C
  refine ⟨n, S, hS, hinj, ?_⟩
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

/-- A nonzero cap on an induced object implies centre fusion. -/
theorem center_fusion_of_nonzero_induced_cap (X : C.Obj)
    (cap : (induction C).obj X ⊗ ((induction C).obj X)ᘁ ⟶ 𝟙_ (𝒵))
    (hne : η_ ((induction C).obj X) (((induction C).obj X)ᘁ) ≫ cap ≠ 0) :
    IsFusionCategory (𝒵) :=
  letI : Simple (𝟙_ C.Obj) := IsFusionCategory.unit_simple
  letI : Simple (𝟙_ (𝒵)) := PropertyF.Ground.Centre.centerUnitSimple
  center_fusion_of_unit_retract C (unitRetractOfNonzeroCap cap hne)

set_option backward.isDefEq.respectTransparency false in
/-- A centre pivotal structure with nonzero trace on an induced object implies fusion. -/
theorem center_fusion_of_nonzero_induced_trace (X : C.Obj)
    (p : Dimensions.PivotalStructure (C := 𝒵))
    (hne : p.rightTrace (𝟙 ((induction C).obj X)) ≠ 0) :
    IsFusionCategory (𝒵) := by
  let J := (induction C).obj X
  let cap : J ⊗ Jᘁ ⟶ 𝟙_ (𝒵) :=
    ((p.iso J).hom ⊗ₘ 𝟙 (Jᘁ)) ≫ ε_ (Jᘁ) ((Jᘁ)ᘁ)
  have hcap : η_ J (Jᘁ) ≫ cap ≠ 0 := by
    intro h
    apply hne
    apply End.ext
    simpa [Dimensions.PivotalStructure.rightTrace, cap, J, Category.assoc] using h
  exact center_fusion_of_nonzero_induced_cap C X cap hcap



end PropertyF.Ground.CentreInduction
