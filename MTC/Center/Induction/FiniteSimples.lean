module
public import MTC.Center.Induction.ActualFusion
public import Mathlib.CategoryTheory.Subobject.ArtinianObject
public import Mathlib.RingTheory.Artinian.Module
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic

/-! # Finiteness and fusion of the centre

The centre has finitely many simple isomorphism classes. A retract of the tensor unit through
an induced object then gives finite semisimple decompositions and a fusion structure.
-/

attribute [local instance] MTC.Center.finiteDimensional_hom

section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits Module
open CategoryTheory.Category
universe v u
@[expose] public noncomputable section
namespace MTC.Center.Induction
variable {C : BraidedFusionCategory.{v,u}}
local notation "Sᶜ" => simples C
local notation "𝒵" => Center C.Obj

attribute [local instance] IsFusionCategory.hom_finite Abelian.hasFiniteBiproducts
local instance (i : Fin (rank C)) : Simple (Sᶜ i) := simples_simple C i
variable {D : Type u} [Category.{v} D] [MonoidalCategory D]

set_option backward.isDefEq.respectTransparency false in
/-- An underlying factorization through a centre monomorphism is central. -/
theorem center_factor {P Q X : Center D} (p : P ⟶ X) (q : Q ⟶ X)
    [IsSplitMono q.f] (g : P.1 ⟶ Q.1) (hg : g ≫ q.f = p.f) :
    ∃ t : P ⟶ Q, t.f = g :=
  ⟨⟨g, fun T ↦ letI : Mono (T ◁ q.f) := inferInstanceAs (Mono ((tensorLeft T).map q.f))
    (cancel_mono (T ◁ q.f)).1 <| by
      simp only [assoc, ← whiskerLeft_comp, hg, ← q.comm, ← comp_whiskerRight_assoc, p.comm]⟩, rfl⟩

/-- Underlying endomorphisms that factor through a centre subobject. -/
def centerUnderlyingRange [Preadditive D] [Linear ℂ D] (X : Center D) (P : Subobject X) :
    Submodule ℂ (X.1 ⟶ X.1) := LinearMap.range (Linear.rightComp ℂ X.1 P.arrow.f)

set_option backward.isDefEq.respectTransparency false in
/-- Underlying endomorphism ranges detect the order of centre subobjects. -/
def centerUnderlyingRangeEmbedding (X : 𝒵) :
    Subobject X ↪o Submodule ℂ (X.1 ⟶ X.1) :=
  OrderEmbedding.ofMapLEIff (centerUnderlyingRange X) (by
    intro P Q
    constructor
    · intro h
      let : IsSplitMono P.arrow.f := mono_splits ((Center.forget C.Obj).map P.arrow)
      have hm : retraction P.arrow.f ≫ P.arrow.f ∈ centerUnderlyingRange X P :=
        ⟨retraction P.arrow.f, rfl⟩
      obtain ⟨g, hg⟩ := h hm
      change g ≫ Q.arrow.f = retraction P.arrow.f ≫ P.arrow.f at hg
      have hg' : (P.arrow.f ≫ g) ≫ Q.arrow.f = P.arrow.f := by
        rw [assoc, hg, ← assoc, IsSplitMono.id, Category.id_comp]
      let : IsSplitMono Q.arrow.f := mono_splits ((Center.forget C.Obj).map Q.arrow)
      obtain ⟨t, ht⟩ := center_factor P.arrow Q.arrow (P.arrow.f ≫ g) hg'
      exact Subobject.le_of_comm t (Center.ext _ _ ((congrArg (· ≫ Q.arrow.f) ht).trans hg'))
    · intro h x hx
      obtain ⟨g, rfl⟩ := hx
      refine ⟨g ≫ (Subobject.ofLE P Q h).f, ?_⟩
      change (g ≫ (Subobject.ofLE P Q h).f) ≫ Q.arrow.f = g ≫ P.arrow.f
      exact (assoc _ _ _).trans <|
        congrArg (g ≫ ·) (congrArg Center.Hom.f (Subobject.ofLE_arrow h)))

variable (X : Center C.Obj)

/-- Every actual centre object is Artinian, without spherical hypotheses. -/
theorem center_artinian : IsArtinianObject X :=
  ⟨(centerUnderlyingRangeEmbedding X).wellFoundedLT⟩

set_option backward.isDefEq.respectTransparency false in
/-- Every simple centre object has a nonzero map to an induced base simple. -/
theorem simple_hom_induced_simple [Simple X] :
    ∃ i : Fin (rank C), ∃ f : X ⟶ (induction C).obj (Sᶜ i), f ≠ 0 :=
  (exists_positive_multiplicity (k := ℂ) (simples_decompose C X.1)
    (fun _ ↦ inferInstance) (fun h ↦ Simple.not_isZero X (MTC.Center.isZero_of_forget h))).imp
    fun i hi ↦ (finrank_pos_iff_exists_ne_zero (R := ℂ)).mp (by
      simpa only [finrank_hom_induction, finrank_to_simple_eq_from_simple _ (Sᶜ i)] using hi)

end MTC.Center.Induction

end
end

/-! An injective-retract route to centre semisimplicity and fusion. -/
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits MTC.Dimensions
universe v u
@[expose] public noncomputable section
namespace MTC.Center.Induction
attribute [local instance] IsFusionCategory.hom_finite IsFusionCategory.unit_simple
variable {D : Type u} [Category.{v} D] [Abelian D] [MonoidalCategory D] [LeftRigidCategory D]

omit [Abelian D] [LeftRigidCategory D] in
/-- Tensoring with an object whose first two left duals exist preserves injectives. -/
theorem tensor_preserves_injective (J U : D)
    [HasLeftDual U] [HasLeftDual (ᘁU)] [Injective J] : Injective (J ⊗ U) :=
  letI : (tensorRight (ᘁU)).IsRightAdjoint :=
    ⟨⟨tensorRight (ᘁ(ᘁU)), ⟨tensorRightAdjunction (ᘁ(ᘁU)) (ᘁU)⟩⟩⟩
  (tensorRightAdjunction (ᘁU) U).map_injective J inferInstance

omit [Abelian D] [LeftRigidCategory D] in
/-- A unit retract of a tensor product with an injective makes an object with
two left duals injective. -/
theorem all_injective_of_unit_retract {J U : D} [Injective J]
    [HasLeftDual U] [HasLeftDual (ᘁU)] (r : Retract (𝟙_ D) (J ⊗ U)) (X : D)
    [HasLeftDual X] [HasLeftDual (ᘁX)] : Injective X :=
  letI : Injective (J ⊗ U) := tensor_preserves_injective J U
  letI : Injective (𝟙_ D) := r.injective
  Injective.of_iso (λ_ X) (tensor_preserves_injective (𝟙_ D) X)

variable {C : BraidedFusionCategory.{v,u}} [RigidCategory (Center C.Obj)]
local notation "𝒵" => Center C.Obj
variable {X : C.Obj}

set_option backward.isDefEq.respectTransparency false in
/-- Under the unit-retract condition every centre object is a finite simple sum. -/
theorem center_finite_simple_sum_of_unit_retract {U : 𝒵}
    (r : Retract (𝟙_ (𝒵)) ((induction C).obj X ⊗ U))
    (Z : 𝒵) : FiniteSimpleSum Z :=
  letI (W : 𝒵) : IsArtinianObject W := center_artinian W
  letI : Injective ((induction C).obj X) := (actualAdjunction C).map_injective X (object_injective X)
  letI (W : 𝒵) : Injective W := all_injective_of_unit_retract r W
  finiteSimpleSum_of_injective (k := ℂ) (fun {_} hW =>
    ⟨simpleSubobject hW, simpleSubobjectArrow hW, inferInstance, inferInstance⟩) Z

/-- The actual centre has finitely many simple objects up to isomorphism. -/
theorem finite_simple_labels {U : 𝒵}
    (r : Retract (𝟙_ (𝒵)) ((induction C).obj X ⊗ U)) :
    ∃ labels : Finset 𝒵, (∀ T ∈ labels, Simple T) ∧
      ∀ Z : 𝒵, Simple Z → ∃ T ∈ labels, Nonempty (Z ≅ T) := by
  classical
  choose n V hV hIso using fun i : Fin (rank C) ↦ finiteSimpleSum_biproduct
    (center_finite_simple_sum_of_unit_retract r ((induction C).obj (simples C i)))
  let labels := (Finset.univ.biUnion fun i => Finset.univ.image (V i)).filter Simple
  refine ⟨labels, fun _ h => (Finset.mem_filter.mp h).2, fun Z hZ => ?_⟩
  let : Simple Z := hZ
  obtain ⟨i, t, ht⟩ := simple_hom_induced_simple Z
  obtain ⟨j, e⟩ := simple_iso_biproduct_summand (hV i) (t ≫ (hIso i).some.hom)
    (fun h => ht (zero_of_comp_mono _ h))
  exact ⟨V i j, Finset.mem_filter.mpr ⟨Finset.mem_biUnion.mpr
    ⟨i, Finset.mem_univ _, Finset.mem_image_of_mem _ (Finset.mem_univ j)⟩, hV i j⟩, e⟩

/-- Centre rigidity and the explicit unit retract imply centre fusion. -/
theorem center_fusion_of_unit_retract {U : 𝒵}
    (r : Retract (𝟙_ (𝒵)) ((induction C).obj X ⊗ U)) :
    IsFusionCategory (𝒵) :=
  let ⟨_, hsimple, hcover⟩ := finite_simple_labels r
  let ⟨n, S, hS, hinj, hcover⟩ := simple_representatives_of_finite_cover hsimple hcover
  MTC.Center.Fusion.fusionOfFiniteSemisimple C ⟨n, S, hS, hinj, fun Z =>
    let ⟨_, V, hV, ⟨e⟩⟩ := finiteSimpleSum_biproduct (center_finite_simple_sum_of_unit_retract r Z)
    let ⟨m, ⟨a⟩⟩ := regroup_biproduct (fun j => hcover (V j) (hV j))
    ⟨m, ⟨e ≪≫ a⟩⟩⟩

set_option backward.isDefEq.respectTransparency false in
/-- A cap with nonzero unit composite gives a unit retract. -/
def unitRetractOfNonzeroCap {D : Type u} [Category.{v} D] [MonoidalCategory D]
    [Preadditive D] [HasKernels D] [Simple (𝟙_ D)]
    {J : D} [HasRightDual J] (cap : J ⊗ Jᘁ ⟶ 𝟙_ D) (hne : η_ J (Jᘁ) ≫ cap ≠ 0) :
    Retract (𝟙_ D) (J ⊗ Jᘁ) :=
  letI : IsIso (η_ J (Jᘁ) ≫ cap) := isIso_of_hom_simple hne
  { i := η_ J (Jᘁ), r := cap ≫ inv (η_ J (Jᘁ) ≫ cap)
    retract := (Category.assoc _ _ _).symm.trans (IsIso.hom_inv_id _) }

set_option backward.isDefEq.respectTransparency false in
/-- A centre pivotal structure with nonzero trace on an induced object implies fusion. -/
theorem center_fusion_of_nonzero_induced_trace (p : PivotalStructure (C := 𝒵))
    (hne : p.rightTrace (𝟙 ((induction C).obj X)) ≠ 0) :
    IsFusionCategory (𝒵) :=
  let J := (induction C).obj X
  let cap : J ⊗ Jᘁ ⟶ 𝟙_ (𝒵) :=
    ((p.iso J).hom ⊗ₘ 𝟙 (Jᘁ)) ≫ ε_ (Jᘁ) ((Jᘁ)ᘁ)
  letI : Simple (𝟙_ (𝒵)) := MTC.Center.centerUnitSimple
  center_fusion_of_unit_retract <| unitRetractOfNonzeroCap cap <| fun h =>
    hne (End.ext (by simpa [PivotalStructure.rightTrace, rightTraceWith,
      cap, J, Category.assoc] using h))

end MTC.Center.Induction
