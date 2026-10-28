module
public import PropertyF.Ground.CentreInduction.ActualFusion
public import Mathlib.CategoryTheory.Subobject.ArtinianObject
public import Mathlib.RingTheory.Artinian.Module
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic

/-! # Finiteness and fusion of the centre

The centre has finitely many simple isomorphism classes. A retract of the tensor unit through
an induced object then gives finite semisimple decompositions and a fusion structure.
-/

section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
universe v u
@[expose] public noncomputable section
namespace PropertyF.Ground.CentreInduction
variable (C : BraidedFusionCategory.{v,u})
local notation "Sᶜ" => simples C
local notation "𝒵" => Center C.Obj

attribute [local instance] IsFusionCategory.hom_finite
variable {D : Type u} [Category.{v} D] [MonoidalCategory D]

set_option backward.isDefEq.respectTransparency false in
/-- An underlying factorization through a centre monomorphism is central. -/
theorem center_factor {P Q X : Center D} (p : P ⟶ X) (q : Q ⟶ X)
    [IsSplitMono q.f] (g : P.1 ⟶ Q.1) (hg : g ≫ q.f = p.f) :
    ∃ t : P ⟶ Q, t.f = g :=
  ⟨⟨g, fun T ↦
    letI : IsSplitMono (T ◁ q.f) :=
      IsSplitMono.mk' ((inferInstance : IsSplitMono q.f).exists_splitMono.some.map (tensorLeft T))
    (cancel_mono (T ◁ q.f)).1 <| by
      simp only [Category.assoc, ← whiskerLeft_comp, hg, ← q.comm T,
        ← comp_whiskerRight_assoc, p.comm]⟩, rfl⟩

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
        rw [Category.assoc, hg, ← Category.assoc, IsSplitMono.id, Category.id_comp]
      let : IsSplitMono Q.arrow.f := mono_splits ((Center.forget C.Obj).map Q.arrow)
      obtain ⟨t, ht⟩ := center_factor P.arrow Q.arrow (P.arrow.f ≫ g) hg'
      exact Subobject.le_of_comm t (Center.ext _ _ ((congrArg (· ≫ Q.arrow.f) ht).trans hg'))
    · intro h x hx
      obtain ⟨g, rfl⟩ := hx
      refine ⟨g ≫ (Subobject.ofLE P Q h).f, ?_⟩
      change (g ≫ (Subobject.ofLE P Q h).f) ≫ Q.arrow.f = g ≫ P.arrow.f
      exact (Category.assoc _ _ _).trans <|
        congrArg (g ≫ ·) (congrArg Center.Hom.f (Subobject.ofLE_arrow h)))

variable (X : Center C.Obj)

/-- Every actual centre object is Artinian, without spherical hypotheses. -/
theorem center_artinian : IsArtinianObject X :=
  ⟨(centerUnderlyingRangeEmbedding C X).wellFoundedLT⟩

set_option backward.isDefEq.respectTransparency false in
/-- Every simple centre object embeds in an induced base simple. -/
theorem simple_mono_induced_simple [Simple X] :
    ∃ i : Fin (rank C), ∃ f : X ⟶ (induction C).obj (Sᶜ i), Mono f := by
  let : HasFiniteBiproducts C.Obj := Abelian.hasFiniteBiproducts
  obtain ⟨i, hi⟩ := exists_positive_multiplicity (simples C) (simples_decompose C X.1)
    (fun _ ↦ IsFusionCategory.hom_finite _ _)
    (fun h => Simple.not_isZero X (Centre.isZero_of_forget h))
  let : Simple (Sᶜ i) := simples_simple C i
  obtain ⟨g, hg⟩ := Module.finrank_pos_iff_exists_ne_zero.mp
    (show 0 < Module.finrank ℂ (X.1 ⟶ Sᶜ i) from by
      simpa only [finrank_to_simple_eq_from_simple _ (Sᶜ i)] using hi)
  let e := homLinearEquivOfAdjunction (k := ℂ) (Center.forget C.Obj) (induction C)
    (actualAdjunction C) X (Sᶜ i)
  exact ⟨i, e.symm g, mono_of_nonzero_from_simple (e.symm.map_eq_zero_iff.not.mpr hg)⟩

/-! Finiteness of simple objects in the actual Drinfeld centre. -/

omit [MonoidalCategory D] in
/-- A simple subobject either lies in a simple kernel or embeds into the cokernel. -/
private theorem simple_mono_cokernel [Abelian D] {P W Q S : D}
    [Simple P] [Simple S] (p : P ⟶ W) [Mono p] (t : S ⟶ W) [Mono t] (q : W ⟶ Q)
    (hpq : p ≫ q = 0) (hc : IsColimit (CokernelCofork.ofπ q hpq)) :
    Nonempty (S ≅ P) ∨ Mono (t ≫ q) :=
  or_iff_not_imp_left.mpr fun h => mono_of_nonzero_from_simple fun hz => h <| by
    obtain ⟨g, hg⟩ : {g : S ⟶ P // g ≫ p = t} := KernelFork.IsLimit.lift'
      (Abelian.monoIsKernelOfCokernel (CokernelCofork.ofπ q hpq) hc) t hz
    let : IsIso g := isIso_of_hom_simple (fun hg0 =>
      mono_ne_zero_of_id_ne_zero t (id_nonzero S) (by simpa [hg0] using hg.symm))
    exact ⟨asIso g⟩

set_option backward.isDefEq.respectTransparency false in
/-- A centre object has only finitely many isomorphism classes of simple subobjects. -/
theorem finite_simple_subobject_labels (W : 𝒵) :
    ∃ L : List (𝒵), ∀ S : 𝒵, Simple S →
      (∃ t : S ⟶ W, Mono t) → ∃ T ∈ L, Nonempty (S ≅ T) := by
  induction W using (measure fun Z : 𝒵 ↦ Module.finrank ℂ (Z.1 ⟶ Z.1)).wf.induction with
  | h W ih =>
    by_cases hw : IsZero W
    · refine ⟨[], fun S hS ⟨t, ht⟩ => ?_⟩
      let : Simple S := hS
      let : Mono t := ht
      exact (Simple.not_isZero S (IsZero.of_mono t hw)).elim
    · let : IsArtinianObject W := center_artinian C W
      let P := simpleSubobject hw
      let p : P ⟶ W := simpleSubobjectArrow hw
      have hp : p ≠ 0 := mono_ne_zero_of_id_ne_zero p (id_nonzero _)
      let Q := Centre.centerCokernel p
      let q : W ⟶ Q := Centre.centerCokernelπ p
      let : IsSplitEpi (cokernel.π p.f) := epi_splits (cokernel.π p.f)
      obtain ⟨L, hL⟩ := ih Q (finrank_end_lt_of_split_epi p.f (cokernel.π p.f)
        (fun h => hp (Center.ext p 0 h)) (cokernel.condition p.f))
      refine ⟨P :: L, fun S hS ⟨t, ht⟩ => ?_⟩
      let : Simple S := hS
      let : Mono t := ht
      exact (simple_mono_cokernel p t q
        (Centre.centerCokernel_condition p) (Centre.centerCokernelIsColimit p)).elim
        (fun hSP => ⟨P, List.Mem.head _, hSP⟩) (fun hmono =>
          let ⟨T, hT, hST⟩ := hL S hS ⟨t ≫ q, hmono⟩
          ⟨T, List.Mem.tail _ hT, hST⟩)

set_option backward.isDefEq.respectTransparency false in
/-- The actual centre has finitely many simple objects up to isomorphism. -/
theorem finite_simple_labels :
    ∃ labels : Finset (𝒵), (∀ T ∈ labels, Simple T) ∧
      ∀ X : 𝒵, Simple X → ∃ T ∈ labels, Nonempty (X ≅ T) := by
  classical
  choose L hL using fun i : Fin (rank C) =>
    finite_simple_subobject_labels C ((induction C).obj (Sᶜ i))
  let labels := (Finset.univ.biUnion (fun i => (L i).toFinset)).filter Simple
  refine ⟨labels, fun _ hT => (Finset.mem_filter.mp hT).2, fun X hX => ?_⟩
  let : Simple X := hX
  obtain ⟨i, t, ht⟩ := simple_mono_induced_simple C X
  obtain ⟨T, hT, ⟨e⟩⟩ := hL i X hX ⟨t, ht⟩
  exact ⟨T, Finset.mem_filter.mpr
    ⟨Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, List.mem_toFinset.mpr hT⟩,
      Simple.of_iso e.symm⟩, ⟨e⟩⟩


end PropertyF.Ground.CentreInduction

end
end

/-! An injective-retract route to centre semisimplicity and fusion. -/
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits PropertyF.Ground.Dimensions
universe v u
@[expose] public noncomputable section
namespace PropertyF.Ground.CentreInduction
attribute [local instance] IsFusionCategory.hom_finite
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
  letI (A : 𝒵) : FiniteDimensional ℂ (A ⟶ A) := Centre.finiteDimensional_hom ℂ A A
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
    [Preadditive D] [HasKernels D] [Simple (𝟙_ D)]
    {J : D} [HasRightDual J] (cap : J ⊗ Jᘁ ⟶ 𝟙_ D) (hne : η_ J (Jᘁ) ≫ cap ≠ 0) :
    Retract (𝟙_ D) (J ⊗ Jᘁ) :=
  letI : IsIso (η_ J (Jᘁ) ≫ cap) := isIso_of_hom_simple hne
  { i := η_ J (Jᘁ), r := cap ≫ inv (η_ J (Jᘁ) ≫ cap)
    retract := (Category.assoc _ _ _).symm.trans (IsIso.hom_inv_id _) }

set_option backward.isDefEq.respectTransparency false in
/-- A centre pivotal structure with nonzero trace on an induced object implies fusion. -/
theorem center_fusion_of_nonzero_induced_trace {X : C.Obj}
    (p : PivotalStructure (C := 𝒵))
    (hne : p.rightTrace (𝟙 ((induction C).obj X)) ≠ 0) :
    IsFusionCategory (𝒵) :=
  let J := (induction C).obj X
  let cap : J ⊗ Jᘁ ⟶ 𝟙_ (𝒵) :=
    ((p.iso J).hom ⊗ₘ 𝟙 (Jᘁ)) ≫ ε_ (Jᘁ) ((Jᘁ)ᘁ)
  letI : Simple (𝟙_ C.Obj) := IsFusionCategory.unit_simple
  letI : Simple (𝟙_ (𝒵)) := Centre.centerUnitSimple
  center_fusion_of_unit_retract C <| unitRetractOfNonzeroCap cap <| fun h =>
    hne (End.ext (by simpa [PivotalStructure.rightTrace, rightTraceWith,
      cap, J, Category.assoc] using h))

end PropertyF.Ground.CentreInduction
