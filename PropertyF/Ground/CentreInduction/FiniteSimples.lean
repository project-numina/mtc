module
public import PropertyF.Ground.CentreInduction.ActualFusion
public import Mathlib.CategoryTheory.Subobject.ArtinianObject
public import Mathlib.RingTheory.Artinian.Module

section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
universe v u
@[expose] public noncomputable section
namespace PropertyF.Ground.CentreInduction
variable (C : BraidedFusionCategory.{v,u})
local notation "Sᶜ" => simples C
local notation "𝒵" => Center C.Obj

/-- Hom spaces in the base fusion category are finite-dimensional. -/
local instance homFinite (A B : C.Obj) : FiniteDimensional ℂ (A ⟶ B) :=
  IsFusionCategory.hom_finite _ _
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

set_option backward.isDefEq.respectTransparency false in
/-- A nonzero centre subobject strictly decreases the underlying endomorphism dimension on quotient. -/
theorem center_cokernel_measure_lt {S W : 𝒵} (p : S ⟶ W) (hp : p ≠ 0) :
    let Q := Centre.centerCokernel p
    Module.finrank ℂ (Q.1 ⟶ Q.1) < Module.finrank ℂ (W.1 ⟶ W.1) :=
  letI : IsSplitEpi (cokernel.π p.f) := epi_splits (cokernel.π p.f)
  finrank_end_lt_of_split_epi p.f (cokernel.π p.f) (fun h => hp (Center.ext p 0 h))
    (congrArg Center.Hom.f (Centre.centerCokernel_condition p))

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
      obtain ⟨L, hL⟩ := ih Q (center_cokernel_measure_lt C p hp)
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
