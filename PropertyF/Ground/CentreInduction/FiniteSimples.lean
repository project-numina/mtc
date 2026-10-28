module
public import PropertyF.Ground.CentreInduction.ActualFusion
public import PropertyF.Ground.Calculus.PartialTrace
public import PropertyF.Ground.Centre.Basic
public import PropertyF.Ground.Modular.SMatrix
public import PropertyF.Ground.Dimensions.SimpleScalars
public import PropertyF.Ground.Fusion.SemisimpleSplit
public import PropertyF.Ground.Centre.Abelian
public import Mathlib.CategoryTheory.Subobject.ArtinianObject
public import Mathlib.CategoryTheory.Subobject.NoetherianObject
public import Mathlib.RingTheory.Artinian.Module
public import Mathlib.CategoryTheory.Abelian.Exact

section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
universe v u
@[expose] public noncomputable section
namespace PropertyF.Ground.CentreInduction
variable (C : BraidedFusionCategory.{v,u})
local notation "𝒵" => Center C.Obj
variable {D : Type u} [Category.{v} D] [MonoidalCategory D]

set_option backward.isDefEq.respectTransparency false in
/-- An underlying factorization through a centre monomorphism is central. -/
theorem center_factor {P Q X : Center D} (p : P ⟶ X) (q : Q ⟶ X)
    [IsSplitMono q.f] (g : P.1 ⟶ Q.1) (hg : g ≫ q.f = p.f) :
    ∃ t : P ⟶ Q, t.f = g := by
  refine ⟨⟨g, ?_⟩, rfl⟩
  intro T
  let : IsSplitMono (T ◁ q.f) :=
    IsSplitMono.mk' ((inferInstance : IsSplitMono q.f).exists_splitMono.some.map (tensorLeft T))
  apply (cancel_mono (T ◁ q.f)).1
  simp only [Category.assoc, ← whiskerLeft_comp, hg]
  rw [← q.comm T, ← comp_whiskerRight_assoc, hg]
  exact p.comm T

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
      have : Mono P.arrow.f := by
        change Mono ((Center.forget C.Obj).map P.arrow)
        infer_instance
      let : IsSplitMono P.arrow.f := mono_splits C P.arrow.f
      have hm : retraction P.arrow.f ≫ P.arrow.f ∈ centerUnderlyingRange X P :=
        ⟨retraction P.arrow.f, rfl⟩
      obtain ⟨g, hg⟩ := h hm
      change g ≫ Q.arrow.f = retraction P.arrow.f ≫ P.arrow.f at hg
      have hg' : (P.arrow.f ≫ g) ≫ Q.arrow.f = P.arrow.f := by
        rw [Category.assoc, hg, ← Category.assoc, IsSplitMono.id, Category.id_comp]
      have : Mono Q.arrow.f := by
        change Mono ((Center.forget C.Obj).map Q.arrow)
        infer_instance
      let : IsSplitMono Q.arrow.f := mono_splits C Q.arrow.f
      obtain ⟨t, ht⟩ := center_factor P.arrow Q.arrow (P.arrow.f ≫ g) hg'
      apply Subobject.le_of_comm t
      apply Center.ext
      change t.f ≫ Q.arrow.f = P.arrow.f
      rw [ht, hg']
    · intro h x hx
      obtain ⟨g, rfl⟩ := hx
      refine ⟨g ≫ (Subobject.ofLE P Q h).f, ?_⟩
      change (g ≫ (Subobject.ofLE P Q h).f) ≫ Q.arrow.f = g ≫ P.arrow.f
      have hfactor := congrArg Center.Hom.f (Subobject.ofLE_arrow h)
      dsimp only [Center.comp_f] at hfactor
      rw [Category.assoc, hfactor])

/-- Every actual centre object is Artinian, without spherical hypotheses. -/
theorem center_artinian (X : 𝒵) : IsArtinianObject X :=
  let : FiniteDimensional ℂ (X.1 ⟶ X.1) := IsFusionCategory.hom_finite _ _
  ⟨(centerUnderlyingRangeEmbedding C X).wellFoundedLT⟩

set_option backward.isDefEq.respectTransparency false in
/-- Every simple centre object embeds in an induced base simple. -/
theorem simple_mono_induced_simple (X : 𝒵) [Simple X] :
    ∃ i : Fin (rank C), ∃ f : X ⟶ (induction C).obj (simples C i), Mono f := by
  obtain ⟨i, hi⟩ := exists_positive_multiplicity C
    (fun h => Simple.not_isZero X (Centre.isZero_of_forget h))
  let : FiniteDimensional ℂ (X.1 ⟶ simples C i) := IsFusionCategory.hom_finite _ _
  obtain ⟨g, hg⟩ := Module.finrank_pos_iff_exists_ne_zero.mp
    (show 0 < Module.finrank ℂ (X.1 ⟶ simples C i) from by
      simpa only [finrank_to_simple_eq_from_simple C] using hi)
  let e := homLinearEquivOfAdjunction (k := ℂ) (Center.forget C.Obj) (induction C)
    (actualAdjunction C) X (simples C i)
  exact ⟨i, e.symm g, mono_of_nonzero_from_simple (e.symm.map_eq_zero_iff.not.mpr hg)⟩

/-! Finiteness of simple objects in the actual Drinfeld centre. -/

set_option backward.isDefEq.respectTransparency false in
/-- A nonzero centre subobject strictly decreases the underlying endomorphism dimension on quotient. -/
theorem center_cokernel_measure_lt {S W : 𝒵} (p : S ⟶ W) (hp : p ≠ 0) :
    let Q := Centre.centerCokernel p
    Module.finrank ℂ (Q.1 ⟶ Q.1) < Module.finrank ℂ (W.1 ⟶ W.1) :=
  let Q := Centre.centerCokernel p
  let q : W.1 ⟶ Q.1 := (Centre.centerCokernelπ p).f
  letI : Epi q := inferInstanceAs (Epi (cokernel.π p.f))
  letI : IsSplitEpi q := epi_splits C q
  letI : FiniteDimensional ℂ (W.1 ⟶ W.1) := IsFusionCategory.hom_finite _ _
  finrank_end_lt_of_split_epi p.f q (fun h => hp (Center.ext p 0 h))
    (congrArg Center.Hom.f (Centre.centerCokernel_condition p))

/-- A simple subobject either lies in a simple kernel or embeds into the cokernel. -/
private theorem simple_mono_cokernel {D : Type u} [Category.{v} D] [Abelian D] {P W Q S : D}
    [Simple P] [Simple S] (p : P ⟶ W) [Mono p] (t : S ⟶ W) [Mono t] (q : W ⟶ Q)
    (hpq : p ≫ q = 0) (hc : IsColimit (CokernelCofork.ofπ q hpq)) :
    Nonempty (S ≅ P) ∨ Mono (t ≫ q) := by
  by_cases hz : t ≫ q = 0
  · obtain ⟨g, hg⟩ := KernelFork.IsLimit.lift'
      (Abelian.monoIsKernelOfCokernel (CokernelCofork.ofπ q hpq) hc) t hz
    change S ⟶ P at g
    change g ≫ p = t at hg
    let : IsIso g := isIso_of_hom_simple (fun h =>
      id_nonzero S ((cancel_mono t).1 (by simpa [h] using hg.symm)))
    exact Or.inl ⟨asIso g⟩
  · exact Or.inr (mono_of_nonzero_from_simple hz)

set_option backward.isDefEq.respectTransparency false in
/-- A centre object has only finitely many isomorphism classes of simple subobjects. -/
theorem finite_simple_subobject_labels (W : 𝒵) :
    ∃ L : List (𝒵), ∀ S : 𝒵, Simple S →
      (∃ t : S ⟶ W, Mono t) → ∃ T ∈ L, Nonempty (S ≅ T) := by
  let m : 𝒵 → ℕ := fun Z => Module.finrank ℂ (Z.1 ⟶ Z.1)
  induction W using (measure m).wf.induction with
  | h W ih =>
    by_cases hw : IsZero W
    · refine ⟨[], ?_⟩
      intro S hS ⟨t, ht⟩
      let : Simple S := hS
      let : Mono t := ht
      exact (Simple.not_isZero S (IsZero.of_mono t hw)).elim
    · let : IsArtinianObject W := center_artinian C W
      obtain ⟨P, hP⟩ := exists_simple_subobject hw
      let : Simple (P : 𝒵) := hP
      let p : (P : 𝒵) ⟶ W := P.arrow
      have hp : p ≠ 0 := fun h0 =>
        id_nonzero _ ((cancel_mono p).1 (by simp [h0]))
      let Q := Centre.centerCokernel p
      let q : W ⟶ Q := Centre.centerCokernelπ p
      obtain ⟨L, hL⟩ := ih Q (center_cokernel_measure_lt C p hp)
      refine ⟨(P : 𝒵) :: L, ?_⟩
      intro S hS ⟨t, ht⟩
      let : Simple S := hS
      let : Mono t := ht
      rcases simple_mono_cokernel p t q
          (Centre.centerCokernel_condition p)
          (Centre.centerCokernelIsColimit p) with hSP | hmono
      · exact ⟨P, List.Mem.head _, hSP⟩
      · let : Mono (t ≫ q) := hmono
        obtain ⟨T, hT, hST⟩ := hL S hS ⟨t ≫ q, inferInstance⟩
        exact ⟨T, List.Mem.tail _ hT, hST⟩

set_option backward.isDefEq.respectTransparency false in
/-- The actual centre has finitely many simple objects up to isomorphism. -/
theorem finite_simple_labels :
    ∃ labels : Finset (𝒵), (∀ T ∈ labels, Simple T) ∧
      ∀ X : 𝒵, Simple X → ∃ T ∈ labels, Nonempty (X ≅ T) := by
  classical
  let L (i : Fin (rank C)) := Classical.choose (finite_simple_subobject_labels C
    ((induction C).obj (simples C i)))
  have hL (i : Fin (rank C)) := Classical.choose_spec (finite_simple_subobject_labels C
    ((induction C).obj (simples C i)))
  let labels := (Finset.univ.biUnion (fun i => (L i).toFinset)).filter Simple
  refine ⟨labels, fun _ hT => (Finset.mem_filter.mp hT).2, ?_⟩
  intro X hX
  let : Simple X := hX
  obtain ⟨i, t, ht⟩ := simple_mono_induced_simple C X
  obtain ⟨T, hT, ⟨e⟩⟩ := hL i X hX ⟨t, ht⟩
  refine ⟨T, Finset.mem_filter.mpr ⟨?_, Simple.of_iso e.symm⟩, ⟨e⟩⟩
  exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, List.mem_toFinset.mpr hT⟩


end PropertyF.Ground.CentreInduction

end
end
