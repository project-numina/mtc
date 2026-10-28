module
public import PropertyF.Ground.CentreInduction.ActualFusion
public import PropertyF.Ground.Calculus.PartialTrace
public import PropertyF.Ground.Centre.Basic
public import PropertyF.Ground.Modular.SMatrix
public import PropertyF.Ground.Dimensions.SimpleScalars
public import PropertyF.Ground.Centre.Basic
public import PropertyF.Ground.Fusion.SemisimpleSplit
public import PropertyF.Ground.Centre.Cokernel
public import PropertyF.Ground.Centre.Abelian
public import Mathlib.CategoryTheory.Subobject.ArtinianObject
public import Mathlib.CategoryTheory.Subobject.NoetherianObject
public import Mathlib.RingTheory.Artinian.Module
public import Mathlib.CategoryTheory.Abelian.Exact
public import PropertyF.Ground.Fusion.SemisimpleSplit

section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
universe v u
@[expose] public noncomputable section
namespace PropertyF.Ground.CentreInduction
variable (C : BraidedFusionCategory.{v,u})

set_option backward.isDefEq.respectTransparency false in
/-- An underlying factorization through a centre monomorphism is central. -/
theorem center_factor {P Q X : CategoryTheory.Center C.Obj} (p : P ⟶ X) (q : Q ⟶ X)
    [Mono q] (g : P.1 ⟶ Q.1) (hg : g ≫ q.f = p.f) :
    ∃ t : P ⟶ Q, t.f = g := by
  have : Mono q.f := by
    change Mono ((CategoryTheory.Center.forget C.Obj).map q)
    infer_instance
  let t : P ⟶ Q := ⟨g, ?_⟩
  · exact ⟨t, rfl⟩
  · intro T
    let : IsSplitMono q.f := mono_splits C q.f
    let : IsSplitMono (T ◁ q.f) := IsSplitMono.mk'
      { retraction := T ◁ retraction q.f
        id := by rw [← whiskerLeft_comp, IsSplitMono.id, whiskerLeft_id] }
    apply (cancel_mono (T ◁ q.f)).1
    have hq := congrArg (fun k => (g ▷ T) ≫ k) (q.comm T).symm
    have hg' := congrArg (fun k => (k ▷ T) ≫ (X.2.β T).hom) hg
    calc
      _ = (g ▷ T) ≫ (q.f ▷ T) ≫ ((X.2.β T).hom) := by simp [Category.assoc]
      _ = (p.f ▷ T) ≫ ((X.2.β T).hom) := by simpa [comp_whiskerRight, Category.assoc] using hg'
      _ = ((P.2.β T).hom) ≫ (T ◁ p.f) := p.comm T
      _ = _ := by rw [← hg, whiskerLeft_comp]; simp [Category.assoc]

/-- Underlying endomorphisms that factor through a centre subobject. -/
def centerUnderlyingRange (X : CategoryTheory.Center C.Obj) (P : Subobject X) :
    Submodule ℂ (X.1 ⟶ X.1) := LinearMap.range (Linear.rightComp ℂ X.1 P.arrow.f)

set_option backward.isDefEq.respectTransparency false in
/-- Underlying endomorphism ranges detect the order of centre subobjects. -/
def centerUnderlyingRangeEmbedding (X : CategoryTheory.Center C.Obj) :
    Subobject X ↪o Submodule ℂ (X.1 ⟶ X.1) :=
  OrderEmbedding.ofMapLEIff (centerUnderlyingRange C X) (by
    intro P Q
    constructor
    · intro h
      have : Mono P.arrow.f := by
        change Mono ((CategoryTheory.Center.forget C.Obj).map P.arrow)
        infer_instance
      let : IsSplitMono P.arrow.f := mono_splits C P.arrow.f
      have hm : retraction P.arrow.f ≫ P.arrow.f ∈ centerUnderlyingRange C X P :=
        ⟨retraction P.arrow.f, rfl⟩
      obtain ⟨g, hg⟩ := h hm
      change g ≫ Q.arrow.f = retraction P.arrow.f ≫ P.arrow.f at hg
      have hg' : (P.arrow.f ≫ g) ≫ Q.arrow.f = P.arrow.f := by
        rw [Category.assoc, hg, ← Category.assoc, IsSplitMono.id, Category.id_comp]
      obtain ⟨t, ht⟩ := center_factor C P.arrow Q.arrow (P.arrow.f ≫ g) hg'
      apply Subobject.le_of_comm t
      apply CategoryTheory.Center.ext
      change t.f ≫ Q.arrow.f = P.arrow.f
      rw [ht, hg']
    · intro h x hx
      obtain ⟨g, rfl⟩ := hx
      refine ⟨g ≫ (Subobject.ofLE P Q h).f, ?_⟩
      change (g ≫ (Subobject.ofLE P Q h).f) ≫ Q.arrow.f = g ≫ P.arrow.f
      have hfactor := congrArg CategoryTheory.Center.Hom.f (Subobject.ofLE_arrow h)
      dsimp only [CategoryTheory.Center.comp_f] at hfactor
      rw [Category.assoc, hfactor])

/-- Every actual centre object is Artinian, without spherical hypotheses. -/
theorem center_artinian (X : CategoryTheory.Center C.Obj) : IsArtinianObject X := by
  let : FiniteDimensional ℂ (X.1 ⟶ X.1) := IsFusionCategory.hom_finite _ _
  exact ⟨(centerUnderlyingRangeEmbedding C X).wellFoundedLT⟩


set_option backward.isDefEq.respectTransparency false in
/-- Every simple centre object embeds in an induced base simple. -/
theorem simple_mono_induced_simple (X : CategoryTheory.Center C.Obj) [Simple X] :
    ∃ i : Fin (rank C), ∃ f : X ⟶ (induction C).obj (simples C i), Mono f := by
  have hx : ¬ IsZero X.1 := by
    intro hz
    have hid : (𝟙 X : X ⟶ X) = 0 := by
      apply CategoryTheory.Center.ext
      change (CategoryTheory.Center.forget C.Obj).map (𝟙 X) =
        (CategoryTheory.Center.forget C.Obj).map 0
      rw [(CategoryTheory.Center.forget C.Obj).map_id, (CategoryTheory.Center.forget C.Obj).map_zero]
      exact (IsZero.iff_id_eq_zero X.1).mp hz
    exact id_nonzero X hid
  obtain ⟨i, hi⟩ := exists_positive_multiplicity C X.1 hx
  have hi' : 0 < Module.finrank ℂ (X.1 ⟶ simples C i) := by
    rw [finrank_to_simple_eq_from_simple C]
    exact hi
  let : FiniteDimensional ℂ (X.1 ⟶ simples C i) := IsFusionCategory.hom_finite _ _
  obtain ⟨g, hg⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hi'
  let e := homLinearEquivOfAdjunction (CategoryTheory.Center.forget C.Obj) (induction C)
    (actualAdjunction C) X (simples C i)
  let t : X ⟶ (induction C).obj (simples C i) := e.symm g
  have ht : t ≠ 0 := by
    intro ht
    apply hg
    have := congrArg e ht
    simpa [t] using this
  exact ⟨i, t, mono_of_nonzero_from_simple ht⟩

end PropertyF.Ground.CentreInduction

end
end

/-! Finiteness of simple objects in the actual Drinfeld centre. -/
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
universe v u
@[expose] public noncomputable section
namespace PropertyF.Ground.CentreInduction
variable (C : BraidedFusionCategory.{v,u})

set_option backward.isDefEq.respectTransparency false in
/-- A nonzero centre subobject strictly decreases the underlying endomorphism dimension on quotient. -/
theorem center_cokernel_measure_lt {S W : CategoryTheory.Center C.Obj}
    (p : S ⟶ W) (hp : p ≠ 0) :
    Module.finrank ℂ ((PropertyF.Ground.Centre.centerCokernel p).1 ⟶
      (PropertyF.Ground.Centre.centerCokernel p).1) < Module.finrank ℂ (W.1 ⟶ W.1) := by
  let Q := PropertyF.Ground.Centre.centerCokernel p
  let q : W.1 ⟶ Q.1 := (PropertyF.Ground.Centre.centerCokernelπ p).f
  have hq : p.f ≫ q = 0 := congrArg CategoryTheory.Center.Hom.f (PropertyF.Ground.Centre.centerCokernel_condition p)
  have : Epi q := by
    change Epi (cokernel.π p.f)
    infer_instance
  let : IsSplitEpi q := epi_splits C q
  let s : Q.1 ⟶ W.1 := section_ q
  have hs : s ≫ q = 𝟙 Q.1 := IsSplitEpi.id q
  let L : (Q.1 ⟶ Q.1) →ₗ[ℂ] (W.1 ⟶ W.1) :=
    (Linear.leftComp ℂ W.1 q).comp (Linear.rightComp ℂ Q.1 s)
  have hinj : Function.Injective L := by
    intro x y h
    have hh := congrArg (fun k => s ≫ k ≫ q) h
    simpa [L, s, Category.assoc, hs] using hh
  have hproper : LinearMap.range L ≠ ⊤ := by
    intro hall
    have hh : (𝟙 W.1) ∈ LinearMap.range L := by rw [hall]; trivial
    obtain ⟨x, hx⟩ := hh
    have he := congrArg (fun k => p.f ≫ k) hx
    have hz : p.f = 0 := by
      change p.f ≫ (q ≫ x ≫ s) = p.f ≫ 𝟙 W.1 at he
      simp only [← Category.assoc, hq, zero_comp, Category.comp_id] at he
      exact he.symm
    apply hp
    apply CategoryTheory.Center.ext
    exact hz
  let : FiniteDimensional ℂ (W.1 ⟶ W.1) := IsFusionCategory.hom_finite _ _
  let : FiniteDimensional ℂ (Q.1 ⟶ Q.1) := IsFusionCategory.hom_finite _ _
  have hlt := Submodule.finrank_lt_finrank_of_lt (lt_top_iff_ne_top.mpr hproper)
  rw [finrank_top, LinearMap.finrank_range_of_inj hinj] at hlt
  exact hlt

set_option backward.isDefEq.respectTransparency false in
/-- A centre object has only finitely many isomorphism classes of simple subobjects. -/
theorem finite_simple_subobject_labels (W : CategoryTheory.Center C.Obj) :
    ∃ L : List (CategoryTheory.Center C.Obj),
      ∀ S : CategoryTheory.Center C.Obj, Simple S →
        (∃ t : S ⟶ W, Mono t) → ∃ T ∈ L, Nonempty (S ≅ T) := by
  classical
  let m : CategoryTheory.Center C.Obj → ℕ := fun Z => Module.finrank ℂ (Z.1 ⟶ Z.1)
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
      let : Simple (P : CategoryTheory.Center C.Obj) := hP
      let p : (P : CategoryTheory.Center C.Obj) ⟶ W := P.arrow
      have hp : p ≠ 0 := fun h0 =>
        id_nonzero _ ((cancel_mono p).1 (by simp [h0]))
      let Q := PropertyF.Ground.Centre.centerCokernel p
      let q : W ⟶ Q := PropertyF.Ground.Centre.centerCokernelπ p
      have hlt : m Q < m W := center_cokernel_measure_lt C p hp
      obtain ⟨L, hL⟩ := ih Q hlt
      refine ⟨(P : CategoryTheory.Center C.Obj) :: L, ?_⟩
      intro S hS ⟨t, ht⟩
      let : Simple S := hS
      let : Mono t := ht
      have ht0 : t ≠ 0 := fun h0 =>
        id_nonzero S ((cancel_mono t).1 (by simp [h0]))
      by_cases hz : t ≫ q = 0
      · have hcok := PropertyF.Ground.Centre.centerCokernelIsColimit p
        have hk := Abelian.monoIsKernelOfCokernel
          (CokernelCofork.ofπ q (PropertyF.Ground.Centre.centerCokernel_condition p)) hcok
        obtain ⟨g, hg⟩ := KernelFork.IsLimit.lift' hk t hz
        change S ⟶ (P : CategoryTheory.Center C.Obj) at g
        change g ≫ p = t at hg
        have hg0 : g ≠ 0 := by
          intro h0
          apply ht0
          simpa [h0] using hg.symm
        let : IsIso g := isIso_of_hom_simple hg0
        exact ⟨P, by simp, ⟨asIso g⟩⟩
      · let : Mono (t ≫ q) := mono_of_nonzero_from_simple hz
        obtain ⟨T, hT, hST⟩ := hL S hS ⟨t ≫ q, inferInstance⟩
        exact ⟨T, by simp [hT], hST⟩

set_option backward.isDefEq.respectTransparency false in
/-- The actual centre has finitely many simple objects up to isomorphism. -/
theorem finite_simple_labels :
    ∃ labels : Finset (CategoryTheory.Center C.Obj),
      (∀ T ∈ labels, Simple T) ∧
      ∀ X : CategoryTheory.Center C.Obj, Simple X → ∃ T ∈ labels, Nonempty (X ≅ T) := by
  classical
  let L (i : Fin (rank C)) := Classical.choose (finite_simple_subobject_labels C
    ((induction C).obj (simples C i)))
  have hL (i : Fin (rank C)) := Classical.choose_spec (finite_simple_subobject_labels C
    ((induction C).obj (simples C i)))
  let labels := (Finset.univ.biUnion (fun i => (L i).toFinset)).filter Simple
  refine ⟨labels, ?_, ?_⟩
  · intro T hT
    exact (Finset.mem_filter.mp hT).2
  · intro X hX
    let : Simple X := hX
    obtain ⟨i, t, ht⟩ := simple_mono_induced_simple C X
    obtain ⟨T, hT, ⟨e⟩⟩ := hL i X hX ⟨t, ht⟩
    refine ⟨T, Finset.mem_filter.mpr ⟨?_, Simple.of_iso e.symm⟩, ⟨e⟩⟩
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, List.mem_toFinset.mpr hT⟩

/-- A finite family of pairwise nonisomorphic centre simples represents every simple. -/
theorem finite_simple_representatives :
    ∃ (n : ℕ) (S : Fin n → CategoryTheory.Center C.Obj),
      (∀ i, Simple (S i)) ∧
      (∀ i j, Nonempty (S i ≅ S j) → i = j) ∧
      (∀ X : CategoryTheory.Center C.Obj, Simple X → ∃ i, Nonempty (X ≅ S i)) := by
  obtain ⟨labels, hs, hc⟩ := finite_simple_labels C
  exact simple_representatives_of_finite_cover labels hs hc

end PropertyF.Ground.CentreInduction
