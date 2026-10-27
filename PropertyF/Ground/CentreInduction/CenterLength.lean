module
public import PropertyF.Ground.CentreInduction.ActualFusion
public import PropertyF.Ground.CentreInduction.Artinian
public import PropertyF.Ground.Fusion.SemisimpleSplit
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
    letI : IsSplitMono q.f := mono_splits C q.f
    letI : IsSplitMono (T ◁ q.f) := IsSplitMono.mk'
      { retraction := T ◁ retraction q.f
        id := by rw [← whiskerLeft_comp, IsSplitMono.id, whiskerLeft_id] }
    apply (cancel_mono (T ◁ q.f)).1
    have hq := congrArg (fun k => (g ▷ T) ≫ k) (q.comm T).symm
    have hg' := congrArg (fun k => (k ▷ T) ≫ (X.2.β T).hom) hg
    calc
      _ = (g ▷ T) ≫ (q.f ▷ T) ≫ ((X.2.β T).hom) := by simpa [Category.assoc] using hq
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
      letI : IsSplitMono P.arrow.f := mono_splits C P.arrow.f
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
  letI : FiniteDimensional ℂ (X.1 ⟶ X.1) := IsFusionCategory.hom_finite _ _
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
  letI : FiniteDimensional ℂ (X.1 ⟶ simples C i) := IsFusionCategory.hom_finite _ _
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
