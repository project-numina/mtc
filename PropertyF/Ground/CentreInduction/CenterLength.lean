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

/-- Every actual centre object is Noetherian, without spherical hypotheses. -/
theorem center_noetherian (X : CategoryTheory.Center C.Obj) : IsNoetherianObject X := by
  letI : FiniteDimensional ℂ (X.1 ⟶ X.1) := IsFusionCategory.hom_finite _ _
  exact ⟨(centerUnderlyingRangeEmbedding C X).wellFoundedGT⟩

end PropertyF.Ground.CentreInduction
