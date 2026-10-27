module
public import PropertyF.Ground.CentreInduction.FiniteSum
public import PropertyF.Ground.CentreInduction.Adjunction

/-! Simple centre objects and induced base simples. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace PropertyF.Ground.CentreInduction
universe v u

set_option backward.isDefEq.respectTransparency false in
/-- Each simple centre object is a retract of an induced base simple, assuming
only a right adjoint and the stated loop-sliding identity. This does not
construct that adjoint. -/
theorem simple_retract_induced_simple (C : BraidedFusionCategory.{v,u})
    (p : Dimensions.PivotalStructure (C := C.Obj)) (hp : p.IsSpherical)
    (hslide : SimpleLoopCentrality C p) (hne : globalDimension C ≠ 0)
    (I : C.Obj ⥤ CategoryTheory.Center C.Obj)
    (adj : CategoryTheory.Center.forget C.Obj ⊣ I)
    (X : CategoryTheory.Center C.Obj) [Simple X] :
    ∃ i : Fin (rank C), Nonempty (Retract X (I.obj (simples C i))) := by
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
  let e := homLinearEquivOfAdjunction (CategoryTheory.Center.forget C.Obj) I adj X (simples C i)
  let t : X ⟶ I.obj (simples C i) := e.symm g
  have ht : t ≠ 0 := by
    intro ht
    apply hg
    have := congrArg e ht
    simpa [t] using this
  letI : Mono t := mono_of_nonzero_from_simple ht
  letI : IsSplitMono t := mono_splits_of_loop_centrality C p hp hslide hne t
  exact ⟨i, ⟨{ i := t, r := retraction t }⟩⟩

/-- A finite simple sum has only finitely many isomorphism classes among its
simple retracts. -/
theorem finite_simple_retract_labels (C : BraidedFusionCategory.{v,u})
    (p : Dimensions.PivotalStructure (C := C.Obj)) (hp : p.IsSpherical)
    (hslide : SimpleLoopCentrality C p) (hne : globalDimension C ≠ 0)
    (W : CategoryTheory.Center C.Obj) (hW : FiniteSimpleSum (CategoryTheory.Center C.Obj) W) :
    ∃ L : List (CategoryTheory.Center C.Obj),
      (∀ T ∈ L, Simple T) ∧
      ∀ (X : CategoryTheory.Center C.Obj), Simple X → Nonempty (Retract X W) →
        ∃ T ∈ L, Nonempty (X ≅ T) := by
  induction hW with
  | zero hz =>
    refine ⟨[], by simp, ?_⟩
    intro X hX ⟨r⟩
    letI : Simple X := hX
    have hi : r.i = 0 := hz.eq_of_tgt r.i 0
    have : (𝟙 X : X ⟶ X) = 0 := by simpa [hi] using r.retract.symm
    exact (id_nonzero X this).elim
  | @cons W S K hS hK he ih =>
    obtain ⟨L, hL, hcover⟩ := ih
    refine ⟨S :: L, ?_, ?_⟩
    · intro T hT
      simp only [List.mem_cons] at hT
      rcases hT with rfl | hT
      · exact hS
      · exact hL T hT
    · intro X hX ⟨r⟩
      letI : Simple X := hX
      letI : Simple S := hS
      obtain ⟨e⟩ := he
      let a := r.i ≫ e.hom
      have ha : a ≠ 0 := by
        intro ha
        have hi : r.i = 0 := by
          have hh := congrArg (fun f => f ≫ e.inv) ha
          simpa [a, Category.assoc] using hh
        have : (𝟙 X : X ⟶ X) = 0 := by simpa [hi] using r.retract.symm
        exact id_nonzero X this
      by_cases hs : a ≫ biprod.fst = 0
      · have hk : a ≫ biprod.snd ≠ 0 := by
          intro hk
          apply ha
          apply biprod.hom_ext <;> simpa [hs, hk]
        letI : Mono (a ≫ biprod.snd) := mono_of_nonzero_from_simple hk
        letI : IsSplitMono (a ≫ biprod.snd) :=
          mono_splits_of_loop_centrality C p hp hslide hne (a ≫ biprod.snd)
        obtain ⟨T, hT, hiso⟩ := hcover X hX
          ⟨{ i := a ≫ biprod.snd, r := retraction (a ≫ biprod.snd) }⟩
        exact ⟨T, by simp [hT], hiso⟩
      · letI : IsIso (a ≫ biprod.fst) := isIso_of_hom_simple hs
        exact ⟨S, by simp, ⟨asIso (a ≫ biprod.fst)⟩⟩

/-- The induction adjunction and loop sliding imply that a finite set of
actual centre simples covers all simple objects up to isomorphism. The
adjunction and sliding identity remain explicit, unproved assumptions. -/
theorem finite_simple_labels_of_adjunction_and_loop (C : BraidedFusionCategory.{v,u})
    (p : Dimensions.PivotalStructure (C := C.Obj)) (hp : p.IsSpherical)
    (hslide : SimpleLoopCentrality C p) (hne : globalDimension C ≠ 0)
    (I : C.Obj ⥤ CategoryTheory.Center C.Obj)
    (adj : CategoryTheory.Center.forget C.Obj ⊣ I) :
    ∃ labels : Finset (CategoryTheory.Center C.Obj),
      (∀ T ∈ labels, Simple T) ∧
      ∀ X : CategoryTheory.Center C.Obj, Simple X → ∃ T ∈ labels, Nonempty (X ≅ T) := by
  classical
  let L (i : Fin (rank C)) := Classical.choose (finite_simple_retract_labels C p hp hslide hne
    (I.obj (simples C i)) (center_finite_simple_sum_of_loop_centrality C p hp hslide hne _))
  have hL (i : Fin (rank C)) := Classical.choose_spec (finite_simple_retract_labels C p hp hslide hne
    (I.obj (simples C i)) (center_finite_simple_sum_of_loop_centrality C p hp hslide hne _))
  refine ⟨Finset.univ.biUnion (fun i => (L i).toFinset), ?_, ?_⟩
  · intro T hT
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hT
    exact (hL i).1 T (List.mem_toFinset.mp hi)
  · intro X hX
    letI : Simple X := hX
    obtain ⟨i, hr⟩ := simple_retract_induced_simple C p hp hslide hne I adj X
    obtain ⟨T, hT, he⟩ := (hL i).2 X hX hr
    refine ⟨T, Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, ?_⟩, he⟩
    exact List.mem_toFinset.mpr hT

end PropertyF.Ground.CentreInduction
