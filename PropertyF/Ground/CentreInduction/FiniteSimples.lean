module
public import PropertyF.Ground.CentreInduction.CenterLength

/-! Finiteness of simple objects in the actual Drinfeld centre. -/
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
universe v u
@[expose] public noncomputable section
namespace PropertyF.Ground.CentreInduction
variable (C : BraidedFusionCategory.{v,u})

set_option backward.isDefEq.respectTransparency false in
/-- A nonzero centre subobject strictly decreases the underlying endomorphism dimension on quotient. -/
theorem center_cokernel_measure_lt {S W : CategoryTheory.Center C.Obj}
    (p : S ⟶ W) [Mono p] (hp : p ≠ 0) :
    Module.finrank ℂ ((PropertyF.Ground.Centre.centerCokernel p).1 ⟶
      (PropertyF.Ground.Centre.centerCokernel p).1) < Module.finrank ℂ (W.1 ⟶ W.1) := by
  let Q := PropertyF.Ground.Centre.centerCokernel p
  let q : W.1 ⟶ Q.1 := (PropertyF.Ground.Centre.centerCokernelπ p).f
  have hq : p.f ≫ q = 0 := congrArg CategoryTheory.Center.Hom.f (PropertyF.Ground.Centre.centerCokernel_condition p)
  have : Epi q := by
    change Epi (cokernel.π p.f)
    infer_instance
  letI : IsSplitEpi q := epi_splits C q
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
  letI : FiniteDimensional ℂ (W.1 ⟶ W.1) := IsFusionCategory.hom_finite _ _
  letI : FiniteDimensional ℂ (Q.1 ⟶ Q.1) := IsFusionCategory.hom_finite _ _
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
      letI : Simple S := hS
      letI : Mono t := ht
      have ht0 : t = 0 := hw.eq_of_tgt _ _
      have hid : 𝟙 S = 0 := by
        apply (cancel_mono t).1
        simp [ht0]
      exact (id_nonzero S hid).elim
    · letI : IsArtinianObject W := center_artinian C W
      obtain ⟨P, hP⟩ := exists_simple_subobject hw
      letI : Simple (P : CategoryTheory.Center C.Obj) := hP
      let p : (P : CategoryTheory.Center C.Obj) ⟶ W := P.arrow
      have hp : p ≠ 0 := by
        intro h0
        have hid : 𝟙 (P : CategoryTheory.Center C.Obj) = 0 := by
          apply (cancel_mono p).1
          simp [h0]
        exact id_nonzero _ hid
      let Q := PropertyF.Ground.Centre.centerCokernel p
      let q : W ⟶ Q := PropertyF.Ground.Centre.centerCokernelπ p
      have hlt : m Q < m W := center_cokernel_measure_lt C p hp
      obtain ⟨L, hL⟩ := ih Q hlt
      refine ⟨(P : CategoryTheory.Center C.Obj) :: L, ?_⟩
      intro S hS ⟨t, ht⟩
      letI : Simple S := hS
      letI : Mono t := ht
      have ht0 : t ≠ 0 := by
        intro h0
        have hid : 𝟙 S = 0 := by
          apply (cancel_mono t).1
          simp [h0]
        exact id_nonzero S hid
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
        letI : IsIso g := isIso_of_hom_simple hg0
        exact ⟨P, by simp, ⟨asIso g⟩⟩
      · letI : Mono (t ≫ q) := mono_of_nonzero_from_simple hz
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
    letI : Simple X := hX
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
