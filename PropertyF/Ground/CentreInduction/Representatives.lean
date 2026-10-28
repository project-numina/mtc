module
public import PropertyF.Ground.CentreInduction.FiniteSum
public import PropertyF.Ground.CentreInduction.Adjunction

/-! Converting binary simple sums to indexed finite biproducts. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace PropertyF.Ground.CentreInduction
universe v u
variable {D : Type u} [Category.{v} D] [Preadditive D] [HasFiniteBiproducts D] [HasBinaryBiproducts D]

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- A binary sum with a finite biproduct is a biproduct indexed by `Option`. -/
def biprodOptionIso {ι : Type} [Fintype ι] (S : D) (V : ι → D) :
    S ⊞ (⨁ V) ≅ ⨁ (fun o : Option ι => o.elim S V) := by
  classical
  let W : Option ι → D := fun o => o.elim S V
  refine { hom := biprod.desc (biproduct.ι W none)
              (biproduct.desc fun i => biproduct.ι W (some i))
           inv := biproduct.desc (fun o => ?_)
           hom_inv_id := ?_
           inv_hom_id := ?_ }
  · cases o with
    | none => exact biprod.inl
    | some i => exact biproduct.ι V i ≫ biprod.inr
  · apply biprod.hom_ext'
    · simp
    · apply biproduct.hom_ext'
      intro i
      simp
  · apply biproduct.hom_ext'
    intro o
    cases o with
    | none => simp [W]
    | some i => simp [W, Category.assoc]

/-- An iterated finite binary sum of simples admits a presentation as a
single finite biproduct of simple objects. -/
theorem finiteSimpleSum_biproduct {X : D} (hX : FiniteSimpleSum D X) :
    ∃ (n : ℕ) (V : Fin n → D), (∀ i, Simple (V i)) ∧ Nonempty (X ≅ ⨁ V) := by
  classical
  induction hX with
  | zero hz =>
    let V : Fin 0 → D := Fin.elim0
    have hzero : IsZero (⨁ V) := (IsZero.iff_id_eq_zero _).mpr (by
      apply biproduct.hom_ext
      intro i
      exact Fin.elim0 i)
    exact ⟨0, V, by intro i; exact Fin.elim0 i, ⟨hz.iso hzero⟩⟩
  | @cons X S K hs hk he ih =>
    obtain ⟨n, V, hv, ⟨e⟩⟩ := ih
    obtain ⟨eX⟩ := he
    let W : Option (Fin n) → D := fun i => i.elim S V
    let W' : Fin (n + 1) → D := fun i => W (finSuccEquiv n i)
    refine ⟨n + 1, W', ?_, ?_⟩
    · intro i
      change Simple (W (finSuccEquiv n i))
      cases h : finSuccEquiv n i with
      | none => exact hs
      | some j => exact hv j
    · let ei : Option (Fin n) ≃ Fin (n + 1) := (finSuccEquiv n).symm
      let er : (⨁ W) ≅ ⨁ W' := biproduct.whiskerEquiv ei (fun i => eqToIso (by simp [W', ei]))
      exact ⟨eX ≪≫ biprod.mapIso (Iso.refl S) e ≪≫ biprodOptionIso S V ≪≫ er⟩

end PropertyF.Ground.CentreInduction

end

/-! Distinct finite representatives of simple objects in the centre. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace PropertyF.Ground.CentreInduction
universe v u

/-- A finite covering family of simples can be deduplicated up to isomorphism. -/
theorem simple_representatives_of_finite_cover {D : Type u} [Category.{v} D] [HasZeroMorphisms D]
    {labels : Finset D} (hs : ∀ T ∈ labels, Simple T)
    (hc : ∀ X : D, Simple X → ∃ T ∈ labels, Nonempty (X ≅ T)) :
    ∃ (n : ℕ) (S : Fin n → D),
      (∀ i, Simple (S i)) ∧
      (∀ i j, Nonempty (S i ≅ S j) → i = j) ∧
      (∀ X : D, Simple X → ∃ i, Nonempty (X ≅ S i)) := by
  classical
  let A := { T : D // T ∈ labels }
  let R : Setoid A := Setoid.comap Subtype.val (isIsomorphicSetoid D)
  let Q := Quotient R
  let : Finite Q := Finite.of_surjective (Quotient.mk R) Quotient.mk_surjective
  let : Fintype Q := Fintype.ofFinite Q
  let e : Q ≃ Fin (Fintype.card Q) := Fintype.equivFin Q
  let S : Fin (Fintype.card Q) → D := fun i => (Quotient.out (e.symm i)).1
  refine ⟨Fintype.card Q, S, ?_, ?_, ?_⟩
  · intro i
    exact hs _ (Quotient.out (e.symm i)).2
  · intro i j hij
    apply e.symm.injective
    have hh : Quotient.mk R (Quotient.out (e.symm i)) =
        Quotient.mk R (Quotient.out (e.symm j)) := Quotient.sound hij
    simpa using hh
  · intro X hX
    obtain ⟨T, hT, ⟨iso⟩⟩ := hc X hX
    let t : A := ⟨T, hT⟩
    let q : Q := Quotient.mk R t
    have hq : R t (Quotient.out q) := Quotient.exact (by simp [q])
    change Nonempty (T ≅ (Quotient.out q).1) at hq
    refine ⟨e q, ?_⟩
    simpa [S] using (show Nonempty (X ≅ (Quotient.out q).1) from
      ⟨iso ≪≫ Classical.choice hq⟩)

/-- Group finitely many objects by chosen representative labels. -/
theorem regroup_biproduct {D : Type u} [Category.{v} D] [Preadditive D]
    [HasFiniteBiproducts D] {n k : ℕ} {S : Fin n → D} {V : Fin k → D}
    (h : ∀ j, ∃ i, Nonempty (V j ≅ S i)) :
    ∃ m : Fin n → ℕ, Nonempty ((⨁ V) ≅ ⨁ (fun p : Σ i, Fin (m i) => S p.1)) := by
  classical
  choose idx hIso using h
  let fiber (i : Fin n) := { j : Fin k // idx j = i }
  let m (i : Fin n) := Fintype.card (fiber i)
  let e (i : Fin n) : fiber i ≃ Fin (m i) := Fintype.equivFin (fiber i)
  let E : (Σ i, Fin (m i)) ≃ Fin k :=
    (Equiv.sigmaCongrRight (fun i => (e i).symm)).trans (Equiv.sigmaFiberEquiv idx)
  have hE (p : Σ i, Fin (m i)) : idx (E p) = p.1 := by
    change idx ((e p.1).symm p.2).1 = p.1
    exact ((e p.1).symm p.2).2
  let W : (Σ i, Fin (m i)) → D := fun p => S p.1
  refine ⟨m, ⟨(biproduct.whiskerEquiv E ?_).symm⟩⟩
  intro p
  have hiso := hIso (E p)
  rw [hE p] at hiso
  exact Classical.choice hiso

end PropertyF.Ground.CentreInduction
