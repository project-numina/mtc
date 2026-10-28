module
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

/-! A finite-step semisimple decomposition from split subobjects. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace PropertyF.Ground.CentreInduction
universe v u
variable {k : Type*} [Field k] {D : Type u} [Category.{v} D] [Preadditive D] [Linear k D]
  [HasBinaryBiproducts D]

omit [HasBinaryBiproducts D] in
/-- A split epimorphism with a nonzero annihilated map decreases endomorphism dimension. -/
theorem finrank_end_lt_of_split_epi {S W Q : D} (p : S ⟶ W) (q : W ⟶ Q)
    [IsSplitEpi q] [FiniteDimensional k (W ⟶ W)]
    (hp : p ≠ 0) (hq : p ≫ q = 0) :
    Module.finrank k (Q ⟶ Q) < Module.finrank k (W ⟶ W) := by
  let s : Q ⟶ W := section_ q
  let L : (Q ⟶ Q) →ₗ[k] (W ⟶ W) :=
    (Linear.leftComp k W q).comp (Linear.rightComp k Q s)
  have hinj : Function.Injective L := by
    intro x y h
    simpa [L, s, Category.assoc] using congrArg (fun f => s ≫ f ≫ q) h
  have hproper : LinearMap.range L ≠ ⊤ := by
    intro hall
    obtain ⟨x, hx⟩ := (LinearMap.range_eq_top.mp hall) (𝟙 W)
    have he := congrArg (fun f => p ≫ f) hx
    apply hp
    change p ≫ (q ≫ x ≫ s) = p ≫ 𝟙 W at he
    simpa only [← Category.assoc, hq, zero_comp, Category.comp_id] using he.symm
  simpa only [finrank_top, LinearMap.finrank_range_of_inj hinj] using
    Submodule.finrank_lt_finrank_of_lt (lt_top_iff_ne_top.mpr hproper)

/-- Removing a nonzero direct summand strictly decreases the dimension of the
endomorphism space. -/
theorem finrank_end_complement_lt (S K : D)
    [FiniteDimensional k (S ⊞ K ⟶ S ⊞ K)] (hS : ¬ IsZero S) :
    Module.finrank k (K ⟶ K) < Module.finrank k (S ⊞ K ⟶ S ⊞ K) :=
  finrank_end_lt_of_split_epi (k := k) biprod.inl biprod.snd
    ((IsZero.iff_isSplitMono_eq_zero (biprod.inl : S ⟶ S ⊞ K)).not.mp hS) (by simp)

/-- Objects built from finitely many simple objects by binary direct sums,
up to isomorphism. -/
inductive FiniteSimpleSum (D : Type u) [Category.{v} D] [Preadditive D]
    [HasBinaryBiproducts D] : D → Prop
  | zero {X} : IsZero X → FiniteSimpleSum D X
  | cons {X S K} : Simple S → FiniteSimpleSum D K → Nonempty (X ≅ S ⊞ K) →
      FiniteSimpleSum D X

attribute [local instance] Abelian.hasFiniteBiproducts

/-- Finite-dimensional injective objects with simple subobjects split into finite simple sums. -/
theorem finiteSimpleSum_of_injective {E : Type u} [Category.{v} E] [Abelian E] [Linear k E]
    [(A B : E) → FiniteDimensional k (A ⟶ B)] [(Z : E) → Injective Z]
    (hasSimple : ∀ {Z : E}, ¬ IsZero Z → ∃ (S : E) (f : S ⟶ Z), Simple S ∧ Mono f)
    (Z : E) : FiniteSimpleSum E Z := by
  let m : E → ℕ := fun W => Module.finrank k (W ⟶ W)
  induction Z using (measure m).wf.induction with
  | h Z ih =>
    by_cases hz : IsZero Z
    · exact .zero hz
    · obtain ⟨S, f, hS, hf⟩ := hasSimple hz
      let : Simple S := hS
      let : Mono f := hf
      obtain ⟨r, hr⟩ := Injective.factors (𝟙 S) f
      let seq := ShortComplex.cokernelSequence f
      let split : seq.Splitting := ShortComplex.Splitting.ofExactOfRetraction seq
        (ShortComplex.cokernelSequence_exact f) r hr inferInstance
      let K := cokernel f
      let e : Z ≅ S ⊞ K := split.isoBinaryBiproduct
      have hk : m K < m Z := by
        change Module.finrank k (K ⟶ K) < Module.finrank k (Z ⟶ Z)
        rw [(CategoryTheory.Linear.homCongr k e e).finrank_eq]
        exact finrank_end_complement_lt _ K (Simple.not_isZero _)
      exact .cons hS (ih K hk) ⟨e⟩

end PropertyF.Ground.CentreInduction

end

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

/-- A family contains one representative of each isomorphism class of simples. -/
abbrev IsSimpleRepresentativeFamily {D : Type u} [Category.{v} D] [HasZeroMorphisms D]
    {ι : Type*} (S : ι → D) : Prop :=
  (∀ i, Simple (S i)) ∧
    (∀ i j, Nonempty (S i ≅ S j) → i = j) ∧
    ∀ X : D, Simple X → ∃ i, Nonempty (X ≅ S i)

/-- A finite covering family of simples can be deduplicated up to isomorphism. -/
theorem simple_representatives_of_finite_cover {D : Type u} [Category.{v} D] [HasZeroMorphisms D]
    {labels : Finset D} (hs : ∀ T ∈ labels, Simple T)
    (hc : ∀ X : D, Simple X → ∃ T ∈ labels, Nonempty (X ≅ T)) :
    ∃ (n : ℕ) (S : Fin n → D), IsSimpleRepresentativeFamily S := by
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
    simpa using (Quotient.sound hij : Quotient.mk R (Quotient.out (e.symm i)) =
      Quotient.mk R (Quotient.out (e.symm j)))
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
  exact Classical.choice (by simpa only [hE] using hIso (E p))

end PropertyF.Ground.CentreInduction
