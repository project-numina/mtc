module
public import Mathlib.CategoryTheory.Abelian.Exact
public import Mathlib.CategoryTheory.Simple
public import Mathlib.CategoryTheory.Preadditive.Schur
public import Mathlib.CategoryTheory.Linear.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! A finite-step semisimple decomposition from split subobjects. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits Module
namespace MTC.Center.Induction
universe v u
variable {k : Type*} [Field k] {D : Type u} [Category.{v} D] [Preadditive D] [Linear k D]
  [HasBinaryBiproducts D]
variable {S W Q : D}

omit [HasBinaryBiproducts D] in
/-- A split epimorphism with a nonzero annihilated map decreases endomorphism dimension. -/
theorem finrank_end_lt_of_split_epi (p : S ⟶ W) (q : W ⟶ Q)
    [IsSplitEpi q] [FiniteDimensional k (W ⟶ W)]
    (hp : p ≠ 0) (hq : p ≫ q = 0) :
    finrank k (Q ⟶ Q) < finrank k (W ⟶ W) := by
  let s : Q ⟶ W := section_ q
  let L : (Q ⟶ Q) →ₗ[k] (W ⟶ W) :=
    (Linear.leftComp k W q).comp (Linear.rightComp k Q s)
  have hinj : Function.Injective L := fun x y h => by
    simpa [L, s, Category.assoc] using congrArg (fun f => s ≫ f ≫ q) h
  have hproper : LinearMap.range L ≠ ⊤ := fun hall =>
    let ⟨x, hx⟩ := (LinearMap.range_eq_top.mp hall) (𝟙 W)
    hp <| by simpa [L, s, ← Category.assoc, hq] using (congrArg (fun f => p ≫ f) hx).symm
  simpa only [finrank_top, LinearMap.finrank_range_of_inj hinj] using
    Submodule.finrank_lt_finrank_of_lt (lt_top_iff_ne_top.mpr hproper)

/-- Removing a nonzero direct summand strictly decreases the dimension of the
endomorphism space. -/
theorem finrank_end_complement_lt (K : D)
    [FiniteDimensional k (S ⊞ K ⟶ S ⊞ K)] (hS : ¬ IsZero S) :
    finrank k (K ⟶ K) < finrank k (S ⊞ K ⟶ S ⊞ K) :=
  finrank_end_lt_of_split_epi (k := k) biprod.inl biprod.snd
    ((IsZero.iff_isSplitMono_eq_zero (biprod.inl : S ⟶ S ⊞ K)).not.mp hS) biprod.inl_snd

/-- Objects built from finitely many simple objects by binary direct sums,
up to isomorphism. -/
inductive FiniteSimpleSum {D : Type u} [Category.{v} D] [Preadditive D]
    [HasBinaryBiproducts D] : D → Prop
  | zero {X} : IsZero X → FiniteSimpleSum X
  | cons {X S K} : Simple S → FiniteSimpleSum K → Nonempty (X ≅ S ⊞ K) →
      FiniteSimpleSum X

attribute [local instance] Abelian.hasFiniteBiproducts

/-- Finite-dimensional injective objects with simple subobjects split into finite simple sums. -/
theorem finiteSimpleSum_of_injective {E : Type u} [Category.{v} E] [Abelian E] [Linear k E]
    [(A : E) → FiniteDimensional k (A ⟶ A)] [(Z : E) → Injective Z]
    (hasSimple : ∀ {Z : E}, ¬ IsZero Z → ∃ (S : E) (f : S ⟶ Z), Simple S ∧ Mono f)
    (Z : E) : FiniteSimpleSum Z := by
  induction Z using (measure fun W : E => finrank k (W ⟶ W)).wf.induction with
  | h Z ih =>
    by_cases hz : IsZero Z
    · exact .zero hz
    · obtain ⟨S, f, hS, hf⟩ := hasSimple hz
      let : Simple S := hS
      let : Mono f := hf
      obtain ⟨r, hr⟩ := Injective.factors (𝟙 S) f
      let e : Z ≅ S ⊞ cokernel f :=
        (ShortComplex.Splitting.ofExactOfRetraction (ShortComplex.cokernelSequence f)
          (ShortComplex.cokernelSequence_exact f) r hr inferInstance).isoBinaryBiproduct
      exact .cons hS (ih (cokernel f) (by
        change finrank k (cokernel f ⟶ cokernel f) < finrank k (Z ⟶ Z)
        simpa only [(CategoryTheory.Linear.homCongr k e e).finrank_eq] using
          finrank_end_complement_lt (k := k) (cokernel f) (Simple.not_isZero S))) ⟨e⟩

end MTC.Center.Induction

end

/-! Converting binary simple sums to indexed finite biproducts. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace MTC.Center.Induction
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
           inv := biproduct.desc (fun o => Option.rec (motive := fun o => W o ⟶ S ⊞ ⨁ V)
             biprod.inl (fun i => biproduct.ι V i ≫ biprod.inr) o)
           hom_inv_id := ?_
           inv_hom_id := ?_ }
  · refine biprod.hom_ext' _ _ ?_ (biproduct.hom_ext' _ _ fun i => ?_)
    · simp [W]
    · simp
  · refine biproduct.hom_ext' _ _ fun o => ?_
    cases o <;> simp [W, Category.assoc]

/-- An iterated finite binary sum of simples admits a presentation as a
single finite biproduct of simple objects. -/
theorem finiteSimpleSum_biproduct {X : D} (hX : FiniteSimpleSum X) :
    ∃ (n : ℕ) (V : Fin n → D), (∀ i, Simple (V i)) ∧ Nonempty (X ≅ ⨁ V) := by
  induction hX with
  | zero hz =>
    exact ⟨0, Fin.elim0, fun i => Fin.elim0 i, ⟨hz.iso ((IsZero.iff_id_eq_zero _).2
      (biproduct.hom_ext' _ _ fun i => Fin.elim0 i))⟩⟩
  | @cons X S K hs hk he ih =>
    obtain ⟨n, V, hv, ⟨e⟩⟩ := ih
    obtain ⟨eX⟩ := he
    refine ⟨n + 1, fun i ↦ (finSuccEquiv n i).elim S V, fun i ↦
      Option.rec (motive := fun o ↦ Simple (o.elim S V)) hs hv (finSuccEquiv n i), ⟨?_⟩⟩
    exact eX ≪≫ biprod.mapIso (Iso.refl S) e ≪≫ biprodOptionIso S V ≪≫
      biproduct.whiskerEquiv (finSuccEquiv n).symm (fun i => eqToIso (by simp))

end MTC.Center.Induction

end

/-! Distinct finite representatives of simple objects in the centre. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace MTC.Center.Induction
universe v u
variable {D : Type u} [Category.{v} D]

/-- A family contains one representative of each isomorphism class of simples. -/
abbrev IsSimpleRepresentativeFamily [HasZeroMorphisms D]
    {ι : Type*} (S : ι → D) : Prop :=
  (∀ i, Simple (S i)) ∧
    (∀ i j, Nonempty (S i ≅ S j) → i = j) ∧
    ∀ X : D, Simple X → ∃ i, Nonempty (X ≅ S i)

/-- A finite covering family of simples can be deduplicated up to isomorphism. -/
theorem simple_representatives_of_finite_cover [HasZeroMorphisms D]
    {labels : Finset D} (hs : ∀ T ∈ labels, Simple T)
    (hc : ∀ X : D, Simple X → ∃ T ∈ labels, Nonempty (X ≅ T)) :
    ∃ (n : ℕ) (S : Fin n → D), IsSimpleRepresentativeFamily S := by
  let A := { T : D // T ∈ labels }
  let R : Setoid A := Setoid.comap Subtype.val (isIsomorphicSetoid D)
  let Q := Quotient R
  let : Finite Q := Finite.of_surjective (Quotient.mk R) Quotient.mk_surjective
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin Q
  let S : Fin n → D := fun i => (Quotient.out (e.symm i)).1
  refine ⟨n, S, fun i => hs _ (Quotient.out (e.symm i)).2, ?_, fun X hX => ?_⟩
  · exact fun i j hij => e.symm.injective (by
      simpa using (Quotient.sound hij : Quotient.mk R (Quotient.out (e.symm i)) =
        Quotient.mk R (Quotient.out (e.symm j))))
  · obtain ⟨T, hT, ⟨iso⟩⟩ := hc X hX
    let q : Q := Quotient.mk R ⟨T, hT⟩
    refine ⟨e q, ?_⟩
    simpa [S] using (show Nonempty (X ≅ (Quotient.out q).1) from
      ⟨iso ≪≫ Classical.choice (Quotient.exact (Quotient.out_eq q).symm)⟩)

/-- A simple object with a nonzero map into a finite sum of simples is a summand. -/
theorem simple_iso_biproduct_summand [Preadditive D] [HasKernels D] [HasFiniteBiproducts D]
    {ι : Type*} [Fintype ι] {V : ι → D} (hV : ∀ i, Simple (V i))
    {Z : D} [Simple Z] (f : Z ⟶ ⨁ V) (hf : f ≠ 0) :
    ∃ i, Nonempty (Z ≅ V i) := by
  obtain ⟨i, hi⟩ : ∃ i, f ≫ biproduct.π V i ≠ 0 := by
    by_contra! h
    apply hf
    exact biproduct.hom_ext _ _ fun i => by simpa only [zero_comp] using h i
  let : Simple (V i) := hV i
  let : IsIso (f ≫ biproduct.π V i) := isIso_of_hom_simple hi
  exact ⟨i, ⟨asIso (f ≫ biproduct.π V i)⟩⟩

/-- Group finitely many objects by chosen representative labels. -/
theorem regroup_biproduct [Preadditive D]
    [HasFiniteBiproducts D] {n k : ℕ} {S : Fin n → D} {V : Fin k → D}
    (h : ∀ j, ∃ i, Nonempty (V j ≅ S i)) :
    ∃ m : Fin n → ℕ, Nonempty ((⨁ V) ≅ ⨁ (fun p : Σ i, Fin (m i) => S p.1)) := by
  choose idx hIso using h
  let fiber (i : Fin n) := { j : Fin k // idx j = i }
  let m (i : Fin n) := Fintype.card (fiber i)
  let e (i : Fin n) : fiber i ≃ Fin (m i) := Fintype.equivFin (fiber i)
  let E : (Σ i, Fin (m i)) ≃ Fin k :=
    (Equiv.sigmaCongrRight (fun i => (e i).symm)).trans (Equiv.sigmaFiberEquiv idx)
  have hE (p : Σ i, Fin (m i)) : idx (E p) = p.1 := ((e p.1).symm p.2).2
  exact ⟨m, ⟨(biproduct.whiskerEquiv E fun p =>
    Classical.choice (by simpa only [hE] using hIso (E p))).symm⟩⟩

end MTC.Center.Induction
