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
  have hs : s ≫ q = 𝟙 Q := IsSplitEpi.id q
  let L : (Q ⟶ Q) →ₗ[k] (W ⟶ W) :=
    (Linear.leftComp k W q).comp (Linear.rightComp k Q s)
  have hinj : Function.Injective L := by
    intro x y h
    have hh := congrArg (fun f => s ≫ f ≫ q) h
    simpa [L, s, Category.assoc, hs] using hh
  have hproper : LinearMap.range L ≠ ⊤ := by
    intro hall
    have hh : (𝟙 W) ∈ LinearMap.range L := by rw [hall]; trivial
    obtain ⟨x, hx⟩ := hh
    have he := congrArg (fun f => p ≫ f) hx
    apply hp
    change p ≫ (q ≫ x ≫ s) = p ≫ 𝟙 W at he
    simpa only [← Category.assoc, hq, zero_comp, Category.comp_id] using he.symm
  have hlt := Submodule.finrank_lt_finrank_of_lt (lt_top_iff_ne_top.mpr hproper)
  rw [finrank_top, LinearMap.finrank_range_of_inj hinj] at hlt
  exact hlt

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
      have hs : ¬ IsZero S := Simple.not_isZero _
      have he : Module.finrank k (Z ⟶ Z) = Module.finrank k (S ⊞ K ⟶ S ⊞ K) :=
        (CategoryTheory.Linear.homCongr k e e).finrank_eq
      have hk : m K < m Z := by
        change Module.finrank k (K ⟶ K) < Module.finrank k (Z ⟶ Z)
        rw [he]
        exact finrank_end_complement_lt _ K hs
      exact .cons hS (ih K hk) ⟨e⟩


end PropertyF.Ground.CentreInduction
