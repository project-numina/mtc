module
public import PropertyF.Ground.Integrate.ExampleDimensions
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import PropertyF.Ground.Modular.BraidFunctor

/-! The full target hypotheses are inhabited by finite-dimensional complex
vector spaces. Braid generators permute the tensor-product basis, so their
image lies in a finite basis stabilizer. -/

@[expose] public noncomputable section
set_option linter.style.haveILetI false
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.Example

variable {K W ι : Type*} [Field K] [AddCommGroup W] [Module K W] [Fintype ι]

/-- Linear automorphisms that permute the basis in both directions. -/
def basisStabilizer (b : Module.Basis ι K W) : Subgroup (W ≃ₗ[K] W) where
  carrier := {g | (∀ i, ∃ j, g (b i) = b j) ∧ (∀ i, ∃ j, g.symm (b i) = b j)}
  one_mem' := by
    constructor <;> intro i <;> exact ⟨i, rfl⟩
  mul_mem' := by
    intro f g hf hg
    constructor
    · intro i
      obtain ⟨j, hj⟩ := hg.1 i
      obtain ⟨k, hk⟩ := hf.1 j
      exact ⟨k, by simpa [hj] using hk⟩
    · intro i
      obtain ⟨j, hj⟩ := hf.2 i
      obtain ⟨k, hk⟩ := hg.2 j
      refine ⟨k, ?_⟩
      change g.symm (f.symm (b i)) = b k
      rw [hj, hk]
  inv_mem' := by intro f hf; exact ⟨hf.2, hf.1⟩

/-- A linear automorphism is determined by its values on a finite basis. -/
theorem basisStabilizer_finite (b : Module.Basis ι K W) : Finite (basisStabilizer b) := by
  classical
  let F : basisStabilizer b → ι → ι := fun f i => Classical.choose (f.property.1 i)
  apply Finite.of_injective F
  intro f g h
  apply Subtype.ext
  apply LinearEquiv.toLinearMap_injective
  apply b.ext
  intro i
  have hf := Classical.choose_spec (f.property.1 i)
  have hg := Classical.choose_spec (g.property.1 i)
  have hi := congrFun h i
  change Classical.choose (f.property.1 i) = Classical.choose (g.property.1 i) at hi
  exact hf.trans (by rw [hi]; exact hg.symm)

/-- Interpret categorical module automorphisms as linear equivalences. -/
def autLinear (M : ModuleCat ℂ) : Aut M →* (M ≃ₗ[ℂ] M) where
  toFun f := f.asIso.toLinearEquiv
  map_one' := rfl
  map_mul' _ _ := rfl

theorem autLinear_injective (M : ModuleCat ℂ) : Function.Injective (autLinear M) := by
  intro f g h
  apply Aut.ext
  apply Iso.ext
  apply ModuleCat.hom_ext
  exact congrArg LinearEquiv.toLinearMap h

/-- Indices for the iterated tensor-product basis. -/
def tupleIndex (ι : Type) : ℕ → Type
  | 0 => PUnit
  | n + 1 => ι × tupleIndex ι n

instance tupleIndexFinite {ι : Type} [Fintype ι] (n : ℕ) : Fintype (tupleIndex ι n) := by
  induction n with
  | zero => change Fintype PUnit; infer_instance
  | succ n ih => change Fintype (ι × tupleIndex ι n); infer_instance

open scoped TensorProduct

/-- The tensor-power basis obtained from a basis of the underlying module. -/
def tensorBasis {ι : Type} (M : ModuleCat ℂ) (b : Module.Basis ι ℂ M) :
    ∀ n, Module.Basis (tupleIndex ι n) ℂ ↥(tensorPower M n)
  | 0 => Module.Basis.singleton PUnit ℂ
  | n + 1 => b.tensorProduct (tensorBasis M b n)

theorem tensorBasis_succ {ι : Type} (M : ModuleCat ℂ) (b : Module.Basis ι ℂ M)
    (n : ℕ) (a : ι) (t : tupleIndex ι n) :
    tensorBasis M b (n + 1) (a, t) = b a ⊗ₜ[ℂ] tensorBasis M b n t := by
  exact Module.Basis.tensorProduct_apply b (tensorBasis M b n) a t

/-- Swap adjacent tensor-basis indices. -/
def tupleSwap {ι : Type} : ∀ n, Fin (n + 1) → tupleIndex ι (n + 2) → tupleIndex ι (n + 2)
  | _, ⟨0, _⟩, (a, b, rest) => (b, a, rest)
  | n + 1, ⟨i + 1, hi⟩, (a, rest) =>
    (a, tupleSwap n ⟨i, Nat.lt_of_succ_lt_succ hi⟩ rest)
  | 0, ⟨i + 1, hi⟩, _ => (Nat.not_lt_zero i (Nat.lt_of_succ_lt_succ hi)).elim

set_option backward.isDefEq.respectTransparency false in
/-- An adjacent categorical braid swaps the corresponding basis indices. -/
theorem generator_basis {ι : Type} (M : ModuleCat ℂ) (b : Module.Basis ι ℂ M) :
    ∀ n (k : Fin (n + 1)) (t : tupleIndex ι (n + 2)),
      (braidGenerator M n k).asIso.hom (tensorBasis M b (n + 2) t) =
        tensorBasis M b (n + 2) (tupleSwap n k t) := by
  intro n
  induction n with
  | zero =>
    intro k t
    have hk : k = 0 := Fin.eq_zero k
    subst k
    obtain ⟨a, b', rest⟩ := t
    simp [braidGenerator, tupleSwap, tensorBasis_succ, Iso.trans_hom, tensorIso_hom]
    ; rfl
  | succ n ih =>
    intro k t
    obtain ⟨k, hk⟩ := k
    cases k with
    | zero =>
      obtain ⟨a, b', rest⟩ := t
      simp [braidGenerator, tupleSwap, tensorBasis_succ, Iso.trans_hom, tensorIso_hom]
    ; rfl
    | succ k =>
      obtain ⟨a, rest⟩ := t
      simp only [braidGenerator, tupleSwap, tensorBasis_succ, tensorIso_hom, Iso.refl_hom]
      change b a ⊗ₜ[ℂ] ((braidGenerator M n ⟨k, Nat.lt_of_succ_lt_succ hk⟩).asIso.hom ((tensorBasis M b (n + 2)) rest)) = _
      rw [ih]

theorem tupleSwap_involutive {ι : Type} : ∀ n (k : Fin (n + 1)) (t : tupleIndex ι (n + 2)),
    tupleSwap n k (tupleSwap n k t) = t := by
  intro n
  induction n with
  | zero =>
    intro k t
    have hk : k = 0 := Fin.eq_zero k
    subst k
    obtain ⟨a, b, rest⟩ := t
    rfl
  | succ n ih =>
    intro ⟨k, hk⟩ t
    cases k with
    | zero => obtain ⟨a, b, rest⟩ := t; rfl
    | succ k =>
      obtain ⟨a, rest⟩ := t
      simp only [tupleSwap, ih]
      rfl

/-- Every finite-dimensional complex module has finite braid images. -/
theorem module_objectPropertyF (M : ModuleCat ℂ) [FiniteDimensional ℂ M] : ObjectPropertyF M := by
  intro n
  let b := Module.finBasis ℂ M
  let bt := tensorBasis M b (n + 2)
  let L := autLinear (tensorPower M (n + 2))
  have hsub : braidImage M n ≤ (basisStabilizer bt).comap L := by
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨k, rfl⟩
    change L (braidGenerator M n k) ∈ basisStabilizer bt
    constructor
    · intro t
      exact ⟨tupleSwap n k t, generator_basis M b n k t⟩
    · intro t
      refine ⟨tupleSwap n k t, ?_⟩
      apply (L (braidGenerator M n k)).injective
      rw [LinearEquiv.apply_symm_apply]
      symm
      change (braidGenerator M n k).asIso.hom ((tensorBasis M b (n + 2)) (tupleSwap n k t)) = _
      rw [generator_basis, tupleSwap_involutive]
  letI : Finite (basisStabilizer bt) := basisStabilizer_finite bt
  let F : braidImage M n → basisStabilizer bt := fun g => ⟨L g, hsub g.property⟩
  apply Finite.of_injective F
  intro f g h
  apply Subtype.ext
  apply autLinear_injective
  exact congrArg Subtype.val h

/-- Finite-dimensional complex vector spaces have property F. -/
theorem propertyF : HasPropertyF V := by
  intro X n
  letI : F.Braided := inferInstanceAs ((ModuleCat.isFG ℂ).ι.Braided)
  letI : FiniteDimensional ℂ (F.obj X) := X.property
  letI : Finite (braidImage (F.obj X) n) := module_objectPropertyF (F.obj X) n
  exact Finite.of_equiv (braidImage (F.obj X) n) (Modular.braidImageFunctorIso F X n).toEquiv.symm

/-- The frozen target hypotheses are simultaneously satisfiable. -/
theorem target_hypotheses_inhabited :
    ∃ C : BraidedFusionCategory.{0,1}, HasPseudoUnitaryGaloisConjugate C ∧ HasPropertyF C.Obj :=
  ⟨complexVectorSpaces, hasPseudoUnitaryGaloisConjugate, propertyF⟩

end PropertyF.Ground.Example
