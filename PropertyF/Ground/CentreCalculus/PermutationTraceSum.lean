module
public import PropertyF.Ground.CentreCalculus.TensorPermutation
public import Mathlib.GroupTheory.Perm.Fin

/-! Summing permutation traces from a one-strand deletion identity. -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
open scoped BigOperators
namespace PropertyF.Ground.CentreCalculus

/-- Signed permutation trace sum, with no categorical assumptions. -/
def signedTraceSum (F : ∀ n : ℕ, Equiv.Perm (Fin n) → ℂ) (n : ℕ) : ℂ :=
  ∑ σ, (Centre.permutationSign ℂ n σ : ℂ) * F n σ

/-- The sign changes precisely when the newly inserted point is moved. -/
theorem sign_decomposeFin (n : ℕ) (p : Fin (n + 1)) (σ : Equiv.Perm (Fin n)) :
    (Centre.permutationSign ℂ (n + 1) (Equiv.Perm.decomposeFin.symm (p, σ)) : ℂ) =
      (if p = 0 then 1 else -1) * (Centre.permutationSign ℂ n σ : ℂ) := by
  by_cases hp : p = 0 <;>
    simp [Centre.permutationSign, Equiv.Perm.decomposeFin.symm_sign, hp]

/-- A deletion identity for the trace gives the signed-sum recurrence. -/
theorem signedTraceSum_succ (F : ∀ n : ℕ, Equiv.Perm (Fin n) → ℂ)
    (d c : ℂ) (n : ℕ)
    (hfixed : ∀ σ, F (n + 1) (Equiv.Perm.decomposeFin.symm (0, σ)) = d * F n σ)
    (hmoved : ∀ (p : Fin (n + 1)), p ≠ 0 → ∀ σ,
      F (n + 1) (Equiv.Perm.decomposeFin.symm (p, σ)) = c * F n σ) :
    signedTraceSum F (n + 1) = (d - (n : ℂ) * c) * signedTraceSum F n := by
  unfold signedTraceSum
  rw [← Equiv.Perm.decomposeFin.symm.sum_comp,
    Fintype.sum_prod_type, Fin.sum_univ_succ]
  simp only [sign_decomposeFin, if_true, one_mul, hfixed, Fin.succ_ne_zero,
    if_false, hmoved _ (Fin.succ_ne_zero _), neg_mul]
  simp only [Finset.sum_neg_distrib]
  simp only [show ∀ (a b c : ℂ), a * (b * c) = b * (a * c) by intros; ring, ← Finset.mul_sum]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

/-- The deletion identities imply the falling-factorial signed trace sum.
This isolates the categorical trace calculation from the permutation sum. -/
theorem signedTraceSum_falling (F : ∀ n : ℕ, Equiv.Perm (Fin n) → ℂ) (d : ℂ)
    (hzero : F 0 1 = 1)
    (hfixed : ∀ n σ, F (n + 1) (Equiv.Perm.decomposeFin.symm (0, σ)) = d * F n σ)
    (hmoved : ∀ n (p : Fin (n + 1)), p ≠ 0 → ∀ σ,
      F (n + 1) (Equiv.Perm.decomposeFin.symm (p, σ)) = F n σ) :
    ∀ n, signedTraceSum F n = ∏ k ∈ Finset.range n, (d - (k : ℂ)) := by
  intro n
  induction n with
  | zero =>
    letI : Unique (Equiv.Perm (Fin 0)) := ⟨⟨1⟩, fun _ => Subsingleton.elim _ _⟩
    simp [signedTraceSum, hzero, Centre.permutationSign]
  | succ n ih =>
    rw [signedTraceSum_succ F d 1 n (hfixed n) (by simpa using hmoved n), ih,
      Finset.prod_range_succ]
    ring

universe v u
/-- Integrality follows from one-strand trace deletion for any compatible
(possibly sign-twisted) family of actual actions. -/
theorem integral_of_trace_deletion (C : BraidedFusionCategory.{v,u})
    (p : Dimensions.PivotalStructure (C := C.Obj))
    (hdim : ∀ i, Modular.simpleDimension C p i = (fpSimple C i : ℂ)) (X : C.Obj)
    (ρ : ∀ n : ℕ, Equiv.Perm (Fin n) →* End (tensorPower X n))
    (hfixed : ∀ n σ,
      unitScalar C (p.rightTrace ((ρ (n + 1)) (Equiv.Perm.decomposeFin.symm (0, σ))).asHom) =
        (fpDimension C X : ℂ) * unitScalar C (p.rightTrace ((ρ n) σ).asHom))
    (hmoved : ∀ n (q : Fin (n + 1)), q ≠ 0 → ∀ σ,
      unitScalar C (p.rightTrace ((ρ (n + 1)) (Equiv.Perm.decomposeFin.symm (q, σ))).asHom) =
        unitScalar C (p.rightTrace ((ρ n) σ).asHom)) :
    ∃ m : ℕ, fpDimension C X = m := by
  let F : ∀ n : ℕ, Equiv.Perm (Fin n) → ℂ := fun n σ =>
    unitScalar C (p.rightTrace ((ρ n) σ).asHom)
  have hz : F 0 1 = 1 := by
    change unitScalar C (p.rightTrace (((ρ 0) 1).asHom)) = 1
    rw [map_one]
    change unitScalar C (p.rightTrace (𝟙 (𝟙_ C.Obj))) = 1
    rw [Dimensions.rightTrace_unit, unitScalar_eq_equiv, map_one]
  have hf := signedTraceSum_falling F (fpDimension C X : ℂ) hz hfixed hmoved
  apply integral_of_signed_permutation_traces C p hdim X
  intro n
  exact ⟨ρ n, hf n⟩

end PropertyF.Ground.CentreCalculus
