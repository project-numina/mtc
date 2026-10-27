module
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Data.Fintype.CardEmbedding
public import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
public import Mathlib.GroupTheory.Perm.Cycle.Basic
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Data.Nat.Factorial.BigOperators
public import Mathlib.Basic.Complex.Basic
public import PropertyF.Ground.CentreCalculus.ParityCorrection

/-!
# Cycle traces and integrality

Fixed-colouring counts identify the signed cycle polynomial with a falling
factorial. Ordinary or signed permutation-trace formulas then imply integrality
of the Frobenius–Perron dimension through the projector criteria.

## Main results

* `signed_cycle_count` gives the falling-factorial identity.
* `integral_of_cycle_traces` and `integral_of_signed_cycle_traces` apply it to
  the corresponding categorical trace formulas.
-/

open scoped BigOperators
open Equiv
@[expose] public noncomputable section
namespace PropertyF.Ground.CentreIntegrate

/-- A sign sum over permutations fixing a colouring is one precisely when
the colouring is injective. -/
theorem signed_sum_fixed_coloring (α β : Type*) [Fintype α] [DecidableEq α] [DecidableEq β] (f : α → β) :
    (∑ σ : Perm α, if ∀ i, f (σ i) = f i then (Perm.sign σ : ℤ) else 0) =
      if Function.Injective f then 1 else 0 := by
  classical
  let M : Matrix α α ℤ := fun i j => if f i = f j then 1 else 0
  have hd : M.det = if Function.Injective f then 1 else 0 := by
    by_cases hf : Function.Injective f
    · have hm : M = 1 := by
        ext i j
        simp [M, hf.eq_iff, Matrix.one_apply]
      simp [hm, hf]
    · obtain ⟨i, j, hij, hne⟩ := Function.not_injective_iff.mp hf
      have hm : M.det = 0 := by
        apply Matrix.det_zero_of_row_eq hne
        funext k
        simp [M, hij]
      simp [hm, hf]
  rw [← hd, Matrix.det_apply]
  apply Finset.sum_congr rfl
  intro σ _
  simp only [M, Fintype.prod_ite_zero, Finset.prod_const_one]
  split_ifs <;> change _ = (Perm.sign σ : ℤ) * _ <;> simp

/-- Summing fixed-colouring signs gives the number of injective colourings. -/
theorem signed_fixed_coloring_sum (n m : ℕ) :
    (∑ σ : Perm (Fin n), ∑ f : Fin n → Fin m,
      if ∀ i, f (σ i) = f i then (Perm.sign σ : ℤ) else 0) =
      (Nat.descFactorial m n : ℤ) := by
  classical
  rw [Finset.sum_comm]
  calc
    _ = ∑ f : Fin n → Fin m, if Function.Injective f then 1 else (0 : ℤ) := by
      apply Finset.sum_congr rfl
      intro f _
      convert signed_sum_fixed_coloring (Fin n) (Fin m) f using 1
      apply Finset.sum_congr rfl
      intro σ _
      split_ifs <;> rfl
    _ = _ := by
      rw [Finset.sum_boole]
      have hcard : (Finset.univ.filter (fun x : Fin n → Fin m => Function.Injective x)).card =
          Fintype.card (Fin n ↪ Fin m) := by
        rw [← Fintype.card_subtype]
        exact Fintype.card_congr (Equiv.subtypeInjectiveEquivEmbedding _ _)
      rw [hcard, Fintype.card_embedding_eq]
      simp

end PropertyF.Ground.CentreIntegrate

end

open scoped BigOperators
open Equiv
@[expose] public noncomputable section
namespace PropertyF.Ground.CentreIntegrate
set_option linter.style.haveILetI false

/-- Colourings fixed by a permutation are precisely functions on its cycle quotient. -/
def fixedColoringEquivCycleQuotient {α β : Type*} [Fintype α] (σ : Perm α) :
    {f : α → β // ∀ i, f (σ i) = f i} ≃ (Quotient (Perm.SameCycle.setoid σ) → β) where
  toFun f := Quotient.lift f.1 (by
    intro x y hxy
    obtain ⟨k, _, hk⟩ := Perm.SameCycle.exists_pow_eq' hxy
    have hpow (k : ℕ) (x : α) : f.1 ((σ ^ k) x) = f.1 x := by
      induction k with
      | zero => rfl
      | succ k ih => rw [pow_succ', Perm.mul_apply, f.2, ih]
    rw [← hk, hpow])
  invFun f := ⟨fun x => f (Quotient.mk (Perm.SameCycle.setoid σ) x), by
    intro i
    apply congrArg f
    apply Quotient.sound
    exact (Perm.sameCycle_apply_left).2 (Perm.SameCycle.refl σ i)⟩
  left_inv f := by cases f; rfl
  right_inv f := by
    funext q
    induction q using Quotient.inductionOn with
    | _ x => rfl

/-- Fixed points count as cycles, via the same-cycle quotient. -/
def countCycles {α : Type*} [Fintype α] (σ : Perm α) : ℕ :=
  Nat.card (Quotient (Perm.SameCycle.setoid σ))

/-- The number of colourings fixed by a permutation is the number of colours
to the number of its cycles. -/
theorem fixed_coloring_count (n m : ℕ) (σ : Perm (Fin n)) :
    (∑ f : Fin n → Fin m, if ∀ i, f (σ i) = f i then (1 : ℤ) else 0) =
      (m : ℤ) ^ countCycles σ := by
  classical
  rw [Finset.sum_boole]
  letI : Fintype (Quotient (Perm.SameCycle.setoid σ)) := Fintype.ofFinite _
  have hcard : (Finset.univ.filter (fun f : Fin n → Fin m => ∀ i, f (σ i) = f i)).card =
      Fintype.card (Quotient (Perm.SameCycle.setoid σ) → Fin m) := by
    rw [← Fintype.card_subtype]
    exact Fintype.card_congr (fixedColoringEquivCycleQuotient σ)
  rw [hcard, Fintype.card_fun]
  simp [countCycles, Nat.card_eq_fintype_card]

/-- At every natural number of colours, the signed cycle-count sum is the
number of injective colourings. -/
theorem signed_cycle_count_nat (n m : ℕ) :
    (∑ σ : Perm (Fin n), (Perm.sign σ : ℤ) * (m : ℤ) ^ countCycles σ) =
      (Nat.descFactorial m n : ℤ) := by
  classical
  rw [← PropertyF.Ground.CentreIntegrate.signed_fixed_coloring_sum n m]
  apply Finset.sum_congr rfl
  intro σ _
  rw [← fixed_coloring_count n m σ, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro f _
  split_ifs <;> simp

end PropertyF.Ground.CentreIntegrate

end

open scoped BigOperators
open Equiv Polynomial
@[expose] public noncomputable section
namespace PropertyF.Ground.CentreIntegrate

/-- The signed cycle-count polynomial. -/
def cyclePoly (n : ℕ) : Polynomial ℂ :=
  ∑ σ : Perm (Fin n), Polynomial.C ((Perm.sign σ : ℤ) : ℂ) * Polynomial.X ^ countCycles σ

/-- The polynomial with roots 0 through n-1. -/
def fallingPoly (n : ℕ) : Polynomial ℂ :=
  ∏ k ∈ Finset.range n, (Polynomial.X - Polynomial.C (k : ℂ))

/-- The signed cycle-count polynomial is the falling factorial polynomial. -/
theorem cyclePoly_eq_fallingPoly (n : ℕ) : cyclePoly n = fallingPoly n := by
  classical
  apply Polynomial.eq_of_infinite_eval_eq
  apply Set.Infinite.mono (s := Set.range (fun k : ℕ => ((n + k : ℕ) : ℂ)))
  · rintro _ ⟨k, rfl⟩
    change Polynomial.eval ((n + k : ℕ) : ℂ) (cyclePoly n) = _
    simp only [cyclePoly, fallingPoly, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
      Polynomial.eval_X, Polynomial.eval_prod, Polynomial.eval_sub]
    have hnat := signed_cycle_count_nat n (n + k)
    have hcast : (∑ σ : Perm (Fin n), ((Perm.sign σ : ℤ) : ℂ) *
        (((n + k : ℕ) : ℂ) ^ countCycles σ)) = ((Nat.descFactorial (n + k) n : ℕ) : ℂ) := by
      exact_mod_cast hnat
    rw [hcast, Nat.descFactorial_eq_prod_range, Nat.cast_prod]
    apply Finset.prod_congr rfl
    intro i hi
    rw [Nat.cast_sub]
    exact Nat.le_trans (Nat.le_of_lt (Finset.mem_range.mp hi)) (Nat.le_add_right n k)
  · apply Set.infinite_range_of_injective
    intro i j h
    have hn : n + i = n + j := Nat.cast_injective h
    exact Nat.add_left_cancel hn

/-- Signed cycle-count identity over ℂ, including fixed points as cycles. -/
theorem signed_cycle_count (n : ℕ) (x : ℂ) :
    (∑ σ : Perm (Fin n), ((Perm.sign σ : ℤ) : ℂ) * x ^ countCycles σ) =
      ∏ k ∈ Finset.range n, (x - (k : ℂ)) := by
  have h := congrArg (Polynomial.eval x) (cyclePoly_eq_fallingPoly n)
  simpa only [cyclePoly, fallingPoly, Polynomial.eval_finsetSum, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_prod,
    Polynomial.eval_sub] using h

end PropertyF.Ground.CentreIntegrate

end


/-! Cycle trace formulas suffice for the existing exterior-projector argument. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
open scoped BigOperators
namespace PropertyF.Ground.CentreIntegrate
universe v u

/-- If the permutation traces have the ordinary cycle formula, positivity of
alternating-projector dimensions forces the FP dimension to be an integer.
The permutation actions and the trace formula remain explicit premises. -/
theorem integral_of_cycle_traces (C : BraidedFusionCategory.{v,u})
    (p : Dimensions.PivotalStructure (C := C.Obj))
    (hdim : ∀ i, Modular.simpleDimension C p i = (fpSimple C i : ℂ))
    (X : C.Obj)
    (hTrace : ∀ n : ℕ, ∃ ρ : Equiv.Perm (Fin n) →* End (tensorPower X n),
      ∀ σ, unitScalar C (p.rightTrace (ρ σ).asHom) =
        (fpDimension C X : ℂ) ^ countCycles σ) :
    ∃ m : ℕ, fpDimension C X = m := by
  apply CentreCalculus.integral_of_signed_permutation_traces C p hdim X
  intro n
  obtain ⟨ρ, hρ⟩ := hTrace n
  refine ⟨ρ, ?_⟩
  simp_rw [hρ]
  change (∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : ℂ) *
    (fpDimension C X : ℂ) ^ countCycles σ) = _
  exact signed_cycle_count n (fpDimension C X : ℂ)

/-- In the opposite parity case the permutation trace acquires the sign;
the ordinary projector then gives the same integrality conclusion. -/
theorem integral_of_signed_cycle_traces (C : BraidedFusionCategory.{v,u})
    (p : Dimensions.PivotalStructure (C := C.Obj))
    (hdim : ∀ i, Modular.simpleDimension C p i = (fpSimple C i : ℂ))
    (X : C.Obj)
    (hTrace : ∀ n : ℕ, ∃ ρ : Equiv.Perm (Fin n) →* End (tensorPower X n),
      ∀ σ, unitScalar C (p.rightTrace (ρ σ).asHom) =
        ((Equiv.Perm.sign σ : ℤ) : ℂ) * (fpDimension C X : ℂ) ^ countCycles σ) :
    ∃ m : ℕ, fpDimension C X = m := by
  apply CentreCalculus.integral_of_unsigned_permutation_traces C p hdim X
  intro n
  obtain ⟨ρ, hρ⟩ := hTrace n
  refine ⟨ρ, ?_⟩
  simp_rw [hρ]
  exact signed_cycle_count n (fpDimension C X : ℂ)

end PropertyF.Ground.CentreIntegrate

end
