module
public import PropertyF.Ground.CentreIntegrate.PermutationSignSum
public import Mathlib.GroupTheory.Perm.Cycle.Basic
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
