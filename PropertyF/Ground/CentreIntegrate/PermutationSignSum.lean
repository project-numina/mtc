module
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Data.Fintype.CardEmbedding
public import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
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
