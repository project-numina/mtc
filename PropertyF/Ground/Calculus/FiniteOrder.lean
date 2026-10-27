module
public import PropertyF.Definitions
public import Mathlib.GroupTheory.OrderOfElement

/-! Finiteness of categorical braid images supplies the finite-order condition
for the squared braiding and for every representation of the braid image. -/

@[expose] public section
open CategoryTheory
namespace PropertyF.Ground.Calculus
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]

/-- An adjacent generator as an element of the actual categorical braid image. -/
def imageGenerator (X : C) (n : ℕ) (i : Fin (n + 1)) : braidImage X n :=
  ⟨braidGenerator X n i, Subgroup.subset_closure (Set.mem_range_self _)⟩

/-- Every represented braid image element has finite order when the categorical
image is finite. No faithfulness of the representation is required. -/
theorem represented_braid_finite_order {H : Type*} [Monoid H]
    (X : C) (n : ℕ) (h : Finite (braidImage X n))
    (ρ : braidImage X n →* H) (g : braidImage X n) :
    ∃ k : ℕ, k ≠ 0 ∧ (ρ g) ^ k = 1 := by
  let _ : Finite (braidImage X n) := h
  obtain ⟨k, hk, hpow⟩ := (ρ.isOfFinOrder (isOfFinOrder_of_finite g)).exists_pow_eq_one
  exact ⟨k, hk.ne', hpow⟩

/-- In particular, the represented square of the two-strand self-braiding
satisfies the `finite_order` condition needed for three-strand rigidity. -/
theorem represented_square_finite_order {H : Type*} [Monoid H]
    (X : C) (h : ObjectPropertyF X) (ρ : braidImage X 0 →* H) :
    ∃ k : ℕ, k ≠ 0 ∧ (ρ ((imageGenerator X 0 0) ^ 2)) ^ k = 1 :=
  represented_braid_finite_order X 0 (h 0) ρ _

/-- The categorical square itself has finite order. -/
theorem braid_square_finite_order (X : C) (h : ObjectPropertyF X) :
    ∃ k : ℕ, k ≠ 0 ∧ (braidGenerator X 0 0 ^ 2) ^ k = 1 := by
  obtain ⟨k, hk, hpow⟩ := represented_square_finite_order X h (braidImage X 0).subtype
  exact ⟨k, hk, hpow⟩

end PropertyF.Ground.Calculus
