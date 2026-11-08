module
public import MTC.Braided.Cabling.ClosureColoredCrossing

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace MTC.Braided
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- Right-associated tuple of tensor powers. -/
def heterogeneousPowerTensor (X : C) : ∀ n : ℕ, (Fin n → ℕ) → C
  | 0, _ => 𝟙_ C
  | n+1, k => tensorPower X (k 0) ⊗ heterogeneousPowerTensor X n (fun i => k i.succ)

/-- Strand count for the same tuple, using left-recursive addition. -/
def heterogeneousStrandCount : ∀ n : ℕ, (Fin n → ℕ) → ℕ
  | 0, _ => 0
  | n+1, k => strandSum (k 0) (heterogeneousStrandCount n (fun i => k i.succ))

/-- The tuple flattens canonically into its original strands. -/
def heterogeneousPowerFlatten (X : C) : ∀ (n : ℕ) (k : Fin n → ℕ),
    heterogeneousPowerTensor X n k ≅ tensorPower X (heterogeneousStrandCount n k)
  | 0, _ => Iso.refl _
  | n+1, k => (Iso.refl (tensorPower X (k 0)) ⊗ᵢ
      heterogeneousPowerFlatten X n (fun i => k i.succ)) ≪≫
        joinPowerIso X (k 0) (heterogeneousStrandCount n (fun i => k i.succ))

/-- Recursive strand counts agree with the ordinary finite sum. -/
theorem heterogeneousStrandCount_eq_sum : ∀ (n : ℕ) (k : Fin n → ℕ),
    heterogeneousStrandCount n k = ∑ i, k i
  | 0, _ => by simp [heterogeneousStrandCount]
  | n+1, k => by
    simp [heterogeneousStrandCount, heterogeneousStrandCount_eq_sum,
      strandSum_eq_add, Fin.sum_univ_succ]

/-- The canonical tuple flattening, with its conventional total-strand index. -/
def heterogeneousPowerFlattenSum (X : C) (n : ℕ) (k : Fin n → ℕ) :
    heterogeneousPowerTensor X n k ≅ tensorPower X (∑ i, k i) :=
  heterogeneousPowerFlatten X n k ≪≫ powerIndexIso X (heterogeneousStrandCount_eq_sum n k)
