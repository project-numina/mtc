module
public import PropertyF.Ground.Calculus.ThreeEmbedding
public import PropertyF.Ground.Calculus.BraidTraceBound
public import PropertyF.Ground.Calculus.PartialTraceGround

/-! Actual overlapping braid products, using the constructed strand maps. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.Calculus
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]

/-- The repository's strand index for `k+1` overlapping copies of an operator
on `t+2` strands. -/
def overlapIndex (t : ℕ) : ℕ → ℕ
  | 0 => t
  | k + 1 => overlapIndex t k + (t + 1)

theorem overlapIndex_formula (t k : ℕ) : overlapIndex t k = t + k * (t + 1) := by
  induction k with
  | zero => simp [overlapIndex]
  | succ k ih => simp [overlapIndex, ih, Nat.succ_mul, Nat.add_assoc]

/-- Extend the existing product by `t+1` identity strands on the right. -/
def overlapLeft (X : C) (t k : ℕ) :
    braidAlgebra X (overlapIndex t k) →ₐ[ℂ] braidAlgebra X (overlapIndex t (k + 1)) := by
  exact addRightBraidAlgebraIter X (overlapIndex t k) (t + 1)

/-- Place a fresh copy at the right, overlapping the old product in one strand. -/
def overlapRight (X : C) (t k : ℕ) :
    braidAlgebra X t →ₐ[ℂ] braidAlgebra X (overlapIndex t (k + 1)) := by
  rw [overlapIndex_formula]
  exact addLeftBraidAlgebraIter X t ((k + 1) * (t + 1))

/-- The actual product of `k+1` successive overlapping braid-algebra elements. -/
def overlapProduct (X : C) (t : ℕ) (u : braidAlgebra X t) :
    ∀ k : ℕ, braidAlgebra X (overlapIndex t k)
  | 0 => u
  | k + 1 => overlapLeft X t k (overlapProduct X t u k) * overlapRight X t k u

end PropertyF.Ground.Calculus
