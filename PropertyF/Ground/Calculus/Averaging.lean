module
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Tactic

/-! A finite group representation preserves a positive definite Hermitian form.
The unnormalized average avoids dividing by the group order. -/

@[expose] public noncomputable section
open Matrix
open scoped BigOperators ComplexOrder
namespace PropertyF.Ground.Calculus

variable {G ι : Type*} [Group G] [Fintype G] [Fintype ι] [DecidableEq ι]

/-- The Gram matrix of the sum of all pullbacks of the standard form. -/
def averagedGram (ρ : G →* (Matrix ι ι ℂ)ˣ) : Matrix ι ι ℂ :=
  ∑ g : G, (↑(ρ g) : Matrix ι ι ℂ)ᴴ * (↑(ρ g) : Matrix ι ι ℂ)

/-- The averaged form is positive definite, even in dimension zero. -/
theorem averagedGram_posDef (ρ : G →* (Matrix ι ι ℂ)ˣ) :
    (averagedGram ρ).PosDef := by
  classical
  unfold averagedGram
  apply Matrix.posDef_sum Finset.univ_nonempty
  intro g _
  exact Matrix.PosDef.conjTranspose_mul_self _
    (Matrix.mulVec_injective_of_isUnit (Units.isUnit (ρ g)))

/-- Every group element is an isometry for the averaged form. -/
theorem averagedGram_invariant (ρ : G →* (Matrix ι ι ℂ)ˣ) (h : G) :
    (↑(ρ h) : Matrix ι ι ℂ)ᴴ * averagedGram ρ * (↑(ρ h) : Matrix ι ι ℂ) = averagedGram ρ := by
  classical
  simp only [averagedGram, Matrix.mul_sum, Matrix.sum_mul]
  calc
    _ = ∑ g : G, (↑(ρ (g * h)) : Matrix ι ι ℂ)ᴴ * (↑(ρ (g * h)) : Matrix ι ι ℂ) := by
      apply Finset.sum_congr rfl
      intro g _
      simp only [map_mul, Units.val_mul, Matrix.conjTranspose_mul]
      simp only [Matrix.mul_assoc]
    _ = ∑ g : G, (↑(ρ g) : Matrix ι ι ℂ)ᴴ * (↑(ρ g) : Matrix ι ι ℂ) := by
      exact Equiv.sum_comp (Equiv.mulRight h)
        (fun g => (↑(ρ g) : Matrix ι ι ℂ)ᴴ * (↑(ρ g) : Matrix ι ι ℂ))

end PropertyF.Ground.Calculus
