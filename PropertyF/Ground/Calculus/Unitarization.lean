module
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Tactic
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.LinearAlgebra.UnitaryGroup

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

/-! A finite complex matrix representation can be conjugated into the unitary group. -/

@[expose] public noncomputable section
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder
namespace PropertyF.Ground.Calculus

variable {G ι : Type*} [Group G] [Fintype G] [Fintype ι] [DecidableEq ι]

/-- A single change of basis unitarizes every matrix in a finite group representation. -/
theorem exists_unitarizing_basis (ρ : G →* (Matrix ι ι ℂ)ˣ) :
    ∃ P : (Matrix ι ι ℂ)ˣ, ∀ g : G,
      ((↑(P * ρ g * P⁻¹) : Matrix ι ι ℂ) ∈ Matrix.unitaryGroup ι ℂ) := by
  classical
  let A := averagedGram ρ
  have hA : 0 ≤ A := (averagedGram_posDef ρ).posSemidef.nonneg
  have hS : IsUnit (CFC.sqrt A) := (CFC.isUnit_sqrt_iff A hA).2
    (averagedGram_posDef ρ).isUnit
  let P : (Matrix ι ι ℂ)ˣ := hS.unit
  have hP : (↑P : Matrix ι ι ℂ) = CFC.sqrt A := hS.unit_spec
  have hself : star (↑P : Matrix ι ι ℂ) = ↑P := by
    rw [hP]
    exact (CFC.sqrt_nonneg A).star_eq
  have hsquare : (↑P : Matrix ι ι ℂ) * (↑P : Matrix ι ι ℂ) = A := by
    rw [hP, ← pow_two, CFC.sq_sqrt A hA]
  refine ⟨P, fun g => ?_⟩
  apply Matrix.mem_unitaryGroup_iff'.2
  have hinv : (↑(ρ g) : Matrix ι ι ℂ)ᴴ * A * (↑(ρ g) : Matrix ι ι ℂ) = A :=
    averagedGram_invariant ρ g
  change star ((↑P : Matrix ι ι ℂ) * (↑(ρ g) : Matrix ι ι ℂ) * (↑(P⁻¹) : Matrix ι ι ℂ)) *
    ((↑P : Matrix ι ι ℂ) * (↑(ρ g) : Matrix ι ι ℂ) * (↑(P⁻¹) : Matrix ι ι ℂ)) = 1
  simp only [star_mul, hself, ← Matrix.star_eq_conjTranspose] at hinv ⊢
  have hselfu : star P = P := Units.ext hself
  have hselfinv : star (↑(P⁻¹) : Matrix ι ι ℂ) = ↑(P⁻¹) := by
    have h : star (P⁻¹) = P⁻¹ := by simp [hselfu]
    exact congrArg (fun Q : (Matrix ι ι ℂ)ˣ => (↑Q : Matrix ι ι ℂ)) h
  rw [hselfinv]
  calc
    _ = (↑(P⁻¹) : Matrix ι ι ℂ) * (star (↑(ρ g) : Matrix ι ι ℂ) * A * ↑(ρ g)) * ↑(P⁻¹) := by
      rw [← hsquare]
      noncomm_ring
    _ = (↑(P⁻¹) : Matrix ι ι ℂ) * (↑P * ↑P) * ↑(P⁻¹) := by rw [hinv, hsquare]
    _ = 1 := by
      change (↑(P⁻¹ * (P * P) * P⁻¹) : Matrix ι ι ℂ) = ↑(1 : (Matrix ι ι ℂ)ˣ)
      congr 1
      simp

end PropertyF.Ground.Calculus
