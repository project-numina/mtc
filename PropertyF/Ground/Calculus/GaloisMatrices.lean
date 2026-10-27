module
public import PropertyF.Ground.Calculus.UnitaryBlocks
public import Mathlib.LinearAlgebra.Matrix.Trace

/-! Entrywise scalar transport and unitarization of finite group representations. -/

@[expose] public noncomputable section
open Matrix
namespace PropertyF.Ground.Calculus

variable {G ι : Type*} [Group G] [Fintype G] [Fintype ι] [DecidableEq ι]

/-- Apply an arbitrary complex field automorphism to every matrix coefficient
of a group representation. -/
def galoisMatrixRepresentation (σ : ℂ ≃+* ℂ) (ρ : G →* (Matrix ι ι ℂ)ˣ) :
    G →* (Matrix ι ι ℂ)ˣ :=
  (Units.map σ.mapMatrix.toMonoidHom).comp ρ

/-- A scalar-twisted, basis-changed matrix algebra equivalence. -/
def galoisMatrixEquiv (σ : ℂ ≃+* ℂ) (P : (Matrix ι ι ℂ)ˣ) :
    Matrix ι ι ℂ ≃+* Matrix ι ι ℂ :=
  σ.mapMatrix.trans (unitConjugation P).toRingEquiv

/-- The matrix equivalence is semilinear with respect to the given scalar
automorphism. -/
theorem galoisMatrixEquiv_smul (σ : ℂ ≃+* ℂ) (P : (Matrix ι ι ℂ)ˣ)
    (z : ℂ) (A : Matrix ι ι ℂ) :
    galoisMatrixEquiv σ P (z • A) = σ z • galoisMatrixEquiv σ P A := by
  have hmap : σ.mapMatrix (z • A) = σ z • σ.mapMatrix A := by
    ext i j
    simp [RingEquiv.mapMatrix_apply, Matrix.smul_apply, map_mul]
  change unitConjugation P (σ.mapMatrix (z • A)) =
    σ z • unitConjugation P (σ.mapMatrix A)
  rw [hmap, map_smul]

/-- Its ordinary matrix trace is exactly the transported trace. -/
theorem galoisMatrixEquiv_trace (σ : ℂ ≃+* ℂ) (P : (Matrix ι ι ℂ)ˣ)
    (A : Matrix ι ι ℂ) : (galoisMatrixEquiv σ P A).trace = σ A.trace := by
  change ((↑P : Matrix ι ι ℂ) * σ.mapMatrix A * (↑(P⁻¹) : Matrix ι ι ℂ)).trace = _
  rw [Matrix.trace_units_conj]
  simpa only [RingEquiv.mapMatrix_apply] using (AddMonoidHom.map_trace σ A).symm

/-- Finite group representations remain simultaneously unitarizable after an
arbitrary scalar automorphism, and their characters are Galois-transformed. -/
theorem exists_galois_unitarization (σ : ℂ ≃+* ℂ) (ρ : G →* (Matrix ι ι ℂ)ˣ) :
    ∃ P : (Matrix ι ι ℂ)ˣ, ∀ g : G,
      ((↑(P * galoisMatrixRepresentation σ ρ g * P⁻¹) : Matrix ι ι ℂ) ∈
        Matrix.unitaryGroup ι ℂ) ∧
      (↑(P * galoisMatrixRepresentation σ ρ g * P⁻¹) : Matrix ι ι ℂ).trace =
        σ (↑(ρ g) : Matrix ι ι ℂ).trace := by
  obtain ⟨P, hP⟩ := exists_unitarizing_basis (galoisMatrixRepresentation σ ρ)
  refine ⟨P, fun g => ⟨hP g, ?_⟩⟩
  change ((↑P : Matrix ι ι ℂ) * σ.mapMatrix (↑(ρ g) : Matrix ι ι ℂ) * (↑(P⁻¹) : Matrix ι ι ℂ)).trace = _
  rw [Matrix.trace_units_conj]
  simpa only [RingEquiv.mapMatrix_apply] using
    (AddMonoidHom.map_trace σ (↑(ρ g) : Matrix ι ι ℂ)).symm

/-- The whole matrix algebra can be transported semilinearly so that all
images of a finite group are unitary and all traces are Galois-transformed. -/
theorem exists_galois_unitary_matrix_equiv (σ : ℂ ≃+* ℂ)
    (ρ : G →* (Matrix ι ι ℂ)ˣ) :
    ∃ P : (Matrix ι ι ℂ)ˣ,
      (∀ g : G, galoisMatrixEquiv σ P (↑(ρ g) : Matrix ι ι ℂ) ∈
        Matrix.unitaryGroup ι ℂ) ∧
      (∀ A : Matrix ι ι ℂ, (galoisMatrixEquiv σ P A).trace = σ A.trace) ∧
      (∀ (z : ℂ) A, galoisMatrixEquiv σ P (z • A) = σ z • galoisMatrixEquiv σ P A) := by
  obtain ⟨P, hP⟩ := exists_galois_unitarization σ ρ
  refine ⟨P, ?_, galoisMatrixEquiv_trace σ P, galoisMatrixEquiv_smul σ P⟩
  intro g
  have h := (hP g).1
  change ((↑P : Matrix ι ι ℂ) * σ.mapMatrix (↑(ρ g) : Matrix ι ι ℂ) *
    (↑(P⁻¹) : Matrix ι ι ℂ)) ∈ Matrix.unitaryGroup ι ℂ at h
  exact h

end PropertyF.Ground.Calculus
