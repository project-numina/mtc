module
public import PropertyF.Ground.CentreIntegrate.CyclePolynomial
public import PropertyF.Ground.CentreCalculus.ParityCorrection

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
