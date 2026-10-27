module
public import PropertyF.Ground.CentreCalculus.ExteriorReduction
public import PropertyF.Ground.Centre.AlternatingImage
public import PropertyF.Definitions

/-! Reducing symmetric integrality to a concrete alternating-projector trace. -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
open scoped BigOperators
namespace PropertyF.Ground.CentreCalculus
universe v u

/-- The symmetric-group order is invertible over the complex numbers. -/
@[instance_reducible] def permutationCardInvertible (n : ℕ) :
    Invertible (Fintype.card (Equiv.Perm (Fin n)) : ℂ) :=
  invertibleOfNonzero (by exact_mod_cast Fintype.card_ne_zero)

/-- A trace formula for actual alternating projectors implies integrality. The
existence of the permutation action and the trace formula remain explicit. -/
theorem integral_of_alternating_projector_trace (C : BraidedFusionCategory.{v,u})
    (p : Dimensions.PivotalStructure (C := C.Obj))
    (hdim : ∀ i, Modular.simpleDimension C p i = (fpSimple C i : ℂ))
    (X : C.Obj)
    (hTrace : ∀ n : ℕ, ∃ ρ : Equiv.Perm (Fin n) →* End (tensorPower X n),
      letI := permutationCardInvertible n
      (Nat.factorial n : ℂ) * unitScalar C
        (p.rightTrace ((Centre.alternatingProjector (k := ℂ) n ρ).asHom)) =
          ∏ k ∈ Finset.range n, ((fpDimension C X : ℂ) - (k : ℂ))) :
    ∃ m : ℕ, fpDimension C X = m := by
  apply integral_of_pivotal_exterior_dimensions C p hdim X
  intro n
  obtain ⟨ρ, hρ⟩ := hTrace n
  letI := permutationCardInvertible n
  obtain ⟨Y, hY⟩ := Centre.alternatingProjector_trace (tensorPower X n) n ρ p
  refine ⟨Y, ?_⟩
  unfold Dimensions.pivotalDimension
  rw [← hY]
  exact hρ

/-- Multiplying the alternating-projector trace by the group order gives
the signed sum of the actual categorical permutation traces. -/
theorem alternatingProjector_scalar_trace (C : BraidedFusionCategory.{v,u})
    (p : Dimensions.PivotalStructure (C := C.Obj)) (X : C.Obj) (n : ℕ)
    (ρ : Equiv.Perm (Fin n) →* End X) :
    letI := permutationCardInvertible n
    (Nat.factorial n : ℂ) * unitScalar C
      (p.rightTrace ((Centre.alternatingProjector (k := ℂ) n ρ).asHom)) =
      ∑ σ : Equiv.Perm (Fin n), (Centre.permutationSign ℂ n σ : ℂ) *
        unitScalar C (p.rightTrace (ρ σ).asHom) := by
  letI := permutationCardInvertible n
  -- Both statements concern the same projector; its trace is the signed average.
  have ht : p.rightTrace ((Centre.alternatingProjector (k := ℂ) n ρ).asHom) =
      ⅟(Fintype.card (Equiv.Perm (Fin n)) : ℂ) •
        ∑ σ : Equiv.Perm (Fin n),
          (Centre.permutationSign ℂ n σ : ℂ) • p.rightTrace (ρ σ).asHom := by
    rw [Centre.alternatingProjector_eq_sum]
    simp only [End.smul_asHom, End.sum_asHom, p.rightTrace_smul]
    congr 1
    have h := map_sum (Dimensions.rightTraceLinear p X)
      (fun σ : Equiv.Perm (Fin n) => (Centre.permutationSign ℂ n σ : ℂ) • (ρ σ).asHom) Finset.univ
    change p.rightTrace (∑ σ : Equiv.Perm (Fin n),
      (Centre.permutationSign ℂ n σ : ℂ) • (ρ σ).asHom) =
      ∑ σ : Equiv.Perm (Fin n), p.rightTrace
        ((Centre.permutationSign ℂ n σ : ℂ) • (ρ σ).asHom) at h
    simpa only [p.rightTrace_smul] using h
  rw [ht, unitScalar_eq_equiv]
  simp only [map_smul, map_sum, smul_eq_mul]
  have hc : (Fintype.card (Equiv.Perm (Fin n)) : ℂ) = (Nat.factorial n : ℂ) := by
    simp [Fintype.card_perm]
  rw [← hc, ← mul_assoc, mul_invOf_self, one_mul]
  simp only [unitScalar_eq_equiv]

/-- It suffices to evaluate the unnormalized signed trace sum for each
permutation action. The existence and evaluation of these actions are still
explicit hypotheses. -/
theorem integral_of_signed_permutation_traces (C : BraidedFusionCategory.{v,u})
    (p : Dimensions.PivotalStructure (C := C.Obj))
    (hdim : ∀ i, Modular.simpleDimension C p i = (fpSimple C i : ℂ))
    (X : C.Obj)
    (hTrace : ∀ n : ℕ, ∃ ρ : Equiv.Perm (Fin n) →* End (tensorPower X n),
      (∑ σ : Equiv.Perm (Fin n), (Centre.permutationSign ℂ n σ : ℂ) *
        unitScalar C (p.rightTrace (ρ σ).asHom)) =
          ∏ k ∈ Finset.range n, ((fpDimension C X : ℂ) - (k : ℂ))) :
    ∃ m : ℕ, fpDimension C X = m := by
  apply integral_of_alternating_projector_trace C p hdim X
  intro n
  obtain ⟨ρ, hρ⟩ := hTrace n
  refine ⟨ρ, ?_⟩
  rw [alternatingProjector_scalar_trace]
  exact hρ

end PropertyF.Ground.CentreCalculus
