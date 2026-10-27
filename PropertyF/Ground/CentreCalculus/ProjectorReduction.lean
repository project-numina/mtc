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

end PropertyF.Ground.CentreCalculus
