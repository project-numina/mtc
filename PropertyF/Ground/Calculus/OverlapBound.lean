module
public import PropertyF.Ground.Calculus.OverlapUnitary
public import PropertyF.PowerBound

/-! Reduction of the sharp trace bound to the categorical overlap recurrence. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory

namespace PropertyF.Ground.Calculus
universe v u

/-- A scaled overlap recurrence and bounds at its strand counts imply the sharp norm bound. -/
theorem norm_bound_of_overlapIndex {δ z : ℂ} {f : ℝ} (hδ : δ ≠ 0) (hf : 0 < f)
    (t : ℕ) (a : ℕ → ℂ) (hbound : ∀ k, ‖a k‖ ≤ f ^ (overlapIndex t k + 2))
    (hrec : ∀ k, a k * δ ^ k = z ^ (k + 1)) : ‖z‖ ≤ ‖δ‖ * f ^ (t + 1) := by
  apply PropertyF.norm_bound_of_overlap (m := t + 2) hδ hf a ?_ hrec
  intro k
  have hexp : overlapIndex t k + 2 = (k + 1) * ((t + 2) - 1) + 1 := by
    rw [overlapIndex_formula]
    have h : (t + 2) - 1 = t + 1 := by omega
    rw [h]
    ring
  simpa only [hexp] using hbound k

/-- Pivotal trace of an element of an actual categorical braid algebra. -/
def actualBraidTrace (C : Ground.BraidedFusionCategory.{v,u}) (X : C.Obj)
    (p : Dimensions.PivotalStructure (C := C.Obj)) (n : ℕ) (a : braidAlgebra X n) : ℂ :=
  Dimensions.groundUnitScalarEquiv C
    (p.rightTrace (a : End (tensorPower X (n + 2))).asHom)

/-- Iterating a single overlap step gives the scaled power identity, without
dividing by the simple dimension. -/
theorem overlap_trace_power_of_step
    (C : Ground.BraidedFusionCategory.{v,u}) (X : C.Obj)
    (p : Dimensions.PivotalStructure (C := C.Obj)) (t : ℕ) (u : braidAlgebra X t)
    (hstep : ∀ k, actualBraidTrace C X p (overlapIndex t (k + 1))
        (overlapProduct X t u (k + 1)) *
        Dimensions.groundUnitScalarEquiv C (p.rightTrace (𝟙 X)) =
      actualBraidTrace C X p (overlapIndex t k) (overlapProduct X t u k) *
        actualBraidTrace C X p t u) :
    ∀ k, actualBraidTrace C X p (overlapIndex t k) (overlapProduct X t u k) *
      (Dimensions.groundUnitScalarEquiv C (p.rightTrace (𝟙 X))) ^ k =
        actualBraidTrace C X p t u ^ (k + 1) := by
  intro k
  induction k with
  | zero => simp [overlapIndex, overlapProduct]
  | succ k ih =>
    calc
      _ = (actualBraidTrace C X p (overlapIndex t (k + 1))
          (overlapProduct X t u (k + 1)) *
          Dimensions.groundUnitScalarEquiv C (p.rightTrace (𝟙 X))) *
          (Dimensions.groundUnitScalarEquiv C (p.rightTrace (𝟙 X))) ^ k := by
            rw [pow_succ]; ring
      _ = (actualBraidTrace C X p (overlapIndex t k) (overlapProduct X t u k) *
          actualBraidTrace C X p t u) *
          (Dimensions.groundUnitScalarEquiv C (p.rightTrace (𝟙 X))) ^ k := by rw [hstep k]
      _ = (actualBraidTrace C X p (overlapIndex t k) (overlapProduct X t u k) *
          (Dimensions.groundUnitScalarEquiv C (p.rightTrace (𝟙 X))) ^ k) *
          actualBraidTrace C X p t u := by ring
      _ = _ := by
        rw [ih]
        exact (pow_succ _ (k + 1)).symm

/-- The sharp bound works in any family of unitary braid-block presentations;
it does not depend on a particular choice made by finite-group averaging. -/
theorem sharp_trace_bound_for_presentations_of_overlap_identity
    (C : Ground.BraidedFusionCategory.{v,u}) (X : C.Obj) [Simple X]
    (p : Dimensions.PivotalStructure (C := C.Obj)) (t : ℕ)
    (r : ℕ → ℕ) (d : ∀ n, Fin (r n) → ℕ)
    (e : ∀ n, braidAlgebra X n ≃ₐ[ℂ]
      ∀ i, Matrix (Fin (d n i)) (Fin (d n i)) ℂ)
    (hd : ∀ n i, 0 < d n i)
    (he : ∀ n g i, e n (groupInImage (braidEndRepresentation X n) g) i ∈
      Matrix.unitaryGroup (Fin (d n i)) ℂ)
    (u : braidAlgebra X t)
    (hu : ∀ i, e t u i ∈ Matrix.unitaryGroup (Fin (d t i)) ℂ)
    (hrec : ∀ k, actualBraidTrace C X p (overlapIndex t k) (overlapProduct X t u k) *
      (Dimensions.groundUnitScalarEquiv C (p.rightTrace (𝟙 X))) ^ k =
        actualBraidTrace C X p t u ^ (k + 1)) :
    ‖actualBraidTrace C X p t u‖ ≤
      ‖Dimensions.groundUnitScalarEquiv C (p.rightTrace (𝟙 X))‖ *
        Ground.fpDimension C X ^ (t + 1) := by
  have hδ : Dimensions.groundUnitScalarEquiv C (p.rightTrace (𝟙 X)) ≠ 0 := by
    intro h
    apply Modular.pivotalTrace_simple_ne_zero C p X
    apply (Dimensions.groundUnitScalarEquiv C).injective
    simpa using h
  have hf : 0 < Ground.fpDimension C X :=
    lt_of_lt_of_le zero_lt_one (Ground.one_le_fpDimension C X (Simple.not_isZero X))
  apply norm_bound_of_overlapIndex hδ hf t
    (fun k => actualBraidTrace C X p (overlapIndex t k) (overlapProduct X t u k)) ?_ hrec
  intro k
  have hbound := braid_trace_unitary_bound_ground C X (overlapIndex t k) p
    (r _) (d _) (hd _) (e _) (overlapProduct X t u k) (overlapProduct_unitary X t r d e he u hu k)
  change ‖actualBraidTrace C X p (overlapIndex t k) (overlapProduct X t u k)‖ ≤ _ at hbound
  exact hbound

end PropertyF.Ground.Calculus
