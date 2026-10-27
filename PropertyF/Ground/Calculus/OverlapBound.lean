module
public import PropertyF.Ground.Calculus.OverlapUnitary
public import PropertyF.PowerBound

/-! Reduction of the sharp trace bound to the categorical overlap recurrence. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.Calculus
universe v u

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

/-- The sharp bound follows from the single remaining categorical coherence:
the displayed scaled overlap trace identity. All unitary blocks and the
ordinary power bound are obtained from actual finite braid images. -/
theorem sharp_trace_bound_of_overlap_identity
    (C : Ground.BraidedFusionCategory.{v,u}) (X : C.Obj) [Simple X]
    (p : Dimensions.PivotalStructure (C := C.Obj)) (t : ℕ)
    (hfinite : ∀ n, Finite (braidImage X n)) :
    ∃ (r : ℕ → ℕ) (d : ∀ n, Fin (r n) → ℕ)
      (e : ∀ n, braidAlgebra X n ≃ₐ[ℂ]
        ∀ i, Matrix (Fin (d n i)) (Fin (d n i)) ℂ),
      ∀ u : braidAlgebra X t,
        (∀ i, e t u i ∈ Matrix.unitaryGroup (Fin (d t i)) ℂ) →
        (∀ k, actualBraidTrace C X p (overlapIndex t k) (overlapProduct X t u k) *
          (Dimensions.groundUnitScalarEquiv C (p.rightTrace (𝟙 X))) ^ k =
            actualBraidTrace C X p t u ^ (k + 1)) →
        ‖actualBraidTrace C X p t u‖ ≤
          ‖Dimensions.groundUnitScalarEquiv C (p.rightTrace (𝟙 X))‖ *
            Ground.fpDimension C X ^ (t + 1) := by
  obtain ⟨r, d, e, hd, he, hunit⟩ := exists_unitary_overlap_presentations X hfinite
  refine ⟨r, d, e, fun u hu hrec => ?_⟩
  have hδ : Dimensions.groundUnitScalarEquiv C (p.rightTrace (𝟙 X)) ≠ 0 := by
    intro h
    apply Modular.pivotalTrace_simple_ne_zero C p X
    apply (Dimensions.groundUnitScalarEquiv C).injective
    simpa using h
  have hf : 0 < Ground.fpDimension C X :=
    lt_of_lt_of_le zero_lt_one (Ground.one_le_fpDimension C X (Simple.not_isZero X))
  have hnum := PropertyF.trace_bound_of_overlap
    (t := ‖actualBraidTrace C X p t u‖)
    (d := ‖Dimensions.groundUnitScalarEquiv C (p.rightTrace (𝟙 X))‖)
    (f := Ground.fpDimension C X) (m := t + 2) (norm_ne_zero_iff.mpr hδ) hf
  have hres : ‖actualBraidTrace C X p t u‖ ≤
      |‖Dimensions.groundUnitScalarEquiv C (p.rightTrace (𝟙 X))‖| *
        Ground.fpDimension C X ^ ((t + 2) - 1) := by
    apply hnum
    intro k
    have hbound := braid_trace_unitary_bound_ground C X (overlapIndex t k) p
      (r _) (d _) (fun i => Nat.pos_of_ne_zero (hd _ i).ne) (e _)
      (overlapProduct X t u k) (hunit t u hu k)
    change ‖actualBraidTrace C X p (overlapIndex t k) (overlapProduct X t u k)‖ ≤ _ at hbound
    have hexp : overlapIndex t k + 2 = (k + 1) * ((t + 2) - 1) + 1 := by
      rw [overlapIndex_formula]
      have h : (t + 2) - 1 = t + 1 := by omega
      rw [h]
      ring
    rw [hexp] at hbound
    calc
      ‖actualBraidTrace C X p t u‖ ^ (k + 1) =
          ‖actualBraidTrace C X p t u ^ (k + 1)‖ := (norm_pow _ _).symm
      _ = ‖actualBraidTrace C X p (overlapIndex t k) (overlapProduct X t u k) *
          (Dimensions.groundUnitScalarEquiv C (p.rightTrace (𝟙 X))) ^ k‖ :=
            congrArg norm (hrec k).symm
      _ = ‖actualBraidTrace C X p (overlapIndex t k) (overlapProduct X t u k)‖ *
          ‖Dimensions.groundUnitScalarEquiv C (p.rightTrace (𝟙 X))‖ ^ k := by
        rw [norm_mul, norm_pow]
      _ ≤ |‖Dimensions.groundUnitScalarEquiv C (p.rightTrace (𝟙 X))‖| ^ k *
          Ground.fpDimension C X ^ ((k + 1) * ((t + 2) - 1) + 1) := by
        simpa only [abs_of_nonneg (norm_nonneg _), mul_comm] using
          mul_le_mul_of_nonneg_right hbound
            (pow_nonneg (norm_nonneg (Dimensions.groundUnitScalarEquiv C (p.rightTrace (𝟙 X)))) k)
  simpa [abs_of_nonneg (norm_nonneg _)] using hres

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
  have hnum := PropertyF.trace_bound_of_overlap
    (t := ‖actualBraidTrace C X p t u‖)
    (d := ‖Dimensions.groundUnitScalarEquiv C (p.rightTrace (𝟙 X))‖)
    (f := Ground.fpDimension C X) (m := t + 2) (norm_ne_zero_iff.mpr hδ) hf
  have hres : ‖actualBraidTrace C X p t u‖ ≤
      |‖Dimensions.groundUnitScalarEquiv C (p.rightTrace (𝟙 X))‖| *
        Ground.fpDimension C X ^ ((t + 2) - 1) := by
    apply hnum
    intro k
    have hbound := braid_trace_unitary_bound_ground C X (overlapIndex t k) p
      (r _) (d _) (hd _) (e _)
      (overlapProduct X t u k) (overlapProduct_unitary X t r d e he u hu k)
    change ‖actualBraidTrace C X p (overlapIndex t k) (overlapProduct X t u k)‖ ≤ _ at hbound
    have hexp : overlapIndex t k + 2 = (k + 1) * ((t + 2) - 1) + 1 := by
      rw [overlapIndex_formula]
      have h : (t + 2) - 1 = t + 1 := by omega
      rw [h]
      ring
    rw [hexp] at hbound
    calc
      ‖actualBraidTrace C X p t u‖ ^ (k + 1) =
          ‖actualBraidTrace C X p t u ^ (k + 1)‖ := (norm_pow _ _).symm
      _ = ‖actualBraidTrace C X p (overlapIndex t k) (overlapProduct X t u k) *
          (Dimensions.groundUnitScalarEquiv C (p.rightTrace (𝟙 X))) ^ k‖ :=
            congrArg norm (hrec k).symm
      _ = ‖actualBraidTrace C X p (overlapIndex t k) (overlapProduct X t u k)‖ *
          ‖Dimensions.groundUnitScalarEquiv C (p.rightTrace (𝟙 X))‖ ^ k := by
        rw [norm_mul, norm_pow]
      _ ≤ |‖Dimensions.groundUnitScalarEquiv C (p.rightTrace (𝟙 X))‖| ^ k *
          Ground.fpDimension C X ^ ((k + 1) * ((t + 2) - 1) + 1) := by
        simpa only [abs_of_nonneg (norm_nonneg _), mul_comm] using
          mul_le_mul_of_nonneg_right hbound
            (pow_nonneg (norm_nonneg (Dimensions.groundUnitScalarEquiv C (p.rightTrace (𝟙 X)))) k)
  simpa [abs_of_nonneg (norm_nonneg _)] using hres

end PropertyF.Ground.Calculus
