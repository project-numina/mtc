module
public import PropertyF.Ground.Centre.SymmetricIntegrality
public import PropertyF.Ground.Dimensions.DimensionCharacter
public import PropertyF.Ground.Fusion.ObjectDimension
public import PropertyF.Ground.Modular.SMatrix
public import PropertyF.Ground.Centre.Averaging
public import PropertyF.Definitions

/-!
# Exterior-power and projector integrality reductions

Positive pivotal dimensions are identified with Frobenius–Perron dimensions.
Falling factorials and alternating-projector traces then provide integrality
criteria for objects and simple dimensions.
-/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
open scoped BigOperators
namespace PropertyF.Ground.CentreCalculus
universe v u

/-- Equality of positive simple dimensions and FP dimensions extends to every
object, including zero objects and the images of split idempotents. -/
theorem pivotalDimension_eq_fpDimension (C : BraidedFusionCategory.{v,u})
    (p : Dimensions.PivotalStructure (C := C.Obj))
    (hdim : ∀ i, Modular.simpleDimension C p i = (fpSimple C i : ℂ))
    (X : C.Obj) : Dimensions.pivotalDimension C p X = (fpDimension C X : ℂ) := by
  rw [Dimensions.pivotalDimension_decomposition]
  unfold fpDimension
  simp only [Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_natCast]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  simpa [Modular.simpleDimension, Dimensions.pivotalDimension, unitScalar_eq_equiv] using hdim i

/-- If the falling factorial of an object's dimension is the dimension of an
actual object up to a positive scalar at every degree, the dimension is an
integer. The remaining categorical task is to construct those objects and
establish their dimensions using alternating projectors. -/
theorem integral_of_exterior_dimensions (C : BraidedFusionCategory.{v,u})
    (X : C.Obj)
    (hExterior : ∀ n : ℕ, ∃ Y : C.Obj,
      (∏ k ∈ Finset.range n, (fpDimension C X - (k : ℝ))) =
        (Nat.factorial n : ℝ) * fpDimension C Y) :
    ∃ m : ℕ, fpDimension C X = m := by
  apply Centre.integral_of_nonnegative_falling_factorials _ (fpDimension_nonneg C X)
  intro n
  obtain ⟨Y, hY⟩ := hExterior n
  rw [hY]
  exact mul_nonneg (Nat.cast_nonneg _) (fpDimension_nonneg C Y)

/-- The same reduction stated using actual pivotal dimensions, so that a
split alternating projector can supply the witnesses. -/
theorem integral_of_pivotal_exterior_dimensions (C : BraidedFusionCategory.{v,u})
    (p : Dimensions.PivotalStructure (C := C.Obj))
    (hdim : ∀ i, Modular.simpleDimension C p i = (fpSimple C i : ℂ))
    (X : C.Obj)
    (hExterior : ∀ n : ℕ, ∃ Y : C.Obj,
      (Nat.factorial n : ℂ) * Dimensions.pivotalDimension C p Y =
        ∏ k ∈ Finset.range n, ((fpDimension C X : ℂ) - (k : ℂ))) :
    ∃ m : ℕ, fpDimension C X = m := by
  apply integral_of_exterior_dimensions C X
  intro n
  obtain ⟨Y, hY⟩ := hExterior n
  refine ⟨Y, ?_⟩
  rw [pivotalDimension_eq_fpDimension C p hdim Y] at hY
  apply Complex.ofReal_injective
  simpa only [Complex.ofReal_prod, Complex.ofReal_sub, Complex.ofReal_natCast,
    Complex.ofReal_mul] using hY.symm

end PropertyF.Ground.CentreCalculus

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
        (p.rightTrace ((Centre.alternatingProjector (k := ℂ) ρ).asHom)) =
          ∏ k ∈ Finset.range n, ((fpDimension C X : ℂ) - (k : ℂ))) :
    ∃ m : ℕ, fpDimension C X = m := by
  apply integral_of_pivotal_exterior_dimensions C p hdim X
  intro n
  obtain ⟨ρ, hρ⟩ := hTrace n
  letI := permutationCardInvertible n
  obtain ⟨Y, hY⟩ := Centre.alternatingProjector_trace ρ p
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
      (p.rightTrace ((Centre.alternatingProjector (k := ℂ) ρ).asHom)) =
      ∑ σ : Equiv.Perm (Fin n), (Centre.permutationSign ℂ n σ : ℂ) *
        unitScalar C (p.rightTrace (ρ σ).asHom) := by
  letI := permutationCardInvertible n
  -- Both statements concern the same projector; its trace is the signed average.
  have ht : p.rightTrace ((Centre.alternatingProjector (k := ℂ) ρ).asHom) =
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
