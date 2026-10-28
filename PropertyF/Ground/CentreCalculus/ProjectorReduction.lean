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
variable (C : BraidedFusionCategory.{v,u}) (p : Dimensions.PivotalStructure (C := C.Obj))
  (hdim : Modular.HasFPSimpleDimensions C p)

include hdim in
/-- Equality of positive simple dimensions and FP dimensions extends to every
object, including zero objects and the images of split idempotents. -/
theorem pivotalDimension_eq_fpDimension (X : C.Obj) : Dimensions.pivotalDimension C p X = (fpDimension C X : ℂ) := by
  rw [Dimensions.pivotalDimension_decomposition]
  simp only [fpDimension, Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_natCast,
    ← hdim, Modular.simpleDimension, Dimensions.pivotalDimension, unitScalar_eq_equiv]

/-- If the falling factorial of an object's dimension is the dimension of an
actual object up to a positive scalar at every degree, the dimension is an
integer. The remaining categorical task is to construct those objects and
establish their dimensions using alternating projectors. -/
theorem integral_of_exterior_dimensions (X : C.Obj)
    (hExterior : ∀ n : ℕ, ∃ Y : C.Obj,
      (∏ k ∈ Finset.range n, (fpDimension C X - (k : ℝ))) =
        (Nat.factorial n : ℝ) * fpDimension C Y) :
    ∃ m : ℕ, fpDimension C X = m :=
  Centre.integral_of_nonnegative_falling_factorials (fpDimension_nonneg C X) fun n ↦
    let ⟨Y, hY⟩ := hExterior n
    hY.symm ▸ mul_nonneg (Nat.cast_nonneg _) (fpDimension_nonneg C Y)

include hdim in
/-- The same reduction stated using actual pivotal dimensions, so that a
split alternating projector can supply the witnesses. -/
theorem integral_of_pivotal_exterior_dimensions (X : C.Obj)
    (hExterior : ∀ n : ℕ, ∃ Y : C.Obj,
      (Nat.factorial n : ℂ) * Dimensions.pivotalDimension C p Y =
        ∏ k ∈ Finset.range n, ((fpDimension C X : ℂ) - (k : ℂ))) :
    ∃ m : ℕ, fpDimension C X = m :=
  integral_of_exterior_dimensions C X fun n ↦
    let ⟨Y, hY⟩ := hExterior n
    ⟨Y, Complex.ofReal_injective <| by
      rw [pivotalDimension_eq_fpDimension C p hdim Y] at hY
      simpa only [Complex.ofReal_prod, Complex.ofReal_sub, Complex.ofReal_natCast,
        Complex.ofReal_mul] using hY.symm⟩

end PropertyF.Ground.CentreCalculus

open CategoryTheory CategoryTheory.MonoidalCategory
open scoped BigOperators
namespace PropertyF.Ground.CentreCalculus
universe v u
variable (C : BraidedFusionCategory.{v,u}) (p : Dimensions.PivotalStructure (C := C.Obj))
  (hdim : Modular.HasFPSimpleDimensions C p)

/-- The symmetric-group order is invertible over the complex numbers. -/
@[instance_reducible] def permutationCardInvertible (n : ℕ) :
    Invertible (Fintype.card (Equiv.Perm (Fin n)) : ℂ) :=
  invertibleOfNonzero (by exact_mod_cast Fintype.card_ne_zero)

include hdim in
/-- A trace formula for actual alternating projectors implies integrality. The
existence of the permutation action and the trace formula remain explicit. -/
theorem integral_of_alternating_projector_trace (X : C.Obj)
    (hTrace : ∀ n : ℕ, ∃ ρ : Equiv.Perm (Fin n) →* End (tensorPower X n),
      letI := permutationCardInvertible n
      (Nat.factorial n : ℂ) * unitScalar C
        (p.rightTrace ((Centre.alternatingProjector (k := ℂ) ρ).asHom)) =
          ∏ k ∈ Finset.range n, ((fpDimension C X : ℂ) - (k : ℂ))) :
    ∃ m : ℕ, fpDimension C X = m :=
  integral_of_pivotal_exterior_dimensions C p hdim X fun n ↦
    let ⟨ρ, hρ⟩ := hTrace n
    let := permutationCardInvertible n
    let ⟨Y, hY⟩ := Centre.alternatingProjector_trace ρ p
    ⟨Y, (congrArg (fun t ↦ (Nat.factorial n : ℂ) * unitScalar C t) hY.symm).trans hρ⟩

/-- Multiplying the alternating-projector trace by the group order gives
the signed sum of the actual categorical permutation traces. -/
theorem alternatingProjector_scalar_trace (X : C.Obj) (n : ℕ)
    (ρ : Equiv.Perm (Fin n) →* End X) :
    letI := permutationCardInvertible n
    (Nat.factorial n : ℂ) * unitScalar C
      (p.rightTrace ((Centre.alternatingProjector (k := ℂ) ρ).asHom)) =
      ∑ σ : Equiv.Perm (Fin n), (Centre.permutationSign ℂ n σ : ℂ) *
        unitScalar C (p.rightTrace (ρ σ).asHom) := by
  let := permutationCardInvertible n
  -- Both statements concern the same projector; its trace is the signed average.
  have ht : p.rightTrace ((Centre.alternatingProjector (k := ℂ) ρ).asHom) =
      ⅟(Fintype.card (Equiv.Perm (Fin n)) : ℂ) •
        ∑ σ : Equiv.Perm (Fin n),
          (Centre.permutationSign ℂ n σ : ℂ) • p.rightTrace (ρ σ).asHom := by
    rw [Centre.alternatingProjector, Centre.algebraAverage_eq_sum]
    change p.rightTrace ((⅟(Fintype.card (Equiv.Perm (Fin n)) : ℂ) •
      ∑ σ : Equiv.Perm (Fin n), (Centre.permutationSign ℂ n σ : ℂ) • ρ σ).asHom) = _
    simp only [End.smul_asHom, End.sum_asHom, p.rightTrace_smul]
    congr 1
    simpa only [Dimensions.rightTraceLinear, LinearMap.coe_mk, AddHom.coe_mk,
      p.rightTrace_smul] using
      map_sum (Dimensions.rightTraceLinear p X)
        (fun σ : Equiv.Perm (Fin n) => (Centre.permutationSign ℂ n σ : ℂ) • (ρ σ).asHom) Finset.univ
  rw [ht, unitScalar_eq_equiv]
  simp only [map_smul, map_sum, smul_eq_mul]
  have hc : (Fintype.card (Equiv.Perm (Fin n)) : ℂ) = (Nat.factorial n : ℂ) := by
    simp [Fintype.card_perm]
  rw [← hc, ← mul_assoc, mul_invOf_self, one_mul]
  simp only [unitScalar_eq_equiv]

include hdim in
/-- It suffices to evaluate the unnormalized signed trace sum for each
permutation action. The existence and evaluation of these actions are still
explicit hypotheses. -/
theorem integral_of_signed_permutation_traces (X : C.Obj)
    (hTrace : ∀ n : ℕ, ∃ ρ : Equiv.Perm (Fin n) →* End (tensorPower X n),
      (∑ σ : Equiv.Perm (Fin n), (Centre.permutationSign ℂ n σ : ℂ) *
        unitScalar C (p.rightTrace (ρ σ).asHom)) =
          ∏ k ∈ Finset.range n, ((fpDimension C X : ℂ) - (k : ℂ))) :
    ∃ m : ℕ, fpDimension C X = m :=
  integral_of_alternating_projector_trace C p hdim X fun n ↦
    let ⟨ρ, hρ⟩ := hTrace n
    ⟨ρ, (alternatingProjector_scalar_trace C p _ n ρ).trans hρ⟩

end PropertyF.Ground.CentreCalculus
