module
public import MTC.Center.SymmetricIntegrality
public import MTC.CategoryTheory.Dimensions.DimensionCharacter
public import MTC.Fusion.ObjectDimension
public import MTC.Modular.SMatrix
public import MTC.Center.Averaging
public import MTC.Braided.Definitions

open MTC.Fusion

open MTC.Braided

/-!
# Exterior-power and projector integrality reductions

Positive pivotal dimensions are identified with Frobenius–Perron dimensions.
Falling factorials and alternating-projector traces then provide integrality
criteria for objects and simple dimensions. The notation `sgn ℂ n σ`
denotes the permutation sign in the scalar ring.
-/
@[expose] public noncomputable section
open MTC.Modular (HasFPSimpleDimensions)
local notation "sgn" => MTC.Center.permutationSign
open MTC.CategoryTheory.Dimensions
open Equiv (Perm)
open Fintype (card_perm)
open CategoryTheory CategoryTheory.MonoidalCategory
open scoped BigOperators
namespace MTC.Center.Trace
universe v u

/-- Signed sum of a function on permutations of a finite set. -/
def signedTraceSum {R : Type*} [CommRing R] {n : ℕ} (F : Perm (Fin n) → R) : R :=
  ∑ σ, (sgn R n σ : R) * F σ

variable {C : BraidedFusionCategory.{v,u}} {p : PivotalStructure (C := C.Obj)}
  (hdim : HasFPSimpleDimensions C p) {X : C.Obj}

include hdim in
/-- Positive simple dimensions agree with pivotal dimensions on the simple family. -/
theorem pivotalDimensions_on_simples :
    ∀ i, pivotalDimension C p (simples C i) = (fpSimple C i : ℂ) := fun i => by
  simpa only [pivotalDimension, unitScalar_eq_equiv, Modular.simpleDimension] using hdim i

/-- The Frobenius–Perron dimension of an object is a natural number. -/
abbrev IsFPIntegral (C : BraidedFusionCategory.{v,u}) (X : C.Obj) : Prop :=
  ∃ n : ℕ, fpDimension C X = n

/-- Every falling factorial is a factorial multiple of a value of `dim`. -/
abbrev HasFallingFactorialDimensions {A R : Type*} [CommRing R] (d : R) (dim : A → R) : Prop :=
  ∀ n : ℕ, ∃ Y, (Nat.factorial n : R) * dim Y = ∏ k ∈ Finset.range n, (d - (k : R))

/-- If the falling factorial of an object's dimension is the dimension of an
actual object up to a positive scalar at every degree, the dimension is an
integer. The remaining categorical task is to construct those objects and
establish their dimensions using alternating projectors. -/
theorem integral_of_exterior_dimensions
    (hExterior : HasFallingFactorialDimensions (fpDimension C X) (fpDimension C)) :
    IsFPIntegral C X :=
  MTC.Center.integral_of_nonnegative_falling_factorials (fpDimension_nonneg X) fun n ↦
    let ⟨Y, hY⟩ := hExterior n
    hY ▸ mul_nonneg (Nat.cast_nonneg _) (fpDimension_nonneg Y)

include hdim in
/-- The same reduction stated using actual pivotal dimensions, so that a
split alternating projector can supply the witnesses. -/
theorem integral_of_pivotal_exterior
    (hExterior : HasFallingFactorialDimensions (fpDimension C X : ℂ) (pivotalDimension C p)) :
    IsFPIntegral C X :=
  integral_of_exterior_dimensions fun n ↦ (hExterior n).imp fun Y hY ↦
    Complex.ofReal_injective <| by simpa [pivotalDimension_eq_fp (pivotalDimensions_on_simples hdim) _] using hY

end MTC.Center.Trace

open CategoryTheory CategoryTheory.MonoidalCategory
open scoped BigOperators
namespace MTC.Center.Trace
universe v u
variable {C : BraidedFusionCategory.{v,u}} {p : PivotalStructure (C := C.Obj)}
  (hdim : HasFPSimpleDimensions C p) {X : C.Obj}

/-- The symmetric-group order is invertible over the complex numbers. -/
@[instance_reducible] def permutationCardInvertible (n : ℕ) :
    Invertible (Fintype.card (Perm (Fin n)) : ℂ) :=
  invertibleOfNonzero (by exact_mod_cast Fintype.card_ne_zero)

/-- The permutation-group order has its canonical local inverse over ℂ. -/
local instance permutationCardInvertibleInstance (n : ℕ) :
    Invertible (Fintype.card (Perm (Fin n)) : ℂ) := permutationCardInvertible n

include hdim in
/-- A trace formula for actual alternating projectors implies integrality. The
existence of the permutation action and the trace formula remain explicit. -/
theorem integral_of_alternating_projector_trace
    (hTrace : ∀ n : ℕ, ∃ ρ : Perm (Fin n) →* End (tensorPower X n),
      letI := permutationCardInvertible n
      (Nat.factorial n : ℂ) * unitScalar C
        (p.rightTrace ((MTC.Center.alternatingProjector (k := ℂ) ρ).asHom)) =
          ∏ k ∈ Finset.range n, ((fpDimension C X : ℂ) - (k : ℂ))) :
    IsFPIntegral C X :=
  integral_of_pivotal_exterior hdim fun n ↦ (hTrace n).elim fun ρ hρ ↦
    (MTC.Center.alternatingProjector_trace ρ p).imp fun _ hY ↦
      (congrArg (fun t ↦ (Nat.factorial n : ℂ) * unitScalar C t) hY.symm).trans hρ

variable {n : ℕ} (ρ : Perm (Fin n) →* End X)

/-- The trace of an alternating projector is the signed average of traces. -/
theorem rightTrace_alternatingProjector :
    letI := permutationCardInvertible n
    p.rightTrace ((MTC.Center.alternatingProjector (k := ℂ) ρ).asHom) =
      ⅟(Fintype.card (Perm (Fin n)) : ℂ) •
        ∑ σ : Perm (Fin n), (sgn ℂ n σ : ℂ) • p.rightTrace (ρ σ).asHom := by
  rw [MTC.Center.alternatingProjector, MTC.Center.algebraAverage_eq_sum]
  change (MTC.CategoryTheory.Dimensions.rightTraceWithLinear (k := ℂ) (p.iso X))
    ((⅟(Fintype.card (Perm (Fin n)) : ℂ) •
      ∑ σ : Perm (Fin n), (sgn ℂ n σ : ℂ) • ρ σ).asHom) = _
  simp only [End.smul_asHom, End.sum_asHom, map_smul, map_sum,
    MTC.CategoryTheory.Dimensions.rightTraceWithLinear, LinearMap.coe_mk, AddHom.coe_mk, PivotalStructure.rightTrace]

/-- Multiplying the alternating-projector trace by the group order gives
 the signed sum of the actual categorical permutation traces. -/
theorem alternatingProjector_scalar_trace :
    letI := permutationCardInvertible n
    (Nat.factorial n : ℂ) * unitScalar C
      (p.rightTrace ((MTC.Center.alternatingProjector (k := ℂ) ρ).asHom)) =
      ∑ σ : Perm (Fin n), (sgn ℂ n σ : ℂ) *
        unitScalar C (p.rightTrace (ρ σ).asHom) := by
  simp [rightTrace_alternatingProjector, unitScalar_eq_equiv, card_perm, n.factorial_ne_zero]

include hdim in
/-- It suffices to evaluate the unnormalized signed trace sum for each
permutation action. The existence and evaluation of these actions are still
explicit hypotheses. -/
theorem integral_of_signed_permutation_traces
    (hTrace : ∀ n : ℕ, ∃ ρ : Perm (Fin n) →* End (tensorPower X n),
      signedTraceSum (fun σ ↦ unitScalar C (p.rightTrace (ρ σ).asHom)) =
          ∏ k ∈ Finset.range n, ((fpDimension C X : ℂ) - (k : ℂ))) :
    IsFPIntegral C X :=
  integral_of_alternating_projector_trace hdim fun n ↦
    let ⟨ρ, hρ⟩ := hTrace n
    ⟨ρ, (alternatingProjector_scalar_trace (C := C) (p := p) ρ).trans hρ⟩

end MTC.Center.Trace
