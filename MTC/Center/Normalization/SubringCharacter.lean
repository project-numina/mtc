module
public import MTC.Center.Normalization.SubringGrading
public import MTC.Center.Normalization.CharacterExtension
public import MTC.Center.Normalization.GradingTwist

open MTC.Fusion MTC.Braided MTC.Center.Braid MTC.CategoryTheory.Dimensions

/-! # Extending and applying fusion-subring degree characters

This supplies the group and pivotal-twist part of normalization, conditional
on an actual character describing the restricted pivotal dimensions.
It does not construct that character or identify neutral degrees with adjoint
labels.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace MTC.Center.Normalization
universe v u
variable {C : BraidedFusionCategory.{v,u}} {A : Finset (Fin (rank C))}
variable (hA : IsFusionSubring C A)

/-- Any unit-valued scalar assignment satisfying subring fusion relations
defines a character of the subring degree group. -/
def subringCharacterOfScalars (c : A → ℂˣ)
    (hu : c ⟨unitIndex C, hA.unit⟩ = 1)
    (hmul : ∀ i j k : A, 0 < fusionCoeff C i j k → c k = c i * c j) :
    Multiplicative (SubringDegreeGroup hA) →* ℂˣ :=
  AddMonoidHom.toMultiplicative <|
    subringDegreeLift hA (fun i ↦ Additive.ofMul (c i))
      (by change c ⟨unitIndex C, hA.unit⟩ = 1; exact hu)
      (fun i j k h ↦ by change c k = c i * c j; exact hmul i j k h)

/-- The character induced by compatible scalars recovers each scalar. -/
theorem subringCharacterOfScalars_apply (c : A → ℂˣ)
    (hu : c ⟨unitIndex C, hA.unit⟩ = 1)
    (hmul : ∀ i j k : A, 0 < fusionCoeff C i j k → c k = c i * c j) (i : A) :
    subringCharacterOfScalars hA c hu hmul (Multiplicative.ofAdd (subringDegree hA i)) = c i := by
  change subringDegreeLift hA (fun i ↦ Additive.ofMul (c i))
    (by change c ⟨unitIndex C, hA.unit⟩ = 1; exact hu)
    (fun i j k h ↦ by change c k = c i * c j; exact hmul i j k h)
    (subringDegree hA i) = _
  rw [subringDegreeLift_apply]
  rfl

/-- A subring degree character that is positive on all ambient-neutral simple
labels extends to a character of the ambient degree group. -/
theorem subringCharacter_extend_of_positive_neutral
    (η : Multiplicative (SubringDegreeGroup hA) →* ℂˣ)
    (hpositive : ∀ i : A, fusionDegree C i = 0 → ∃ r : ℝ,
      0 < r ∧ (η (Multiplicative.ofAdd (subringDegree hA i)) : ℂ) = r) :
    ∃ ψ : Multiplicative (FusionDegreeGroup C) →* ℂˣ,
      ∀ i : A, ψ (Multiplicative.ofAdd (fusionDegree C i)) =
        η (Multiplicative.ofAdd (subringDegree hA i)) := by
  let φ := AddMonoidHom.toMultiplicative (subringDegreeToAmbient hA)
  have hker : ∀ g ∈ φ.ker, ∃ r : ℝ, 0 < r ∧ (η g : ℂ) = r := by
    intro g hg
    have hg' : Multiplicative.toAdd g ∈ (subringDegreeToAmbient hA).ker := by
      change subringDegreeToAmbient hA (Multiplicative.toAdd g) = 0
      exact hg
    obtain ⟨i, hi, hneutral⟩ := (subringDegreeToAmbient_kernel_iff hA _).mp hg'
    obtain ⟨r, hr, hrval⟩ := hpositive i hneutral
    refine ⟨r, hr, ?_⟩
    change (η (Multiplicative.ofAdd (Multiplicative.toAdd g)) : ℂ) = r
    rw [← hi]
    exact hrval
  obtain ⟨ψ, hψ⟩ := character_extend_along_of_positive_kernel φ η hker
  refine ⟨ψ, fun i ↦ ?_⟩
  have h := DFunLike.congr_fun hψ (Multiplicative.ofAdd (subringDegree hA i))
  change ψ (Multiplicative.ofAdd (subringDegreeToAmbient hA (subringDegree hA i))) =
    η (Multiplicative.ofAdd (subringDegree hA i)) at h
  simpa only [subringDegreeToAmbient_apply] using h

/-- If a subring character describes the old pivotal dimensions relative to
FP dimensions, and is positive on ambient-neutral simples, an actual pivotal
structure normalizes the dimensions on that subring. -/
theorem normalize_pivotal_of_subring_character
    (p : PivotalStructure (C := C.Obj))
    (η : Multiplicative (SubringDegreeGroup hA) →* ℂˣ)
    (hpositive : ∀ i : A, fusionDegree C i = 0 → ∃ r : ℝ,
      0 < r ∧ (η (Multiplicative.ofAdd (subringDegree hA i)) : ℂ) = r)
    (hη : ∀ i : A, pivotalDimension C p (simples C i) =
      (η (Multiplicative.ofAdd (subringDegree hA i)) : ℂ) * (fpSimple C i : ℂ)) :
    ∃ q : PivotalStructure (C := C.Obj), ∀ i : A,
      pivotalDimension C q (simples C i) = (fpSimple C i : ℂ) := by
  obtain ⟨ψ, hψ⟩ := subringCharacter_extend_of_positive_neutral hA η hpositive
  refine ⟨pivotalTwistOfDegreeCharacter p ψ⁻¹, fun i ↦ ?_⟩
  rw [pivotalTwistOfDegreeCharacter_dimension, hη i]
  simp only [characterScalar, MonoidHom.inv_apply, Units.val_inv_eq_inv_val, hψ]
  have hne : (η (Multiplicative.ofAdd (subringDegree hA i)) : ℂ) ≠ 0 := Units.ne_zero _
  rw [← mul_assoc, inv_mul_cancel₀ hne, one_mul]

/-- A subring dimension character and positivity of the actual pivotal
dimensions on ambient-neutral labels suffice for normalization. -/
theorem normalize_pivotal_of_subring_character_and_positive_dimensions
    (p : PivotalStructure (C := C.Obj))
    (η : Multiplicative (SubringDegreeGroup hA) →* ℂˣ)
    (hpositive : ∀ i : A, fusionDegree C i = 0 → ∃ r : ℝ,
      0 < r ∧ pivotalDimension C p (simples C i) = r)
    (hη : ∀ i : A, pivotalDimension C p (simples C i) =
      (η (Multiplicative.ofAdd (subringDegree hA i)) : ℂ) * (fpSimple C i : ℂ)) :
    ∃ q : PivotalStructure (C := C.Obj), ∀ i : A,
      pivotalDimension C q (simples C i) = (fpSimple C i : ℂ) := by
  apply normalize_pivotal_of_subring_character hA p η ?_ hη
  intro i hi
  obtain ⟨r, hr, hrval⟩ := hpositive i hi
  have hfp : (fpSimple C i : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (fpSimple_pos C i))
  refine ⟨r / fpSimple C i, div_pos hr (fpSimple_pos C i), ?_⟩
  rw [Complex.ofReal_div, eq_div_iff hfp, ← hη i, hrval]

/-- Fusion-compatible scalar ratios and positivity on the neutral ambient
component suffice to normalize the pivotal dimensions on a fusion subring. -/
theorem normalize_pivotal_of_fusion_scalar_ratios
    (p : PivotalStructure (C := C.Obj)) (c : A → ℂˣ)
    (hu : c ⟨unitIndex C, hA.unit⟩ = 1)
    (hmul : ∀ i j k : A, 0 < fusionCoeff C i j k → c k = c i * c j)
    (hpositive : ∀ i : A, fusionDegree C i = 0 → ∃ r : ℝ,
      0 < r ∧ pivotalDimension C p (simples C i) = r)
    (hc : ∀ i : A, pivotalDimension C p (simples C i) = (c i : ℂ) * (fpSimple C i : ℂ)) :
    ∃ q : PivotalStructure (C := C.Obj), ∀ i : A,
      pivotalDimension C q (simples C i) = (fpSimple C i : ℂ) := by
  apply normalize_pivotal_of_subring_character_and_positive_dimensions hA p
    (subringCharacterOfScalars hA c hu hmul) hpositive
  intro i
  simpa only [subringCharacterOfScalars_apply] using hc i

end MTC.Center.Normalization
end
