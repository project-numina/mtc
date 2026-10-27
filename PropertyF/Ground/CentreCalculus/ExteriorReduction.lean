module
public import PropertyF.Ground.Centre.SymmetricIntegrality
public import PropertyF.Ground.Dimensions.DimensionCharacter
public import PropertyF.Ground.Fusion.ObjectDimension
public import PropertyF.Ground.Modular.SMatrix

/-! Positive categorical dimensions and the exterior-power reduction. -/
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
