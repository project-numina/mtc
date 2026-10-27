module
public import PropertyF.Ground.Dimensions.WeightedEigenvalue
public import PropertyF.Ground.Dimensions.MultiplicityDefect
public import PropertyF.Ground.Dimensions.NaturalTrace
public import PropertyF.Ground.Dimensions.IntrinsicNonzero

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
open scoped BigOperators
namespace PropertyF.Ground.Dimensions
universe v u

/-- The dimension of a simple object with respect to the natural double-dual
square root. -/
def rootDimension (C : Ground.BraidedFusionCategory.{v,u}) (i : Fin (Ground.rank C)) : ℂ :=
  Ground.unitScalar C (rootTrace C (𝟙 (Ground.simples C i)))

set_option backward.isDefEq.respectTransparency false in
/-- All natural-root simple dimensions are nonzero. -/
theorem rootDimension_ne_zero (C : Ground.BraidedFusionCategory.{v,u}) (i : Fin (Ground.rank C)) :
    rootDimension C i ≠ 0 := by
  letI : Simple (Ground.simples C i) := Ground.simples_simple C i
  have h := rightQuantumTrace_simple_ne_zero C (Ground.simples C i)
    ((fourthDualRootNaturalIso C).app (Ground.simples C i))
  intro hz
  apply h
  apply (groundUnitScalarEquiv C).injective
  have hz' : Ground.unitScalar C (rightQuantumTrace
      ((fourthDualRootNaturalIso C).app (Ground.simples C i))) = 0 := by
    simpa [rootDimension, rootTrace, rightTraceWith, rightQuantumTrace, tensorHom_def] using hz
  simpa only [map_zero, groundUnitScalarEquiv_apply] using hz'

/-- The matrix of traces of the actual natural-root multiplicity defects. -/
def enoTraceMatrix (C : Ground.BraidedFusionCategory.{v,u}) (i : Fin (Ground.rank C)) :
    Fin (Ground.rank C) → Fin (Ground.rank C) → ℂ := fun j k =>
  LinearMap.trace ℂ _ (multiplicityDefect C i j k).toLinearMap

/-- Once the categorical multiplicity defects are involutive and their trace
matrix has the natural-root dimension vector as an eigenvector, ENO's FP
bound follows. Both remaining identities are explicit hypotheses. -/
theorem rootDimension_norm_le_fp_of_trace_matrix
    (C : Ground.BraidedFusionCategory.{v,u}) (i : Fin (Ground.rank C))
    (hinv : ∀ j k, (multiplicityDefect C i j k).toLinearMap *
      (multiplicityDefect C i j k).toLinearMap = 1)
    (heig : ∀ j, ∑ k, enoTraceMatrix C i j k * rootDimension C k =
      rootDimension C i * rootDimension C j) :
    ‖rootDimension C i‖ ≤ Ground.fpSimple C i := by
  apply fusion_dominated_eigenvalue_bound C i (enoTraceMatrix C i) (rootDimension C)
    (rootDimension C i) (Ground.unitIndex C) (rootDimension_ne_zero C _)
  · intro j k
    obtain ⟨n, hn, hb⟩ := multiplicityDefect_trace_integer_bound C i j k (hinv j k)
    change ‖LinearMap.trace ℂ _ (multiplicityDefect C i j k).toLinearMap‖ ≤ _
    rw [hn, Complex.norm_intCast, ← Int.cast_abs]
    exact_mod_cast hb
  · exact heig

end PropertyF.Ground.Dimensions
