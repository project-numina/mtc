module
public import MTC.CategoryTheory.Dimensions.DimensionCharacter
public import MTC.Fusion.Agreement
public import MTC.Fusion.SpectralIntegral
public import MTC.PropertyF.Reduction.CharacterReality

open MTC.Fusion MTC.Braided MTC.CategoryTheory.Dimensions MTC.PropertyF.Reduction

/-! # Algebraic integrality of pivotal dimensions

A simple pivotal dimension is an eigenvalue of an integer fusion matrix. The
result extends to all objects by the actual semisimple decomposition.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
open scoped BigOperators Matrix Matrix.Norms.Operator
namespace MTC.Center.Normalization
universe v u
variable (C : BraidedFusionCategory.{v,u})

/-- Values of any nonzero fusion character are algebraic integers. -/
theorem fusionCharacter_isIntegral
    {χ : Fin (rank C) → ℂ} {i₀ : Fin (rank C)} (hχ : χ i₀ ≠ 0)
    (hchar : IsFusionMultiplicative C χ) (i : Fin (rank C)) : IsIntegral ℤ (χ i) := by
  let A : Matrix (Fin (rank C)) (Fin (rank C)) ℤ := fun j k ↦ fusionCoeff C i j k
  let B : Matrix (Fin (rank C)) (Fin (rank C)) ℂ := A.map (Int.castRingHom ℂ)
  have hB : B = fun j k ↦ (fusionCoeff C i j k : ℂ) := by
    ext j k
    change (((fusionCoeff C i j k : ℤ) : ℂ)) = (fusionCoeff C i j k : ℂ)
    norm_cast
  have heig : B *ᵥ χ = χ i • χ := by
    rw [hB]
    exact fusion_character_eigenvector hchar i
  have hv : χ ≠ 0 := fun h ↦ hχ (congrFun h i₀)
  have hs : χ i ∈ spectrum ℂ B := Matrix.spectrum_toLin' B ▸
    (Module.End.hasEigenvalue_of_hasEigenvector
      ⟨Module.End.mem_eigenspace_iff.mpr (funext fun j ↦ (congrFun heig j)), hv⟩).mem_spectrum
  exact ⟨A.charpoly, A.charpoly_monic, by
    change Polynomial.eval₂ (Int.castRingHom ℂ) (χ i) A.charpoly = 0
    rw [Polynomial.eval₂_eq_eval_map, ← Matrix.charpoly_map]
    exact (Matrix.mem_spectrum_iff_isRoot_charpoly.mp hs).eq_zero⟩

/-- The pivotal dimension of every object of a braided fusion category is an
algebraic integer, without sphericality. -/
theorem pivotalDimension_isIntegral (p : PivotalStructure (C := C.Obj)) (X : C.Obj) :
    IsIntegral ℤ (pivotalDimension C p X) := by
  rw [pivotalDimension_decomposition C p]
  apply IsIntegral.sum
  intro i hi
  exact (isIntegral_natCast (R := ℤ) (simpleMultiplicity C i X)).mul <|
    fusionCharacter_isIntegral C ((pivotalDimension_unitIndex C p).symm ▸ one_ne_zero)
      (pivotalDimension_character C p) i

end MTC.Center.Normalization
end
