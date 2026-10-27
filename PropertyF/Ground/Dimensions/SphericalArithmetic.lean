module
public import PropertyF.Ground.Dimensions.PseudoUnitary
public import PropertyF.Ground.Integrate.CharacterReality
public import PropertyF.Ground.Modular.DimensionNonzero
open scoped BigOperators

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.Dimensions

/-- Simple pivotal dimensions are nonzero, by rigidity, semisimplicity and Schur. -/
theorem pivotalDimension_simple_ne_zero (C : Ground.BraidedFusionCategory)
    (p : PivotalStructure (C := C.Obj)) (i : Fin (Ground.rank C)) :
    pivotalDimension C p (Ground.simples C i) ≠ 0 := by
  have h := Ground.Modular.simpleDimension_ne_zero C p i
  simpa [Ground.Modular.simpleDimension, pivotalDimension, Ground.unitScalar_eq_equiv] using h

/-- Every Galois conjugate of a self-dual pivotal dimension is real. The
categorical equality on dual labels is an explicit remaining input. -/
theorem galois_pivotalDimension_real_of_dual (C : Ground.BraidedFusionCategory)
    (p : PivotalStructure (C := C.Obj))
    (hdual : ∀ i, pivotalDimension C p (Ground.simples C (Ground.dualIndex C i)) =
      pivotalDimension C p (Ground.simples C i)) (σ : ℂ ≃+* ℂ) (i : Fin (Ground.rank C)) :
    ((σ (pivotalDimension C p (Ground.simples C i))).re : ℂ) =
      σ (pivotalDimension C p (Ground.simples C i)) := by
  apply Complex.conj_eq_iff_re.mp
  apply Ground.selfDual_character_galois_real C
    (fun j => pivotalDimension C p (Ground.simples C j)) (Ground.unitIndex C)
  · obtain ⟨e⟩ := Ground.unitIndex_iso C
    rw [pivotalDimension_iso C p e, pivotalDimension_unit]
    exact one_ne_zero
  · exact pivotalDimension_character C p
  · exact hdual

end PropertyF.Ground.Dimensions
