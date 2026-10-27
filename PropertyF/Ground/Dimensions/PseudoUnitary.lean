module
public import PropertyF.Ground.Dimensions.DimensionCharacter
public import PropertyF.Ground.Dimensions.GlobalInequality

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
open scoped BigOperators
namespace PropertyF.Ground.Dimensions

/-- For a spherical structure with real simple dimensions satisfying the
tensor trace law, pseudo-unitarity is equivalent to saturation of
the absolute-value bound at every simple object. The trace laws and reality
are explicit premises, not assumptions hidden in the category. -/
theorem pseudoUnitary_iff_simple_saturation (C : Ground.BraidedFusionCategory)
    (p : PivotalStructure (C := C.Obj)) (hp : p.IsSpherical)
    (d : Fin (Ground.rank C) → ℝ)
    (hreal : ∀ i, pivotalDimension C p (Ground.simples C i) = (d i : ℂ))
    (hmul : ∀ X Y, pivotalDimension C p (X ⊗ Y) =
      pivotalDimension C p X * pivotalDimension C p Y) :
    Ground.PseudoUnitary C ↔ ∀ i, |d i| = Ground.fpSimple C i := by
  have hr : ∀ i, Ground.unitScalar C (rightQuantumTrace (p.iso (Ground.simples C i))) =
      (d i : ℂ) := by
    intro i
    simpa [pivotalDimension, rightTrace_id] using hreal i
  have hg := target_globalDimension_real C p hp d hr
  have hb : ∀ i, |d i| ≤ Ground.fpSimple C i := by
    intro i
    have h := galois_pivotalDimension_norm_le_fpSimple C p hmul (RingEquiv.refl ℂ) i
    simpa [hreal, Complex.norm_real] using h
  rw [← global_sum_squares_eq_iff C d hb]
  unfold Ground.PseudoUnitary
  rw [hg]
  exact Complex.ofReal_injective.eq_iff

end PropertyF.Ground.Dimensions
