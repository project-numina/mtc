module
public import PropertyF.Ground.Dimensions.PivotalPairing

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.Dimensions
universe v u
/-- Real pivotal simple dimensions are invariant under duality. -/
theorem pivotalDimension_dual_of_real (C : Ground.BraidedFusionCategory.{v,u})
    (p : PivotalStructure (C := C.Obj)) (d : Fin (Ground.rank C) → ℝ)
    (hreal : ∀ i, pivotalDimension C p (Ground.simples C i) = (d i : ℂ)) (i : Fin (Ground.rank C)) :
    pivotalDimension C p (Ground.simples C (Ground.dualIndex C i)) =
      pivotalDimension C p (Ground.simples C i) := by
  have h := galois_pivotalDimension_dual_eq_conj C p (RingEquiv.refl ℂ) i
  change pivotalDimension C p (Ground.simples C (Ground.dualIndex C i)) =
    star (pivotalDimension C p (Ground.simples C i)) at h
  simpa [hreal] using h

end PropertyF.Ground.Dimensions
