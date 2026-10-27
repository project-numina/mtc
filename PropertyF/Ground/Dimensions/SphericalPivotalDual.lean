module
public import PropertyF.Ground.Dimensions.PositivePivotalDual
public import PropertyF.Ground.Dimensions.SignCharacter

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.Dimensions
universe v u
/-- Real spherical simple dimensions force pivotal dual coherence on all objects. -/
theorem real_spherical_pivotal_dual (C : Ground.BraidedFusionCategory.{v,u})
    (p : PivotalStructure (C := C.Obj)) (hp : p.IsSpherical)
    (d : Fin (Ground.rank C) → ℝ)
    (hreal : ∀ i, pivotalDimension C p (Ground.simples C i) = (d i : ℂ))
    (X : C.Obj) : p.iso (Xᘁ) = (rightDualIsoMap (p.iso X)).symm := by
  apply pivotal_dual_of_simple_dual C p _ X
  intro i
  apply spherical_pivotal_dual_simple_of_dimension C p hp i
  have h := galois_pivotalDimension_dual_eq_conj C p (RingEquiv.refl ℂ) i
  change pivotalDimension C p (Ground.simples C (Ground.dualIndex C i)) =
    star (pivotalDimension C p (Ground.simples C i)) at h
  simpa [hreal] using h

/-- Every spherical structure on a pseudo-unitary category is dual-coherent. -/
theorem pseudoUnitary_spherical_pivotal_dual (C : Ground.BraidedFusionCategory.{v,u})
    (p : PivotalStructure (C := C.Obj)) (hp : p.IsSpherical)
    (hpu : Ground.PseudoUnitary C) (X : C.Obj) :
    p.iso (Xᘁ) = (rightDualIsoMap (p.iso X)).symm := by
  apply real_spherical_pivotal_dual C p hp
    (fun i => (pivotalDimension C p (Ground.simples C i)).re) _ X
  intro i
  exact (spherical_dimensions_real_of_pseudoUnitary C p hp hpu i).symm
end PropertyF.Ground.Dimensions
