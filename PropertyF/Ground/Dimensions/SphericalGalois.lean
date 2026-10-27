module
public import PropertyF.Ground.Dimensions.SignCharacter
public import PropertyF.Ground.Dimensions.CharacterDual

@[expose] public noncomputable section
open CategoryTheory
namespace PropertyF.Ground.Dimensions
universe v u

/-- In a pseudo-unitary category, dimensions for any spherical structure are
invariant under duality. -/
theorem pseudoUnitary_spherical_dimension_dual
    (C : Ground.BraidedFusionCategory.{v,u})
    (p : PivotalStructure (C := C.Obj)) (hp : p.IsSpherical)
    (hpu : Ground.PseudoUnitary C) (i : Fin (Ground.rank C)) :
    pivotalDimension C p (Ground.simples C (Ground.dualIndex C i)) =
      pivotalDimension C p (Ground.simples C i) := by
  rw [pivotalDimension_dual_eq_conj]
  exact Complex.conj_eq_iff_re.mpr (spherical_dimensions_real_of_pseudoUnitary C p hp hpu i)

/-- Every Galois conjugate of each simple dimension of any spherical structure
on a pseudo-unitary category is real. -/
theorem pseudoUnitary_spherical_dimension_galois_real
    (C : Ground.BraidedFusionCategory.{v,u})
    (p : PivotalStructure (C := C.Obj)) (hp : p.IsSpherical)
    (hpu : Ground.PseudoUnitary C) (σ : ℂ ≃+* ℂ) (i : Fin (Ground.rank C)) :
    ((σ (pivotalDimension C p (Ground.simples C i))).re : ℂ) =
      σ (pivotalDimension C p (Ground.simples C i)) :=
  galois_pivotalDimension_real_of_dual C p
    (pseudoUnitary_spherical_dimension_dual C p hp hpu) σ i

end PropertyF.Ground.Dimensions
