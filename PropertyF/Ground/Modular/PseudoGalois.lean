module
public import PropertyF.Ground.Modular.GaloisFromVerlinde
public import PropertyF.Ground.Fusion.SpectralIntegral
public import PropertyF.Ground.Modular.UnitDimension

/-! The pseudo-unitary case of categorical Galois symmetry. -/
open scoped BigOperators
open PropertyF.Ground.Dimensions
@[expose] public noncomputable section
namespace PropertyF.Ground.Modular

/-- S-square and Verlinde produce the Galois action in a pseudo-unitary category. -/
theorem categoricalS_galois_action_pseudoUnitary (C : Ground.BraidedFusionCategory)
    (h : Ground.PseudoUnitary C) (p : PivotalStructure (C := C.Obj))
    (hsq : ∀ x y, ∑ z, categoricalS C p x z * categoricalS C p z y =
      if x = Ground.dualIndex C y then globalDimension C else 0)
    (hVerlinde : ∀ i j y,
      (categoricalS C p i y / simpleDimension C p y) *
        (categoricalS C p j y / simpleDimension C p y) =
      ∑ k, (fusionCoeff C i j k : ℂ) * (categoricalS C p k y / simpleDimension C p y)) :
    ∃ act : (ℂ ≃+* ℂ) →* Equiv.Perm (Fin (rank C)), ∀ (σ : ℂ ≃+* ℂ) i j,
      σ (categoricalS C p i j / simpleDimension C p j) =
        categoricalS C p i (act σ j) / simpleDimension C p (act σ j) :=
  categoricalS_galois_action C p (Ground.dualIndex C) (Ground.globalDimension_ne_zero_of_pseudoUnitary C h) hsq hVerlinde

/-- Proposition 2.1 specialized to actual spherical S-matrices; the unit
S-square identity remains an explicit categorical obligation. -/
theorem categoricalS_galois_unit_properties (C : Ground.BraidedFusionCategory)
    (h : Ground.PseudoUnitary C) (p : PivotalStructure (C := C.Obj)) (hp : p.IsSpherical)
    (hsq : ∀ x y, ∑ z, categoricalS C p x z * categoricalS C p z y =
      if x = Ground.dualIndex C y then globalDimension C else 0)
    (σ : ℂ ≃+* ℂ) (y : Fin (rank C))
    (hchar : ∀ x, σ (categoricalS C p x (unitIndex C) /
      simpleDimension C p (unitIndex C)) = categoricalS C p x y / simpleDimension C p y) :
    (∀ x, categoricalS C p x y = simpleDimension C p y * σ (simpleDimension C p x)) ∧
      y = Ground.dualIndex C y ∧
      σ (globalDimension C) = globalDimension C / simpleDimension C p y ^ 2 :=
  galois_unit_properties (unitIndex C) (categoricalS C p) (Ground.dualIndex C)
    (simpleDimension C p) (globalDimension C) (simpleDimension_ne_zero C p)
    (Ground.globalDimension_ne_zero_of_pseudoUnitary C h) (simpleDimension_unit C p)
    (categorical_global_eq_sum_squares C p hp) (categoricalS_symmetric C p)
    (categoricalS_unit C p) hsq σ y hchar
end PropertyF.Ground.Modular
