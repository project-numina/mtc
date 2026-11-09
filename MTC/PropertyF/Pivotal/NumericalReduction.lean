module
public import MTC.PropertyF.Pivotal.Nondegeneracy
public import MTC.PropertyF.Pivotal.GaloisDimensionTransport

/-! # Reduction of the nondegenerate theorem to numerical centrality

The numerical-to-actual transparency implication is an explicit categorical
premise below; the implication is established in `NondegeneracyRelative`.
-/

@[expose] public noncomputable section
open CategoryTheory MTC.Fusion MTC.Modular MTC.Braided MTC.CategoryTheory.Dimensions
namespace MTC.PropertyF.Pivotal
universe v u
variable (C : BraidedFusionCategory.{v,u}) (p : PivotalStructure (C := C.Obj))

/-- Actual nondegeneracy implies S invertibility once the stated numerical
test for transparent simples is established. -/
theorem categoricalS_invertible_of_nondegenerate_of_numerical_transparency
    (hnondeg : IsNondegenerate C)
    (hcriterion : ∀ k, (∀ i, categoricalS C p i k =
      simpleDimension C p i * simpleDimension C p k) →
      MTC.Center.Transparent (simples C k)) :
    (categoricalS C p).det ≠ 0 :=
  categoricalS_det_ne_zero_of_trivial_S_centralizer C p fun k hk =>
    hnondeg k (hcriterion k hk)

/-- The full nondegenerate conclusion follows from property F and the
explicit numerical-to-actual transparency criterion. -/
theorem main_of_nondegenerate_of_numerical_transparency
    (hnondeg : IsNondegenerate C)
    (hcriterion : ∀ k, (∀ i, categoricalS C p i k =
      simpleDimension C p i * simpleDimension C p k) →
      MTC.Center.Transparent (simples C k))
    (hF : HasPropertyF C.Obj) :
    PseudoUnitary C ∧ AllGaloisConjugatesPseudoUnitary C ∧
      WeaklyIntegral (globalFPDimension C) :=
  main_of_invertibleS_of_propertyF C p
    (categoricalS_invertible_of_nondegenerate_of_numerical_transparency C p hnondeg hcriterion) hF

end MTC.PropertyF.Pivotal
end
