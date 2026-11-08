module
public import MTC.Center.Helpers
public import MTC.Modular.SMatrix

/-!
# Targets for the pivotal Property F manuscript

These are statements, not asserted proofs. The frozen original property-F
statement is left unchanged.
-/

@[expose] public noncomputable section
open MTC.Fusion MTC.Braided MTC.CategoryTheory.Dimensions
namespace MTC.PropertyF.Pivotal
universe v u

/-- A braided fusion category is nondegenerate if its only transparent
simple representative is the tensor unit. -/
def IsNondegenerate (C : BraidedFusionCategory.{v,u}) : Prop :=
  ∀ i, MTC.Center.Transparent (simples C i) → i = unitIndex C

/-- Every represented semilinear braided Galois conjugate is pseudo-unitary. -/
def AllGaloisConjugatesPseudoUnitary (C : BraidedFusionCategory.{v,u}) : Prop :=
  ∀ (D : BraidedFusionCategory.{v,u}) (σ : ℂ ≃+* ℂ),
    Nonempty (GaloisConjugate C D σ) → PseudoUnitary D

/-- The main theorem's nondegenerate pivotal statement. This definition does
not assert that the statement has been proved. -/
def NondegenerateMainStatement : Prop :=
  ∀ C : BraidedFusionCategory.{v,u},
    Nonempty (PivotalStructure (C := C.Obj)) → IsNondegenerate C → HasPropertyF C.Obj →
      PseudoUnitary C ∧ AllGaloisConjugatesPseudoUnitary C ∧
        WeaklyIntegral (globalFPDimension C)

end MTC.PropertyF.Pivotal
