module
public import MTC.Center.Helpers
public import MTC.Modular.SMatrix
public import MTC.Center.Normalization.AdjointDegrees

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

/-- Positivity of pivotal dimensions on transparent simple adjoint labels.
The adjoint labels are defined by the fusion closure of constituents of
`X ⊗ X*`; identifying this presentation with a bundled categorical adjoint
subcategory is a separate obligation. -/
def PositiveOnTransparentAdjoint (C : BraidedFusionCategory.{v,u})
    (p : PivotalStructure (C := C.Obj)) : Prop :=
  ∀ i, MTC.Center.Transparent (simples C i) →
    MTC.Center.Normalization.IsAdjointLabel C i →
    ∃ r : ℝ, 0 < r ∧ MTC.Modular.simpleDimension C p i = (r : ℂ)

/-- The normalization lemma, stated as an unproved target. -/
def NormalizationStatement : Prop :=
  ∀ (C : BraidedFusionCategory.{v,u}) (p : PivotalStructure (C := C.Obj)),
    PositiveOnTransparentAdjoint C p →
      ∃ q : PivotalStructure (C := C.Obj), ∀ i,
        MTC.Center.Transparent (simples C i) →
          MTC.Modular.simpleDimension C q i = (fpSimple C i : ℂ)

/-- The degenerate pivotal theorem, stated as an unproved target. -/
def DegenerateMainStatement : Prop :=
  ∀ (C : BraidedFusionCategory.{v,u}) (p : PivotalStructure (C := C.Obj)),
    PositiveOnTransparentAdjoint C p → HasPropertyF C.Obj →
      PseudoUnitary C ∧ AllGaloisConjugatesPseudoUnitary C ∧
        WeaklyIntegral (globalFPDimension C)

/-- The pseudo-unitary-conjugate corollary's full conclusion, stated as an
unproved target; the existing theorem covers its weak-integrality component. -/
def PseudoUnitaryConjugateStatement : Prop :=
  ∀ C : BraidedFusionCategory.{v,u},
    HasPseudoUnitaryGaloisConjugate C → HasPropertyF C.Obj →
      PseudoUnitary C ∧ WeaklyIntegral (globalFPDimension C)

/-- Property F is preserved by the generated tensor closure, stated as an
unproved target in terms of actual generated objects and braid images. -/
def ClosureStatement : Prop :=
  ∀ (C : BraidedFusionCategory.{v,u}) (X Y : C.Obj),
    ObjectPropertyF X → GeneratedBy X Y → ObjectPropertyF Y

end MTC.PropertyF.Pivotal
