module
public import MTC.PropertyF.Pivotal.NondegeneracyHaarBasis

open MTC.Fusion MTC.Modular MTC.CategoryTheory.Dimensions MTC.Center.Induction MTC.Center.Trace
open scoped BigOperators

/-! Pivotal Frobenius mates for the Haar fusion-basis contraction. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
namespace MTC.PropertyF.Pivotal
universe v u
variable (C : BraidedFusionCategory.{v,u}) (p : PivotalStructure (C := C.Obj))

/-- Pivotality turns the chosen right dual into a left dual, with its actual
coevaluation and evaluation transported along the pivotal isomorphism. -/
@[instance_reducible] def pivotalLeftPairing (X : C.Obj) : ExactPairing (Xᘁ) X :=
  exactPairingCongrRight (p.iso X)

/-- The first Frobenius mate in the DGNO C.1 basis calculation. -/
def haarInclusionMate (X Y U : C.Obj) :
    (X ⟶ Y ⊗ U) ≃ₗ[ℂ] ((Yᘁ) ⟶ U ⊗ (Xᘁ)) :=
  (tensorLeftHomLinearEquiv (k := ℂ) X Y (Yᘁ) U).symm.trans
    (tensorRightHomLinearEquiv (k := ℂ) (Yᘁ) X (Xᘁ) U)

/-- The second Frobenius mate uses the actual pivotal left duals. -/
def haarProjectionMate (X Y U : C.Obj) :
    (Y ⊗ U ⟶ X) ≃ₗ[ℂ] (U ⊗ (Xᘁ) ⟶ (Yᘁ)) :=
  letI : ExactPairing (Yᘁ) Y := pivotalLeftPairing C p Y
  letI : ExactPairing (Xᘁ) X := pivotalLeftPairing C p X
  (tensorLeftHomLinearEquiv (k := ℂ) U (Yᘁ) Y X).trans
    (tensorRightHomLinearEquiv (k := ℂ) U (Xᘁ) X (Yᘁ)).symm

/-- The pivotal left coevaluation is the usual right coevaluation transported
by the inverse pivotal component. -/
theorem pivotalLeftPairing_coevaluation (X : C.Obj) :
    @ExactPairing.coevaluation C.Obj _ _ (Xᘁ) X (pivotalLeftPairing C p X) =
      η_ (Xᘁ) ((Xᘁ)ᘁ) ≫ (Xᘁ) ◁ (p.iso X).inv := rfl

/-- The pivotal left evaluation is the usual right evaluation transported
by the pivotal component. -/
theorem pivotalLeftPairing_evaluation (X : C.Obj) :
    @ExactPairing.evaluation C.Obj _ _ (Xᘁ) X (pivotalLeftPairing C p X) =
      (p.iso X).hom ▷ (Xᘁ) ≫ ε_ (Xᘁ) ((Xᘁ)ᘁ) := rfl

/-- The two mate maps are actual linear equivalences, so they transport every
chosen fusion basis to a basis of the corresponding dual Hom space. -/
def haarMatedInclusionBasis (X Y U : C.Obj) {I : Type*}
    (b : Module.Basis I ℂ (X ⟶ Y ⊗ U)) :
    Module.Basis I ℂ ((Yᘁ) ⟶ U ⊗ (Xᘁ)) :=
  b.map (haarInclusionMate C X Y U)

/-- The pivotal projection mates likewise transport bases without any
positivity or sphericality assumption. -/
def haarMatedProjectionBasis (X Y U : C.Obj) {I : Type*}
    (b : Module.Basis I ℂ (Y ⊗ U ⟶ X)) :
    Module.Basis I ℂ (U ⊗ (Xᘁ) ⟶ (Yᘁ)) :=
  b.map (haarProjectionMate C p X Y U)

end MTC.PropertyF.Pivotal
end
