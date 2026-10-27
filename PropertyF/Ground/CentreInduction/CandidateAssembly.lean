module
public import PropertyF.Ground.CentreInduction.CrossingCoherence
public import PropertyF.Ground.CentreInduction.AdjunctionAssembly

/-! Assembly of the centre induction data from the explicit matrix crossing. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.CentreInduction
universe v u

/-- The actual matrix crossing is invertible by rigidity. -/
theorem crossingCandidate_isIso (C : BraidedFusionCategory.{v,u}) (X T : C.Obj) :
    IsIso (crossingCandidate C X T) :=
  weak_isIso (underlying C X) (crossingCandidate C X)
    (fun f => crossingCandidate_natural_test C X f)
    (fun T U => crossingCandidate_tensor C X T U)
    (crossingCandidate_unit C X) T (ᘁT)

/-- The explicit matrix crossings form an actual half-braiding on the
induction sum, with no additional coherence assumptions. -/
def halfBraidingOfCrossingCandidate (C : BraidedFusionCategory.{v,u}) (X : C.Obj) :
    HalfBraiding (underlying C X) where
  β T := by letI := crossingCandidate_isIso C X T; exact asIso (crossingCandidate C X T)
  monoidal T U := crossingCandidate_tensor C X T U
  naturality f := crossingCandidate_natural_test C X f

/-- The proposed half-braiding is automatically natural in its induction
argument: this coherence was proved directly for the matrix crossing. -/
theorem halfBraidingOfCrossingCandidate_natural (C : BraidedFusionCategory.{v,u})
    {X Y : C.Obj} (f : X ⟶ Y) (T : C.Obj) :
    ((underlyingFunctor C).map f ▷ T) ≫
        ((halfBraidingOfCrossingCandidate C Y).β T).hom =
      ((halfBraidingOfCrossingCandidate C X).β T).hom ≫
        (T ◁ (underlyingFunctor C).map f) :=
  crossingCandidate_natural_middle C f T

/-- The actual induction functor to Mathlib's Drinfeld centre. -/
def induction (C : BraidedFusionCategory.{v,u}) : C.Obj ⥤ CategoryTheory.Center C.Obj :=
  inductionOfHalfBraiding C (halfBraidingOfCrossingCandidate C)
    (halfBraidingOfCrossingCandidate_natural C)

/-- Forgetting induction gives the finite sum of `Sᵢ ⊗ X ⊗ Sᵢ*`. -/
theorem induction_forget_obj (C : BraidedFusionCategory.{v,u}) (X : C.Obj) :
    ((induction C).obj X).1 = underlying C X := rfl

end PropertyF.Ground.CentreInduction
