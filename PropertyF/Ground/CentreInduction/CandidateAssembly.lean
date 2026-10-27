module
public import PropertyF.Ground.CentreInduction.CrossingNaturality
public import PropertyF.Ground.CentreInduction.AdjunctionAssembly

/-! Assembly of the centre induction data from the explicit matrix crossing. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.CentreInduction
universe v u

/-- If the matrix crossings are isomorphisms and obey the half-braiding
tensor law, they form the desired half-braiding; naturality is proved.
Invertibility and the tensor law are currently unproved. -/
def halfBraidingOfCrossingCandidate (C : BraidedFusionCategory.{v,u})
    (hinv : ∀ X T : C.Obj, IsIso (crossingCandidate C X T))
    (htensor : ∀ (X T U : C.Obj), crossingCandidate C X (T ⊗ U) =
      (α_ _ _ _).inv ≫ (crossingCandidate C X T ▷ U) ≫ (α_ _ _ _).hom ≫
        (T ◁ crossingCandidate C X U) ≫ (α_ _ _ _).inv) (X : C.Obj) :
    HalfBraiding (underlying C X) where
  β T := by letI := hinv X T; exact asIso (crossingCandidate C X T)
  monoidal T U := htensor X T U
  naturality f := crossingCandidate_natural_test C X f

/-- The proposed half-braiding is automatically natural in its induction
argument: this coherence was proved directly for the matrix crossing. -/
theorem halfBraidingOfCrossingCandidate_natural (C : BraidedFusionCategory.{v,u})
    (hinv : ∀ X T : C.Obj, IsIso (crossingCandidate C X T))
    (htensor : ∀ (X T U : C.Obj), crossingCandidate C X (T ⊗ U) =
      (α_ _ _ _).inv ≫ (crossingCandidate C X T ▷ U) ≫ (α_ _ _ _).hom ≫
        (T ◁ crossingCandidate C X U) ≫ (α_ _ _ _).inv)
    {X Y : C.Obj} (f : X ⟶ Y) (T : C.Obj) :
    ((underlyingFunctor C).map f ▷ T) ≫
        ((halfBraidingOfCrossingCandidate C hinv htensor Y).β T).hom =
      ((halfBraidingOfCrossingCandidate C hinv htensor X).β T).hom ≫
        (T ◁ (underlyingFunctor C).map f) :=
  crossingCandidate_natural_middle C f T

end PropertyF.Ground.CentreInduction
