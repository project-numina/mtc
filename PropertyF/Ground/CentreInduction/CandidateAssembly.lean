module
public import PropertyF.Ground.CentreInduction.TensorDetection
public import PropertyF.Ground.CentreInduction.AdjunctionAssembly

/-! Assembly of the centre induction data from the explicit matrix crossing. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.CentreInduction
universe v u

/-- The matrix crossings form a half-braiding once invertibility on pairs of
simples and the tensor law on triples of simples are proved. Both finite
checks remain open; naturality and extension to all objects are proved. -/
def halfBraidingOfCrossingCandidate (C : BraidedFusionCategory.{v,u})
    (hinv : ∀ i j, IsIso (crossingCandidate C (simples C i) (simples C j)))
    (htensor : ∀ i j k, crossingCandidate C (simples C i) (simples C j ⊗ simples C k) =
      crossingTensorComposite C (simples C i) (simples C j) (simples C k)) (X : C.Obj) :
    HalfBraiding (underlying C X) where
  β T := by letI := crossingCandidate_isIso_of_simples C hinv X T; exact asIso (crossingCandidate C X T)
  monoidal T U := crossingCandidate_tensor_of_all_simples C htensor X T U
  naturality f := crossingCandidate_natural_test C X f

/-- The proposed half-braiding is automatically natural in its induction
argument: this coherence was proved directly for the matrix crossing. -/
theorem halfBraidingOfCrossingCandidate_natural (C : BraidedFusionCategory.{v,u})
    (hinv : ∀ i j, IsIso (crossingCandidate C (simples C i) (simples C j)))
    (htensor : ∀ i j k, crossingCandidate C (simples C i) (simples C j ⊗ simples C k) =
      crossingTensorComposite C (simples C i) (simples C j) (simples C k))
    {X Y : C.Obj} (f : X ⟶ Y) (T : C.Obj) :
    ((underlyingFunctor C).map f ▷ T) ≫
        ((halfBraidingOfCrossingCandidate C hinv htensor Y).β T).hom =
      ((halfBraidingOfCrossingCandidate C hinv htensor X).β T).hom ≫
        (T ◁ (underlyingFunctor C).map f) :=
  crossingCandidate_natural_middle C f T

end PropertyF.Ground.CentreInduction
