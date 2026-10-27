module
public import PropertyF.Ground.CentreInduction.CrossingUnit
public import PropertyF.Ground.CentreInduction.AdjunctionAssembly

/-! Assembly of the centre induction data from the explicit matrix crossing. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.CentreInduction
universe v u

/-- The matrix crossings form a half-braiding once the tensor law on triples
of simples is proved. That finite check remains open; unit normalization,
rigidity-based invertibility and naturality are proved. -/
def halfBraidingOfCrossingCandidate (C : BraidedFusionCategory.{v,u})
    (htensor : ∀ i j k, crossingCandidate C (simples C i) (simples C j ⊗ simples C k) =
      crossingTensorComposite C (simples C i) (simples C j) (simples C k)) (X : C.Obj) :
    HalfBraiding (underlying C X) where
  β T := by letI := crossing_isIso_of_unit_tensor C (fun i => crossingCandidate_unit C (simples C i)) htensor X T; exact asIso (crossingCandidate C X T)
  monoidal T U := crossingCandidate_tensor_of_all_simples C htensor X T U
  naturality f := crossingCandidate_natural_test C X f

/-- The proposed half-braiding is automatically natural in its induction
argument: this coherence was proved directly for the matrix crossing. -/
theorem halfBraidingOfCrossingCandidate_natural (C : BraidedFusionCategory.{v,u})
    (htensor : ∀ i j k, crossingCandidate C (simples C i) (simples C j ⊗ simples C k) =
      crossingTensorComposite C (simples C i) (simples C j) (simples C k))
    {X Y : C.Obj} (f : X ⟶ Y) (T : C.Obj) :
    ((underlyingFunctor C).map f ▷ T) ≫
        ((halfBraidingOfCrossingCandidate C htensor Y).β T).hom =
      ((halfBraidingOfCrossingCandidate C htensor X).β T).hom ≫
        (T ◁ (underlyingFunctor C).map f) :=
  crossingCandidate_natural_middle C f T

end PropertyF.Ground.CentreInduction
