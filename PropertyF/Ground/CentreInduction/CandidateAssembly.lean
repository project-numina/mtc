module
public import PropertyF.Ground.CentreInduction.CrossingCoherence
public import PropertyF.Ground.CentreInduction.AdjunctionAssembly

/-! Assembly of the centre induction data from the explicit matrix crossing. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.CentreInduction
universe v u
variable (C : BraidedFusionCategory.{v,u})

/-- The actual matrix crossing is invertible by rigidity. -/
theorem crossingCandidate_isIso (X T : C.Obj) :
    IsIso (crossingCandidate C X T) :=
  weak_isIso (underlying C X) (crossingCandidate C X)
    (fun f => crossingCandidate_natural_test C X f)
    (fun T U => crossingCandidate_tensor C X T U)
    (crossingCandidate_unit C X) T (ᘁT)

/-- The explicit matrix crossings form an actual half-braiding on the
induction sum, with no additional coherence assumptions. -/
def halfBraidingOfCrossingCandidate (X : C.Obj) :
    HalfBraiding (underlying C X) where
  β T := by letI := crossingCandidate_isIso C X T; exact asIso (crossingCandidate C X T)
  monoidal T U := crossingCandidate_tensor C X T U
  naturality f := crossingCandidate_natural_test C X f

/-- The actual induction functor to Mathlib's Drinfeld centre. -/
def induction : C.Obj ⥤ CategoryTheory.Center C.Obj where
  obj X := ⟨underlying C X, halfBraidingOfCrossingCandidate C X⟩
  map f := ⟨(underlyingFunctor C).map f, crossingCandidate_natural_middle C f⟩
  map_id X := by
    apply CategoryTheory.Center.ext
    change (underlyingFunctor C).map (𝟙 X) = 𝟙 ((underlyingFunctor C).obj X)
    exact (underlyingFunctor C).map_id X
  map_comp f g := by
    apply CategoryTheory.Center.ext
    change (underlyingFunctor C).map (f ≫ g) =
      (underlyingFunctor C).map f ≫ (underlyingFunctor C).map g
    exact (underlyingFunctor C).map_comp f g


end PropertyF.Ground.CentreInduction
