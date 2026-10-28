module
public import PropertyF.Ground.CentreInduction.PartialTrace
public import PropertyF.Ground.Centre.Basic
public import PropertyF.Ground.Modular.SMatrix

/-! The spherical loop average on underlying maps of centre objects. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
open scoped BigOperators
namespace PropertyF.Ground.CentreInduction
universe v u

/-- Wind a strand around an underlying map using the two half-braidings. -/
def winding (C : BraidedFusionCategory.{v,u}) (X Y : CategoryTheory.Center C.Obj)
    (T : C.Obj) (f : X.1 ⟶ Y.1) : X.1 ⊗ T ⟶ Y.1 ⊗ T :=
  (X.2.β T).hom ≫ (T ◁ f) ≫ (Y.2.β T).inv


/-- The unnormalized Kirby-colour loop sum. Its centrality on arbitrary
underlying maps is a separate, unproved coherence obligation. -/
def loopSum (C : BraidedFusionCategory.{v,u})
    (p : Dimensions.PivotalStructure (C := C.Obj))
    (X Y : CategoryTheory.Center C.Obj) (f : X.1 ⟶ Y.1) : X.1 ⟶ Y.1 :=
  ∑ i, Modular.simpleDimension C p i •
    partialTraceHom p X.1 Y.1 (simples C i) (winding C X Y (simples C i) f)



end PropertyF.Ground.CentreInduction

namespace PropertyF.Ground.CentreInduction
universe v u




end PropertyF.Ground.CentreInduction
