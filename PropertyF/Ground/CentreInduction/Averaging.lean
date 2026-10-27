module
public import PropertyF.Ground.CentreInduction.PartialTrace
public import PropertyF.Ground.Centre.Linear
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

/-- A genuine centre morphism is unchanged by the winding operation. -/
theorem winding_center_hom (C : BraidedFusionCategory.{v,u})
    {X Y : CategoryTheory.Center C.Obj} (f : X ⟶ Y) (T : C.Obj) :
    winding C X Y T f.f = f.f ▷ T := by
  unfold winding
  rw [← f.comm_assoc T]
  simp

/-- The unnormalized Kirby-colour loop sum. Its centrality on arbitrary
underlying maps is a separate, unproved coherence obligation. -/
def loopSum (C : BraidedFusionCategory.{v,u})
    (p : Dimensions.PivotalStructure (C := C.Obj))
    (X Y : CategoryTheory.Center C.Obj) (f : X.1 ⟶ Y.1) : X.1 ⟶ Y.1 :=
  ∑ i, Modular.simpleDimension C p i •
    partialTraceHom p X.1 Y.1 (simples C i) (winding C X Y (simples C i) f)

/-- Each loop around a centre morphism scales it by the dimension of the
closed strand. -/
theorem trace_winding_center_hom (C : BraidedFusionCategory.{v,u})
    (p : Dimensions.PivotalStructure (C := C.Obj))
    {X Y : CategoryTheory.Center C.Obj} (f : X ⟶ Y) (i : Fin (rank C)) :
    partialTraceHom p X.1 Y.1 (simples C i) (winding C X Y (simples C i) f.f) =
      Modular.simpleDimension C p i • f.f := by
  rw [winding_center_hom, partialTraceHom_whisker]
  have hs : p.rightTrace (𝟙 (simples C i)) =
      Modular.simpleDimension C p i • (1 : End (𝟙_ C.Obj)) := by
    apply (unitScalarEquiv C).injective
    simp [Modular.simpleDimension]
  have hs' := congrArg End.asHom hs
  simp only [End.smul_asHom, End.one_asHom] at hs'
  rw [hs']
  simp


end PropertyF.Ground.CentreInduction

namespace PropertyF.Ground.CentreInduction
universe v u
set_option backward.isDefEq.respectTransparency false in
/-- Winding commutes with a central map on the source side. -/
theorem winding_precompose (C : BraidedFusionCategory.{v,u})
    {W X Y : CategoryTheory.Center C.Obj} (f : W ⟶ X) (g : X.1 ⟶ Y.1)
    (T : C.Obj) :
    winding C W Y T (f.f ≫ g) = (f.f ▷ T) ≫ winding C X Y T g := by
  simp only [winding, MonoidalCategory.whiskerLeft_comp, Category.assoc, ← f.comm_assoc]




end PropertyF.Ground.CentreInduction
