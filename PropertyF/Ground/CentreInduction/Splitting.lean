module
public import PropertyF.Ground.CentreInduction.Averaging
public import PropertyF.Ground.CentreInduction.SimpleDetection
public import PropertyF.Ground.Fusion.SemisimpleSplit
public import PropertyF.Ground.Centre.Abelian

/-! The Maschke consequence of the remaining loop-sliding identity. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.CentreInduction
universe v u

/-- The specific, as-yet-unproved sliding identity needed for averaging. It is
stated only against the finite family of simple representatives. -/
def SimpleLoopCentrality (C : BraidedFusionCategory.{v,u})
    (p : Dimensions.PivotalStructure (C := C.Obj)) : Prop :=
  ∀ (X Y : CategoryTheory.Center C.Obj) (f : X.1 ⟶ Y.1) i,
    (loopSum C p X Y f ▷ simples C i) ≫ (Y.2.β (simples C i)).hom =
      (X.2.β (simples C i)).hom ≫ (simples C i ◁ loopSum C p X Y f)

/-- Assuming the loop-sliding identity, normalized averaging produces an
actual centre map from any underlying map. -/
def average (C : BraidedFusionCategory.{v,u})
    (p : Dimensions.PivotalStructure (C := C.Obj)) (hslide : SimpleLoopCentrality C p)
    (X Y : CategoryTheory.Center C.Obj) (f : X.1 ⟶ Y.1) : X ⟶ Y where
  f := (globalDimension C)⁻¹ • loopSum C p X Y f
  comm U := by
    simp only [MonoidalLinear.smul_whiskerRight, Linear.smul_comp,
      MonoidalLinear.whiskerLeft_smul, Linear.comp_smul]
    rw [comm_of_simples C X Y (loopSum C p X Y f) (hslide X Y f) U]





end PropertyF.Ground.CentreInduction
