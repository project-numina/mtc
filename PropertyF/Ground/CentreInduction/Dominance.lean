module
public import PropertyF.Ground.CentreInduction.Splitting
public import Mathlib.CategoryTheory.Adjunction.FullyFaithful

/-! Dominance of a right adjoint from the Maschke splitting. -/

@[expose] public noncomputable section
open CategoryTheory
namespace PropertyF.Ground.CentreInduction
universe v u

set_option backward.isDefEq.respectTransparency false in
/-- Given the centre-forgetful right adjoint, the averaging sliding identity
splits the adjunction unit, making every centre object a retract of the
induced underlying object. Neither the adjoint nor the sliding identity is
constructed by this theorem. -/
def retract_of_adjunction_and_loop (C : BraidedFusionCategory.{v,u})
    (p : Dimensions.PivotalStructure (C := C.Obj)) (hp : p.IsSpherical)
    (hslide : SimpleLoopCentrality C p) (hne : globalDimension C ≠ 0)
    (I : C.Obj ⥤ CategoryTheory.Center C.Obj)
    (adj : CategoryTheory.Center.forget C.Obj ⊣ I) (X : CategoryTheory.Center C.Obj) :
    Retract X (I.obj X.1) := by
  letI : Mono (adj.unit.app X) := adj.unit_mono_of_L_faithful X
  letI : IsSplitMono (adj.unit.app X) :=
    mono_splits_of_loop_centrality C p hp hslide hne (adj.unit.app X)
  exact { i := adj.unit.app X, r := retraction (adj.unit.app X) }

end PropertyF.Ground.CentreInduction
