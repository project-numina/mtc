module
public import MTC.PropertyF.Pivotal.GaloisUnitScalar
public import Mathlib.CategoryTheory.Monoidal.Rigid.OfEquivalence

/-! # Dual objects under monoidal equivalence -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace MTC.PropertyF.Pivotal
universe v u v' u'
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
variable {D : Type u'} [Category.{v'} D] [MonoidalCategory D] [RightRigidCategory D]

/-- A monoidal equivalence carries an exact pairing to an exact pairing on
its actual images. -/
@[instance_reducible] def exactPairingOfMonoidalEquivalence (e : C ≌ D) [e.functor.Monoidal]
    (X Y : C) [ExactPairing X Y] : ExactPairing (e.functor.obj X) (e.functor.obj Y) := by
  letI : e.inverse.Monoidal := e.inverseMonoidal
  let ex : e.inverse.obj (e.functor.obj X) ≅ X := (e.unitIso.app X).symm
  let ey : e.inverse.obj (e.functor.obj Y) ≅ Y := (e.unitIso.app Y).symm
  letI : ExactPairing (e.inverse.obj (e.functor.obj X)) Y :=
    exactPairingCongrLeft ex
  letI : ExactPairing (e.inverse.obj (e.functor.obj X))
      (e.inverse.obj (e.functor.obj Y)) := exactPairingCongrRight ey
  exact ExactPairing.ofFullyFaithful e.inverse (e.functor.obj X) (e.functor.obj Y)

/-- The image of the chosen right dual is isomorphic to the chosen right
  dual of the image. -/
def rightDualOfMonoidalEquivalence (e : C ≌ D) [e.functor.Monoidal] (X : C) :
    e.functor.obj (Xᘁ) ≅ (e.functor.obj X)ᘁ := by
  letI := exactPairingOfMonoidalEquivalence e X (Xᘁ)
  exact rightDualIso (exactPairingOfMonoidalEquivalence e X (Xᘁ)) HasRightDual.exact

end MTC.PropertyF.Pivotal
end
