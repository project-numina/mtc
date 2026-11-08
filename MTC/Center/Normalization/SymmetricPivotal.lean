module
public import MTC.Center.Normalization.MugerCategory
public import MTC.Center.Induction.DrinfeldTheorem

open MTC.Fusion MTC.Braided MTC.CategoryTheory.Dimensions

/-! # The canonical pivotal structure of a symmetric category

The Drinfeld isomorphism is monoidal when the braiding is symmetric. Sphericality
and integer dimensions of this pivotal structure are separate obligations.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace MTC.Center.Normalization
universe v u
variable {D : Type u} [Category.{v} D] [MonoidalCategory D]
  [SymmetricCategory D] [RightRigidCategory D]

/-- The Drinfeld isomorphism gives a pivotal structure in every symmetric
right-rigid monoidal category. -/
def canonicalSymmetricPivotal : PivotalStructure (C := D) where
  iso X := drinfeldIso X
  naturality f := drinfeldIso_natural f
  tensor X Y := by
    have h := (MTC.Center.Induction.drinfeld_tensor X Y).w
    simpa [MTC.Modular.doubleBraiding, SymmetricCategory.symmetry] using h
  unit := drinfeld_unit

/-- The actual symmetric Müger fusion category has its canonical Drinfeld
pivotal structure. -/
def mugerCanonicalPivotal (C : BraidedFusionCategory.{v,u}) :
    PivotalStructure (C := MugerCategory C) := canonicalSymmetricPivotal

end MTC.Center.Normalization
end
