module
public import MTC.PropertyF.Statement

/-!
# Braided tensor equivalence

This is a complex-linear braided monoidal equivalence of the underlying
braided fusion categories. It does not assert that an independently selected
pivotal or ribbon structure is preserved. Therefore it is coarser than the
usual equivalence of modular categories with specified ribbon structure.
-/

@[expose] public noncomputable section
open CategoryTheory

namespace MTC
universe v u

/-- Complex-linear braided monoidal equivalence of braided fusion categories. -/
structure BraidedTensorEquivalence (C D : PropertyF.Ground.BraidedFusionCategory.{v,u}) where
  equivalence : C.Obj ≌ D.Obj
  [monoidal : equivalence.functor.Monoidal]
  [braided : equivalence.functor.Braided]
  map_smul : ∀ {X Y : C.Obj} (z : ℂ) (f : X ⟶ Y),
    equivalence.functor.map (z • f) = z • equivalence.functor.map f

end MTC
