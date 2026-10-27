module
public import PropertyF.Ground.CentreInduction.Splitting
public import PropertyF.Ground.Centre.Abelian
public import Mathlib.CategoryTheory.Subobject.ArtinianObject
public import Mathlib.CategoryTheory.Subobject.NoetherianObject
public import Mathlib.RingTheory.Artinian.Module
public import Mathlib.CategoryTheory.Abelian.Exact

/-! Finite Hom spaces and split monomorphisms force Artinian objects. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace PropertyF.Ground.CentreInduction
universe v u
variable {D : Type u} [Category.{v} D] [Preadditive D] [Linear ℂ D]

/-- Associate to a subobject the subspace of endomorphisms factoring through
its embedding. -/
def subobjectEndRange (X : D) (P : Subobject X) : Submodule ℂ (X ⟶ X) :=
  LinearMap.range (Linear.rightComp ℂ X P.arrow)






end PropertyF.Ground.CentreInduction
