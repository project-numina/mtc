module
public import PropertyF.Ground.CentreInduction.Fusion
public import PropertyF.Ground.Fusion.SpectralIntegral

/-! Pseudo-unitarity supplies the nonzero scalar needed for averaging. -/

@[expose] public noncomputable section
open CategoryTheory
namespace PropertyF.Ground.CentreInduction
universe v u

/-- The global categorical dimension of a pseudo-unitary fusion category is
nonzero, because its global FP dimension is at least one. -/
theorem globalDimension_ne_zero_of_pseudoUnitary (C : BraidedFusionCategory.{v,u})
    (hPU : PseudoUnitary C) : globalDimension C ≠ 0 :=
by
  rw [hPU]
  exact_mod_cast (ne_of_gt (lt_of_lt_of_le zero_lt_one (one_le_globalFPDimension C)))

/-- For pseudo-unitary C the fusion assembly needs no separate nonzero
global-dimension premise. The adjunction and loop-sliding identity remain
explicit unproved assumptions. -/
theorem fusion_of_pseudoUnitary_and_induction (C : BraidedFusionCategory.{v,u})
    [RigidCategory (CategoryTheory.Center C.Obj)] (hPU : PseudoUnitary C)
    (p : Dimensions.PivotalStructure (C := C.Obj)) (hp : p.IsSpherical)
    (hslide : SimpleLoopCentrality C p)
    (I : C.Obj ⥤ CategoryTheory.Center C.Obj)
    (adj : CategoryTheory.Center.forget C.Obj ⊣ I) :
    IsFusionCategory (CategoryTheory.Center C.Obj) :=
  fusion_of_adjunction_and_loop C p hp hslide
    (globalDimension_ne_zero_of_pseudoUnitary C hPU) I adj

end PropertyF.Ground.CentreInduction
