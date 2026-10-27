module
public import PropertyF.Ground.CentreCalculus.TwistSign
public import PropertyF.Ground.CentreCabling.ProductCore

/-! Integral dimensions for the actual symmetric core of the Drinfeld centre. -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.CentreCalculus
universe v u

/-- Every simple in the common centralizer of the two canonical images in
Mathlib's actual centre has integer categorical dimension in an FP-valued
spherical structure. -/
theorem actual_symmetricCore_integrality (C : BraidedFusionCategory.{v,u})
    [RigidCategory (CategoryTheory.Center C.Obj)]
    [IsFusionCategory (CategoryTheory.Center C.Obj)]
    (p : Dimensions.PivotalStructure (C := (Integrate.bundledCenter C).Obj))
    (hp : p.IsSpherical)
    (hdim : ∀ i, Modular.simpleDimension (Integrate.bundledCenter C) p i =
      (fpSimple (Integrate.bundledCenter C) i : ℂ)) :
    ∀ y ∈ CentreCabling.symmetricCore C,
      ∃ z : ℤ, Modular.simpleDimension (Integrate.bundledCenter C) p y = z :=
  fun y hy ↦ selfTransparent_simpleDimension_integer (Integrate.bundledCenter C) p hp hdim y
    (commonCentralizer_self (simples (Integrate.bundledCenter C) y) hy.1 hy.2)

end PropertyF.Ground.CentreCalculus
