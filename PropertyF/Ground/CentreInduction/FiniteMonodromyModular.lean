module
public import PropertyF.Ground.CentreInduction.Transparent
public import PropertyF.Ground.CentreCabling.TraceSaturation
public import PropertyF.Ground.CentreCabling.CentralityClosure
public import PropertyF.Ground.CentreModular.TransparencyCriterion

/-! Nondegeneracy from finite mixed monodromy and the trivial transparent centre. -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.CentreInduction
universe v u
set_option backward.isDefEq.respectTransparency false
variable (C : BraidedFusionCategory.{v,u}) [RigidCategory (CategoryTheory.Center C.Obj)]
  [IsFusionCategory (CategoryTheory.Center C.Obj)]

/-- Finite-order simple mixed monodromies make the actual centre S matrix invertible. -/
theorem center_S_invertible_of_finite_simple_monodromy
    (p : Dimensions.PivotalStructure (C := CategoryTheory.Center C.Obj))
    (hdim : ∀ i, Modular.simpleDimension (Integrate.bundledCenter C) p i =
      (fpSimple (Integrate.bundledCenter C) i : ℂ))
    (hfinite : ∀ i j, IsOfFinOrder (End.of (Modular.doubleBraiding
      (simples (Integrate.bundledCenter C) i) (simples (Integrate.bundledCenter C) j)))) :
    (Modular.categoricalS (Integrate.bundledCenter C) p).det ≠ 0 := by
  let D := Integrate.bundledCenter C
  apply CentreModular.categoricalS_det_ne_zero_of_trivial_S_centralizer D p hdim
  intro k hs
  let Z := simples D k
  letI : Simple Z := simples_simple D k
  have hc (W : CategoryTheory.Center C.Obj) : Centre.Centralizes Z W := by
    apply Centre.centralizes_symm
    have hm := CentreCabling.doubleBraiding_eq_one_of_simple_constituents D (fun _ => True)
      (fun _ _ => trivial) W Z trivial (fun i _ =>
        CentreCabling.doubleBraiding_eq_one_of_sTest_of_finite_order D p hdim i k (hfinite i k) (hs i))
    exact hm
  obtain ⟨e⟩ := center_transparent_simple_iso_unit C Z hc
  exact simples_injective D k (unitIndex D) ⟨e ≪≫ (Classical.choice (unitIndex_iso D)).symm⟩
end PropertyF.Ground.CentreInduction
