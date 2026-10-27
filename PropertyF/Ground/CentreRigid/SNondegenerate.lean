module
public import PropertyF.Ground.CentreRigid.TransparentUnit
public import PropertyF.Ground.CentreCabling.CoreCentrality
public import PropertyF.Ground.CentreModular.KirbyCriterion

/-! Numerical nondegeneracy from categorical centre nondegeneracy. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
namespace PropertyF.Ground.CentreRigid
universe v u
/-- Test objects are retracts of negative images or of the induced unit. -/
def centralTest (C : BraidedFusionCategory.{v,u}) (W : Center C.Obj) : Prop :=
  (∃ T : C.Obj, Nonempty (Retract W ((Centre.negative C.Obj).obj T))) ∨
    Nonempty (Retract W ((CentreInduction.induction C).obj (𝟙_ C.Obj)))

/-- The test-object class is closed under retracts. -/
theorem centralTest_retract (C : BraidedFusionCategory.{v,u}) {X Y : Center C.Obj}
    (r : Retract X Y) (h : centralTest C Y) : centralTest C X := by
  rcases h with h | h
  · obtain ⟨T, ⟨s⟩⟩ := h
    exact Or.inl ⟨T, ⟨r.trans s⟩⟩
  · obtain ⟨s⟩ := h
    exact Or.inr ⟨r.trans s⟩

set_option backward.isDefEq.respectTransparency false in
/-- Centre S is invertible when numerical centrality detects centrality on the test objects. -/
theorem center_s_invertible_of_test_monodromy (C : BraidedFusionCategory.{v,u})
    [RigidCategory (Center C.Obj)] [IsFusionCategory (Center C.Obj)]
    (p : Dimensions.PivotalStructure (C := (Integrate.bundledCenter C).Obj))
    (hdim : ∀ i, Modular.simpleDimension (Integrate.bundledCenter C) p i =
      (fpSimple (Integrate.bundledCenter C) i : ℂ))
    (hfinite : ∀ y, (∀ i, Modular.categoricalS (Integrate.bundledCenter C) p i y =
      Modular.simpleDimension (Integrate.bundledCenter C) p i *
        Modular.simpleDimension (Integrate.bundledCenter C) p y) →
      ∀ i, centralTest C (simples (Integrate.bundledCenter C) i) →
      IsOfFinOrder (End.of (Modular.doubleBraiding
        (simples (Integrate.bundledCenter C) i) (simples (Integrate.bundledCenter C) y)))) :
    (Modular.categoricalS (Integrate.bundledCenter C) p).det ≠ 0 := by
  let D := Integrate.bundledCenter C
  apply CentreModular.categoricalS_det_ne_zero_of_trivial_S_centralizer D p hdim
  intro y hy
  let Z : Center C.Obj := simples D y
  letI : Simple Z := simples_simple D y
  have hcentral (W : Center C.Obj) (hW : centralTest C W) : Centre.Centralizes Z W := by
    apply Centre.centralizes_symm
    change Modular.doubleBraiding W Z = 𝟙 _
    apply CentreCabling.doubleBraiding_eq_one_of_simple_constituents D (centralTest C)
      (fun r hr => centralTest_retract C r hr) W Z hW
    intro i hi
    exact CentreCabling.doubleBraiding_eq_one_of_sTest_of_finite_order D p hdim i y
      (hfinite y hy i hi) (hy i)
  obtain ⟨e⟩ := CentreRigid.negative_and_induced_detect_unit C Z
    (fun T => hcentral _ (Or.inl ⟨T, ⟨Retract.refl _⟩⟩))
    (hcentral _ (Or.inr ⟨Retract.refl _⟩))
  apply simples_injective D y (unitIndex D)
  obtain ⟨u⟩ := unitIndex_iso D
  exact ⟨e ≪≫ u.symm⟩

end PropertyF.Ground.CentreRigid
