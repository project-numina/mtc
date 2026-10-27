module
public import PropertyF.Ground.Integrate.BalancedCenterReduction
public import PropertyF.Ground.CentreModular.TransparencyCriterion

/-! Actual centre transparency replaces the S-determinant premise. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground
universe v u
set_option linter.style.haveILetI false

/-- The target follows from base pivotal existence, balancing of the resulting
centre pivotal twist, and triviality of the centre's transparent simples.
These three conditions remain explicit and unproved here. -/
theorem target_of_pivotal_balanced_center_trivial_transparency
    (hCenter : ∀ (C : BraidedFusionCategory.{v,u}) (hpu : PseudoUnitary C),
      HasPropertyF C.Obj →
      ∃ (p : Dimensions.PivotalStructure (C := C.Obj)),
        letI := CentreRigid.rigidCenter (C := C.Obj)
        letI := centerFusionOfPivotalPseudoUnitary C p hpu
        let pZ := centerPivotalOfPivotalPseudoUnitary C p hpu
        let D := Integrate.bundledCenter C
        (∀ X Y : D.Obj, Modular.doubleBraiding X Y ≫
          ((Dimensions.pivotalBraidedTwist D pZ X).hom ⊗ₘ
            (Dimensions.pivotalBraidedTwist D pZ Y).hom) =
          (Dimensions.pivotalBraidedTwist D pZ (X ⊗ Y)).hom) ∧
        (∀ k, Transparent (simples D k) → k = unitIndex D)) : TargetStatement.{v,u} := by
  apply target_of_pivotal_base_modular_balanced_center
  intro C hpu hF
  obtain ⟨p, hbalance, htrivial⟩ := hCenter C hpu hF
  letI := CentreRigid.rigidCenter (C := C.Obj)
  letI := centerFusionOfPivotalPseudoUnitary C p hpu
  let pZ := centerPivotalOfPivotalPseudoUnitary C p hpu
  have hs := Classical.choose_spec (Classical.choose_spec
    (CentreInduction.center_structure_of_pivotal_pseudoUnitary C p hpu))
  obtain ⟨_, hd, _, _⟩ := hs
  change ∀ i, Dimensions.pivotalDimension (Integrate.bundledCenter C) pZ
    (simples (Integrate.bundledCenter C) i) = (fpSimple (Integrate.bundledCenter C) i : ℂ) at hd
  have hdim : ∀ i, Modular.simpleDimension (Integrate.bundledCenter C) pZ i =
      (fpSimple (Integrate.bundledCenter C) i : ℂ) := by
    intro i
    simpa [Modular.simpleDimension, Dimensions.pivotalDimension, Dimensions.rightTrace_id,
      Dimensions.groundUnitScalarEquiv_apply, unitScalar_eq_equiv] using hd i
  exact ⟨p, CentreModular.categoricalS_det_ne_zero_of_trivial_transparency
    (Integrate.bundledCenter C) pZ hdim hbalance htrivial, hbalance⟩

end PropertyF.Ground
