module
public import PropertyF.Ground.Integrate.CoreIntegralityReduction
public import PropertyF.Ground.CentreCalculus.ActualCoreIntegrality
public import PropertyF.Ground.Centre.Modular.Vafa

/-! The actual core and mixed-monodromy obligations from pivotal balancing. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground
universe v u
set_option linter.style.haveILetI false

/-- For a pseudo-unitary base with a pivotal structure, the actual centre is
rigid, fusion and positive spherical. If its pivotal twist is balanced, its
symmetric core is integral and the required mixed monodromy has finite order.
The base pivotal structure, balancing and S invertibility are still explicit
premises. -/
theorem target_of_pivotal_base_modular_balanced_center
    (hCenter : ∀ (C : BraidedFusionCategory.{v,u}) (hpu : PseudoUnitary C),
      HasPropertyF C.Obj →
      ∃ (p : Dimensions.PivotalStructure (C := C.Obj)),
        letI := CentreRigid.rigidCenter (C := C.Obj)
        letI := centerFusionOfPivotalPseudoUnitary C p hpu
        let pZ := centerPivotalOfPivotalPseudoUnitary C p hpu
        let D := Integrate.bundledCenter C
        (Modular.categoricalS D pZ).det ≠ 0 ∧
        (∀ X Y : D.Obj, Modular.doubleBraiding X Y ≫
          ((Dimensions.pivotalBraidedTwist D pZ X).hom ⊗ₘ
            (Dimensions.pivotalBraidedTwist D pZ Y).hom) =
          (Dimensions.pivotalBraidedTwist D pZ (X ⊗ Y)).hom)) : TargetStatement.{v,u} := by
  apply target_of_center_image_monodromy_no_square
  intro C hpu hF
  obtain ⟨p, hdet, hbalance⟩ := hCenter C hpu hF
  letI := CentreRigid.rigidCenter (C := C.Obj)
  letI := centerFusionOfPivotalPseudoUnitary C p hpu
  let pZ := centerPivotalOfPivotalPseudoUnitary C p hpu
  have hs := Classical.choose_spec (Classical.choose_spec
    (CentreInduction.center_structure_of_pivotal_pseudoUnitary C p hpu))
  obtain ⟨hspherical, hd, _, _⟩ := hs
  change ∀ i, Dimensions.pivotalDimension (Integrate.bundledCenter C) pZ
    (simples (Integrate.bundledCenter C) i) = (fpSimple (Integrate.bundledCenter C) i : ℂ) at hd
  have hdim : ∀ i, Modular.simpleDimension (Integrate.bundledCenter C) pZ i =
      (fpSimple (Integrate.bundledCenter C) i : ℂ) := by
    intro i
    simpa [Modular.simpleDimension, Dimensions.pivotalDimension, Dimensions.rightTrace_id,
      Dimensions.groundUnitScalarEquiv_apply, unitScalar_eq_equiv] using hd i
  refine ⟨CentreRigid.rigidCenter, inferInstance, pZ, hspherical, hdim, hdet,
    CentreCalculus.actual_symmetricCore_integrality C pZ hspherical hdim, ?_⟩
  intro y _ a _
  exact CentreModular.mixed_monodromy_finite_of_pivotal_balancing
    (Integrate.bundledCenter C) pZ hbalance _ _

end PropertyF.Ground
