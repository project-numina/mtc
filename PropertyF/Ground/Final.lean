module
public import PropertyF.Ground.Integrate.DrinfeldComplete
public import PropertyF.Ground.CentreInduction.DrinfeldTheorem

/-! The unconditional frozen target for genuine braided fusion categories. -/

@[expose] public noncomputable section
open CategoryTheory
namespace PropertyF.Ground
universe v u

/-- A braided fusion category with property F and a pseudo-unitary Galois
conjugate has integral global Frobenius–Perron dimension. -/
theorem target : TargetStatement.{v,u} := by
  apply target_of_actual_center
  intro C hpu hF
  obtain ⟨p, _, _⟩ := CentreInduction.positive_spherical_of_pseudoUnitary C hpu
  let := CentreRigid.rigidCenter (C := C.Obj)
  let := centerFusionOfPivotalPseudoUnitary C p hpu
  let pZ := centerPivotalOfPivotalPseudoUnitary C p hpu
  have hbalance : CentreModular.IsPivotalTwistBalanced (Integrate.bundledCenter C) pZ :=
    fun X Y ↦ pivotal_twist_balanced (Integrate.bundledCenter C) pZ X Y
  have hs := Classical.choose_spec (Classical.choose_spec
    (CentreInduction.center_structure_of_pivotal_pseudoUnitary C p hpu))
  obtain ⟨hspherical, _, _, _⟩ := hs
  have hdim := centerPivotal_hasFPDimensions C p hpu
  have hdet := CentreModular.categoricalS_det_ne_zero_of_trivial_transparency
    (Integrate.bundledCenter C) pZ hdim hbalance (center_transparent_label_eq_unit C)
  have hfinite : CentreCabling.HasFiniteImageCentralizerMonodromy C pZ := by
    intro y _ a _
    exact CentreModular.mixed_monodromy_finite_of_pivotal_balancing
      (Integrate.bundledCenter C) pZ hbalance _ _
  refine ⟨CentreRigid.rigidCenter, inferInstance, pZ, CentreCabling.symmetricCore C,
    (↑(CentreCabling.productLabels C) : Set _), hspherical, hdim, hdet,
    center_globalDimension_square_of_actual_induction C pZ hspherical hdim,
    CentreCalculus.actual_symmetricCore_integrality C pZ hspherical hdim, ?_, ?_⟩
  · intro y hy
    exact (CentreCabling.mem_productLabels C y).mpr
      (CentreCabling.productLabels_doubleCentralizer_of_image_monodromy C hspherical hdet hdim hfinite y hy)
  · intro y hy
    exact (CentreCabling.mem_productLabels C y).mp hy

end PropertyF.Ground
