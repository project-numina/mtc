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
  intro C hPU hF
  obtain ⟨D, _, ⟨E⟩, hD⟩ := hPU
  have hDF := Modular.conjugate_propertyF E hF
  obtain ⟨p, _, _⟩ := CentreInduction.positive_spherical_of_pseudoUnitary D hD
  let := CentreRigid.rigidCenter (C := D.Obj)
  let := centerFusionOfPivotalPseudoUnitary D p hD
  let pZ := centerPivotalOfPivotalPseudoUnitary D p hD
  have hbalance : CentreModular.IsPivotalTwistBalanced (Integrate.bundledCenter D) pZ :=
    fun X Y ↦ pivotal_twist_balanced (Integrate.bundledCenter D) pZ X Y
  have hs := Classical.choose_spec (Classical.choose_spec
    (CentreInduction.center_structure_of_pivotal_pseudoUnitary D p hD))
  obtain ⟨hspherical, _, _, _⟩ := hs
  have hdim := centerPivotal_hasFPDimensions D p hD
  have hdet := CentreModular.categoricalS_det_ne_zero_of_trivial_transparency
    (Integrate.bundledCenter D) pZ hdim hbalance (center_transparent_label_eq_unit D)
  have hfinite : CentreCabling.HasFiniteImageCentralizerMonodromy D pZ := by
    intro y _ a _
    exact CentreModular.mixed_monodromy_finite_of_pivotal_balancing
      (Integrate.bundledCenter D) pZ hbalance _ _
  have hInt : WeaklyIntegral (globalFPDimension D) := by
    apply weaklyIntegral_of_actual_center D hDF hspherical hdim hdet
      (center_globalDimension_square_of_actual_induction D pZ hspherical hdim)
      (CentreCalculus.actual_symmetricCore_integrality hspherical hdim)
    · intro y hy
      exact (CentreCabling.mem_productLabels D y).mpr
        (CentreCabling.productLabels_doubleCentralizer_of_image_monodromy D hspherical hdet hdim hfinite y hy)
    · intro y hy
      exact (CentreCabling.mem_productLabels D y).mp hy
  rwa [Modular.conjugate_globalFPDimension E]

end PropertyF.Ground
