module
public import PropertyF.Ground.CentreInduction.DrinfeldTheorem
public import PropertyF.Ground.CentreCabling.ImageCore
public import PropertyF.Ground.Integrate.ActualCenterReduction
public import PropertyF.Ground.CentreInduction.ActualFusion
public import PropertyF.Ground.CentreInduction.PositivePivotal
public import PropertyF.Ground.Centre.Rigid
public import PropertyF.Ground.CentreInduction.ForgetDual
public import PropertyF.Ground.CentreInduction.PivotalCentrality
public import PropertyF.Ground.Centre.Modular.Vafa
public import PropertyF.Ground.CentreModular.TransparencyCriterion

/-! # The centre reduction and the final theorem

The induction dimension formula and trivial centre transparency supply
the modular ingredients for the property-F weak-integrality theorem.

## Main results

* `center_globalDimension_square_of_actual_induction` gives the centre dimension.
* `center_transparent_label_eq_unit` proves trivial centre transparency.
* `target` proves weak integrality from property F and a pseudo-unitary conjugate. -/

section
/-! The constructed induction adjunction removes the centre square premise. -/

@[expose] public noncomputable section
open CategoryTheory
namespace PropertyF.Ground
universe v u

variable (C : BraidedFusionCategory.{v,u})
variable [RigidCategory (CategoryTheory.Center C.Obj)] [IsFusionCategory (CategoryTheory.Center C.Obj)]
local notation "𝒵ᶠ" => Integrate.bundledCenter C

/-- The centre square follows from its actual induction adjunction as soon as
its genuine fusion structure and FP-valued spherical structure are available. -/
theorem center_globalDimension_square_of_actual_induction
    {p : Dimensions.PivotalStructure (C := 𝒵ᶠ.Obj)}
    (hfp : Modular.IsFPSpherical 𝒵ᶠ p) :
    globalDimension 𝒵ᶠ = (globalFPDimension C : ℂ) ^ 2 :=
  (Modular.categorical_global_eq_sum_squares 𝒵ᶠ p hfp.1).trans <| by
    simpa [globalFPDimension, hfp.2, Complex.ofReal_sum, Complex.ofReal_pow] using
      congrArg (fun x : ℝ ↦ (x : ℂ)) (CentreInduction.globalFPDimension_square_of_actual_induction C)

end PropertyF.Ground
end
end

/-! # Pivotal and balancing reductions

The pivotal, balancing and transparency arguments supply the final reduction. -/

section

/-! Trivial centre transparency is constructed from actual induction. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground
universe v u
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false

variable (C : BraidedFusionCategory.{v,u})
variable [RigidCategory (CategoryTheory.Center C.Obj)] [IsFusionCategory (CategoryTheory.Center C.Obj)]
local notation "𝒵ᶠ" => Integrate.bundledCenter C

/-- The actual rigid fusion centre has no non-unit transparent simple. -/
theorem center_transparent_label_eq_unit
    (k : Fin (rank 𝒵ᶠ))
    (hk : Transparent (simples 𝒵ᶠ k)) :
    k = unitIndex 𝒵ᶠ :=
  let : Simple (simples 𝒵ᶠ k) := simples_simple _ k
  simples_injective _ ⟨(CentreInduction.center_transparent_simple_iso_unit (C := C) hk).some ≪≫
    (unitIndex_iso 𝒵ᶠ).some.symm⟩

end PropertyF.Ground
end
end

/-! The unconditional frozen target for genuine braided fusion categories. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground
universe v u

/-- A braided fusion category with property F and a pseudo-unitary Galois
conjugate has integral global Frobenius–Perron dimension. -/
theorem target : TargetStatement.{v,u} := by
  intro C hPU hF
  obtain ⟨D, _, ⟨E⟩, hD⟩ := hPU
  obtain ⟨p, _, hp⟩ := CentreInduction.positive_spherical_of_pseudoUnitary hD
  let := CentreRigid.rigidCenter (C := D.Obj)
  let hc := CentreInduction.pivotalComponentsCentral_proved p
  let pZ := CentreInduction.liftedPivotalStructure p hc
  let J := (CentreInduction.induction D).obj (𝟙_ D.Obj)
  let := CentreInduction.center_fusion_of_compatible_pivotal hp
    (CentreInduction.liftedPivotalStructure_compatible hc J)
  obtain ⟨hspherical, hfp⟩ := CentreInduction.center_positive_spherical_of_compatible_pivotal hp
    (CentreInduction.liftedPivotalStructure_compatible hc)
  have hdim : Modular.HasFPSimpleDimensions (Integrate.bundledCenter D) pZ := by
    intro i
    simpa [Modular.simpleDimension, Dimensions.pivotalDimension, Dimensions.rightTrace_id,
      unitScalar_eq_equiv] using hfp i
  have hbalance : CentreModular.IsPivotalTwistBalanced (Integrate.bundledCenter D) pZ :=
    fun X Y ↦ CentreIntegrate.pivotal_balance_of_drinfeld_tensor pZ
      (doubleDualIso (Integrate.bundledCenter D)) (drinfeld_tensor X Y).w
  have hdet := CentreModular.categoricalS_det_ne_zero_of_trivial_transparency
    (Integrate.bundledCenter D) pZ hdim hbalance (center_transparent_label_eq_unit D)
  have hfinite : CentreCabling.HasFiniteImageCentralizerMonodromy D pZ :=
    fun _ _ _ _ ↦ CentreModular.mixed_monodromy_finite_of_pivotal_balancing
      (Integrate.bundledCenter D) pZ hbalance _ _
  rw [Modular.conjugate_globalFPDimension E]
  apply weaklyIntegral_of_actual_center D (Modular.conjugate_propertyF E hF) ⟨hspherical, hdim⟩ hdet
    (center_globalDimension_square_of_actual_induction D ⟨hspherical, hdim⟩)
    (fun y hy ↦ CentreCalculus.actual_symmetricCore_integrality ⟨hspherical, hdim⟩
      (y := ⟨y, hy⟩))
  · exact fun y hy ↦ (CentreCabling.mem_productLabels D y).mpr
      (CentreCabling.productLabels_doubleCentralizer_of_image_monodromy D hspherical hdet hdim hfinite y hy)
  · exact fun y hy ↦ (CentreCabling.mem_productLabels D y).mp hy

end PropertyF.Ground
