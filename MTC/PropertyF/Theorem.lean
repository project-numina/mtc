module
public import MTC.Center.Induction.DrinfeldTheorem
public import MTC.Center.Braid.ImageCore
public import MTC.PropertyF.Reduction.ActualCenterReduction
public import MTC.Center.Induction.ActualFusion
public import MTC.Center.Induction.PositivePivotal
public import MTC.Center.Rigid
public import MTC.Center.Induction.ForgetDual
public import MTC.Center.Induction.PivotalCentrality
public import MTC.Center.Modular.Vafa
public import MTC.Center.Modular.TransparencyCriterion

/-! # The centre reduction and the final theorem

The induction dimension formula and trivial centre transparency supply
the modular ingredients for the property-F weak-integrality theorem.

## Main results

* `center_globalDimension_square_of_actual_induction` gives the centre dimension.
* `center_transparent_label_eq_unit` proves trivial centre transparency.
* `PropertyF.weaklyIntegral_of_propertyF` proves weak integrality from property F and a pseudo-unitary conjugate. -/

section
/-! The constructed induction adjunction removes the centre square premise. -/

@[expose] public noncomputable section
open CategoryTheory
namespace MTC
universe v u

variable (C : BraidedFusionCategory.{v,u})
variable [RigidCategory (CategoryTheory.Center C.Obj)] [IsFusionCategory (CategoryTheory.Center C.Obj)]
local notation "𝒵ᶠ" => MTC.PropertyF.Reduction.bundledCenter C

/-- The centre square follows from its actual induction adjunction as soon as
its genuine fusion structure and FP-valued spherical structure are available. -/
theorem center_globalDimension_square_of_actual_induction
    {p : Dimensions.PivotalStructure (C := 𝒵ᶠ.Obj)}
    (hfp : Modular.IsFPSpherical 𝒵ᶠ p) :
    globalDimension 𝒵ᶠ = (globalFPDimension C : ℂ) ^ 2 :=
  (Modular.categorical_global_eq_sum_squares 𝒵ᶠ p hfp.1).trans <| by
    simpa [globalFPDimension, hfp.2, Complex.ofReal_sum, Complex.ofReal_pow] using
      congrArg (fun x : ℝ ↦ (x : ℂ)) (MTC.Center.Induction.globalFPDimension_square_of_actual_induction C)

end MTC
end
end

/-! # Pivotal and balancing reductions

The pivotal, balancing and transparency arguments supply the final reduction. -/

section

/-! Trivial centre transparency is constructed from actual induction. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace MTC
universe v u
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false

variable (C : BraidedFusionCategory.{v,u})
variable [RigidCategory (CategoryTheory.Center C.Obj)] [IsFusionCategory (CategoryTheory.Center C.Obj)]
local notation "𝒵ᶠ" => MTC.PropertyF.Reduction.bundledCenter C

/-- The actual rigid fusion centre has no non-unit transparent simple. -/
theorem center_transparent_label_eq_unit
    (k : Fin (rank 𝒵ᶠ))
    (hk : Transparent (simples 𝒵ᶠ k)) :
    k = unitIndex 𝒵ᶠ :=
  let : Simple (simples 𝒵ᶠ k) := simples_simple _ k
  simples_injective _ ⟨(MTC.Center.Induction.center_transparent_simple_iso_unit (C := C) hk).some ≪≫
    (unitIndex_iso 𝒵ᶠ).some.symm⟩

end MTC
end
end

/-! The unconditional frozen target for genuine braided fusion categories. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace MTC
universe v u

/-- A braided fusion category with property F and a pseudo-unitary Galois
conjugate has integral global Frobenius–Perron dimension. -/
theorem PropertyF.weaklyIntegral_of_propertyF : PropertyF.TargetStatement.{v,u} := by
  intro C hPU hF
  obtain ⟨D, _, ⟨E⟩, hD⟩ := hPU
  obtain ⟨p, _, hp⟩ := MTC.Center.Induction.positive_spherical_of_pseudoUnitary hD
  let := MTC.Center.Rigid.rigidCenter (C := D.Obj)
  let hc := MTC.Center.Induction.pivotalComponentsCentral_proved p
  let pZ := MTC.Center.Induction.liftedPivotalStructure p hc
  let J := (MTC.Center.Induction.induction D).obj (𝟙_ D.Obj)
  let := MTC.Center.Induction.center_fusion_of_compatible_pivotal hp
    (MTC.Center.Induction.liftedPivotalStructure_compatible hc J)
  obtain ⟨hspherical, hfp⟩ := MTC.Center.Induction.center_positive_spherical_of_compatible_pivotal hp
    (MTC.Center.Induction.liftedPivotalStructure_compatible hc)
  have hdim : Modular.HasFPSimpleDimensions (MTC.PropertyF.Reduction.bundledCenter D) pZ := by
    intro i
    simpa [Modular.simpleDimension, Dimensions.pivotalDimension, Dimensions.rightTrace_id,
      unitScalar_eq_equiv] using hfp i
  have hbalance : MTC.Center.Modular.IsPivotalTwistBalanced (MTC.PropertyF.Reduction.bundledCenter D) pZ :=
    fun X Y ↦ MTC.Center.Balancing.pivotal_balance_of_drinfeld_tensor pZ
      (doubleDualIso (MTC.PropertyF.Reduction.bundledCenter D)) (drinfeld_tensor X Y).w
  have hdet := MTC.Center.Modular.categoricalS_det_ne_zero_of_trivial_transparency
    (MTC.PropertyF.Reduction.bundledCenter D) pZ hdim hbalance (center_transparent_label_eq_unit D)
  have hfinite : MTC.Center.Braid.HasFiniteImageCentralizerMonodromy D pZ :=
    fun _ _ _ _ ↦ MTC.Center.Modular.mixed_monodromy_finite_of_pivotal_balancing
      (MTC.PropertyF.Reduction.bundledCenter D) pZ hbalance _ _
  rw [Modular.conjugate_globalFPDimension E]
  apply weaklyIntegral_of_actual_center D (Modular.conjugate_propertyF E hF) ⟨hspherical, hdim⟩ hdet
    (center_globalDimension_square_of_actual_induction D ⟨hspherical, hdim⟩)
    (fun y hy ↦ MTC.Center.Trace.actual_symmetricCore_integrality ⟨hspherical, hdim⟩
      (y := ⟨y, hy⟩))
  · exact fun y hy ↦ (MTC.Center.Braid.mem_productLabels D y).mpr
      (MTC.Center.Braid.productLabels_doubleCentralizer_of_image_monodromy D hspherical hdet hdim hfinite y hy)
  · exact fun y hy ↦ (MTC.Center.Braid.mem_productLabels D y).mp hy

end MTC
