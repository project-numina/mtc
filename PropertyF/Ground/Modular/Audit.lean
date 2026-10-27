module


import all PropertyF.Definitions
import all PropertyF.Axioms
import all PropertyF.BlockTrace
import all PropertyF.CenterBasics
import all PropertyF.UnitaryTrace
import all PropertyF.Ground.Target
import all PropertyF.Ground.Fusion.Splitting
import all PropertyF.Ground.Fusion.Simples
import all PropertyF.Ground.Fusion.Multiplicity
import all PropertyF.Ground.Fusion.Reciprocity
import all PropertyF.Ground.Fusion.MatrixIntegral
import all PropertyF.Ground.Fusion.SpectralIntegral
import all PropertyF.Ground.Integrate.UnitScalar
import all PropertyF.Ground.Integrate.Representatives
import all PropertyF.Ground.Dimensions.Norm
import all PropertyF.Ground.Dimensions.Pivotal
import all PropertyF.Ground.Dimensions.Trace
import all PropertyF.Ground.Dimensions.DualCoherence
import all PropertyF.Ground.Dimensions.BiproductTrace
import all PropertyF.Ground.Calculus.PartialTrace
import all PropertyF.Ground.Dimensions.TensorTrace
import all PropertyF.Ground.Dimensions.IteratedTrace
import all PropertyF.Ground.Dimensions.GroundNorm
import all PropertyF.Ground.Modular.BraidIso
import all PropertyF.Ground.Modular.BraidFunctor
import all PropertyF.Ground.Modular.Characters
import all PropertyF.Ground.Modular.Classification
import all PropertyF.Ground.Modular.Labels
import all PropertyF.Ground.Modular.FusionTransport
import all PropertyF.Ground.Modular.SMatrix
import all PropertyF.Ground.Modular.SAdditivity
import all PropertyF.Ground.Modular.HopfPartialTrace
import all PropertyF.Ground.Modular.Verlinde
import all PropertyF.Ground.Modular.DimensionNonzero
import all PropertyF.Ground.Modular.UnitDimension
import all PropertyF.Ground.Modular.GaloisFromVerlinde
import all PropertyF.Ground.Modular.PseudoGalois
import all PropertyF.Ground.Integrate.DependencyAudit
meta import PropertyF.Ground.Integrate.DependencyAudit
/-!
# Modular ground dependency audit

Build this module to inspect both types and private bodies of the ground
modular declarations, rejecting old hypothesis bundles and non-foundational
axioms. The final target audit remains the responsibility of integration.
-/

open Lean Elab Command PropertyF.Ground.DependencyAudit in
run_cmd do
  let env ← getEnv
  for n in #[``PropertyF.Ground.Modular.conjugate_labels,
      ``PropertyF.Ground.Modular.conjugate_globalFPDimension,
      ``PropertyF.Ground.Modular.conjugate_propertyF,
      ``PropertyF.Ground.Modular.braidImageFunctorMap_surjective,
      ``PropertyF.Ground.Modular.categoricalS_symmetric,
      ``PropertyF.Ground.Modular.categoricalS_unit,
      ``PropertyF.Ground.Modular.SEntry_tensor_decomposition,
      ``PropertyF.Ground.Modular.partialTrace_doubleBraiding_simple,
      ``PropertyF.Ground.Modular.hopf_product_of_partialTrace_composition,
      ``PropertyF.Ground.Modular.categoricalS_verlinde_of_hopf_product,
      ``PropertyF.Ground.Modular.categoricalS_verlinde,
      ``PropertyF.Ground.Modular.categoricalS_galois_action_of_S_square,
      ``PropertyF.Ground.Modular.simpleDimension_ne_zero,
      ``PropertyF.Ground.Modular.simpleDimension_unit,
      ``PropertyF.Ground.Modular.categoricalS_galois_action,
      ``PropertyF.Ground.Modular.galois_unit_properties,
      ``PropertyF.Ground.Modular.categoricalS_galois_action_pseudoUnitary,
      ``PropertyF.Ground.Modular.categoricalS_galois_unit_properties] do
    if let some bad := findIssue env n then
      throwError "{n}: {repr bad}"
    let axioms ← Lean.collectAxioms n
    for ax in axioms do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "{n} depends on forbidden axiom {ax}"
    logInfo m!"{n}: hardened scan and axiom audit clean"
