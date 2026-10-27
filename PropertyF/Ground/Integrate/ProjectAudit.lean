module
public import PropertyF.Audit
public meta import PropertyF.Ground.Integrate.DependencyAudit
public import PropertyF.Ground.Integrate.UnitScalar
public import PropertyF.Ground.Integrate.Norm
public import PropertyF.Ground.Integrate.StrandInclusion
public import PropertyF.Ground.Integrate.Representatives
public import PropertyF.Ground.Integrate.Conjugacy
public import PropertyF.Ground.Integrate.Arithmetic
public import PropertyF.Ground.Integrate.PropertyFTransport
public import PropertyF.Ground.Final
public import PropertyF.Ground.Modular.Labels
public import PropertyF.Ground.Fusion.Reciprocity
public import PropertyF.Ground.Fusion.MatrixIntegral
public import PropertyF.Ground.Integrate.Example
public import PropertyF.Ground.Fusion.Integrality
public import PropertyF.Ground.Fusion.Splitting
public import PropertyF.Ground.Dimensions.DimensionField
public import PropertyF.Ground.Dimensions.Norm
public import PropertyF.Ground.Calculus.StarSpan
public import PropertyF.Ground.Centre.Embeddings
public import PropertyF.Ground.Modular.Classification
public import PropertyF.Ground.Cabling.Strands
public import PropertyF.Ground.Cabling.Pure
public import PropertyF.Ground.Cabling.Witness








import all PropertyF.Arithmetic
import all PropertyF.Audit
import all PropertyF.Axioms
import all PropertyF.BlockTrace
import all PropertyF.BraidAlgebra
import all PropertyF.Center
import all PropertyF.CenterBasics
import all PropertyF.Consequences
import all PropertyF.Definitions
import all PropertyF.Descent
import all PropertyF.GaloisRigidity
import all PropertyF.GaloisSymmetry
import all PropertyF.Ground.Cabling.DualClosure
import all PropertyF.Ground.Cabling.Generated
import all PropertyF.Ground.Cabling.Images
import all PropertyF.Ground.Cabling.Inclusion
import all PropertyF.Ground.Cabling.Perron
import all PropertyF.Ground.Cabling.Primitive
import all PropertyF.Ground.Cabling.Pure
import all PropertyF.Ground.Cabling.Rigidity
import all PropertyF.Ground.Cabling.Strands
import all PropertyF.Ground.Cabling.Witness
import all PropertyF.Ground.Calculus.Averaging
import all PropertyF.Ground.Calculus.BraidBlocks
import all PropertyF.Ground.Calculus.CategoricalTrace
import all PropertyF.Ground.Calculus.CyclicTrace
import all PropertyF.Ground.Calculus.FiniteOrder
import all PropertyF.Ground.Calculus.GroupBlocks
import all PropertyF.Ground.Calculus.ImageMaps
import all PropertyF.Ground.Calculus.Intertwining
import all PropertyF.Ground.Calculus.PartialTrace
import all PropertyF.Ground.Calculus.StarSpan
import all PropertyF.Ground.Calculus.Unitarization
import all PropertyF.Ground.Calculus.UnitaryBlocks
import all PropertyF.Ground.Centre.Embeddings
import all PropertyF.Ground.Centre.Linear
import all PropertyF.Ground.Centre.Product
import all PropertyF.Ground.Centre.ProductImages
import all PropertyF.Ground.Centre.ReverseBraiding
import all PropertyF.Ground.Centre.Zero
import all PropertyF.Ground.Dimensions.BiproductTrace
import all PropertyF.Ground.Dimensions.CharacterBound
import all PropertyF.Ground.Dimensions.DimensionField
import all PropertyF.Ground.Dimensions.FusionDimensionField
import all PropertyF.Ground.Dimensions.GlobalInequality
import all PropertyF.Ground.Dimensions.GroundNorm
import all PropertyF.Ground.Dimensions.Norm
import all PropertyF.Ground.Dimensions.Pivotal
import all PropertyF.Ground.Dimensions.TargetDimensionField
import all PropertyF.Ground.Dimensions.Trace
import all PropertyF.Ground.Final
import all PropertyF.Ground.Fusion.Agreement
import all PropertyF.Ground.Fusion.Character
import all PropertyF.Ground.Fusion.Integrality
import all PropertyF.Ground.Fusion.MatrixIntegral
import all PropertyF.Ground.Fusion.Multiplicity
import all PropertyF.Ground.Fusion.Perron
import all PropertyF.Ground.Fusion.PositiveMatrix
import all PropertyF.Ground.Fusion.Reciprocity
import all PropertyF.Ground.Fusion.Schur
import all PropertyF.Ground.Fusion.Simples
import all PropertyF.Ground.Fusion.SpectralBound
import all PropertyF.Ground.Fusion.SpectralIntegral
import all PropertyF.Ground.Fusion.Splitting
import all PropertyF.Ground.Fusion.TotalMatrix
import all PropertyF.Ground.Integrate.Arithmetic
import all PropertyF.Ground.Integrate.Conjugacy
import all PropertyF.Ground.Integrate.DependencyAudit
import all PropertyF.Ground.Integrate.Example
import all PropertyF.Ground.Integrate.FPRepresentatives
import all PropertyF.Ground.Integrate.Fixedness
import all PropertyF.Ground.Integrate.LegacyBridge
import all PropertyF.Ground.Integrate.Norm
import all PropertyF.Ground.Integrate.PropertyFTransport
import all PropertyF.Ground.Integrate.Reduction
import all PropertyF.Ground.Integrate.Representatives
import all PropertyF.Ground.Integrate.StrandInclusion
import all PropertyF.Ground.Integrate.UnitScalar
import all PropertyF.Ground.Modular.BraidFunctor
import all PropertyF.Ground.Modular.BraidIso
import all PropertyF.Ground.Modular.Characters
import all PropertyF.Ground.Modular.Classification
import all PropertyF.Ground.Modular.FusionTransport
import all PropertyF.Ground.Modular.GaloisFromVerlinde
import all PropertyF.Ground.Modular.Labels
import all PropertyF.Ground.Modular.SMatrix
import all PropertyF.Ground.Target
import all PropertyF.Main
import all PropertyF.PowerBound
import all PropertyF.TraceBound
import all PropertyF.Transfer
import all PropertyF.UnitaryTrace

/-! Scan all currently integrated project declarations, including the ground
modules. `PropertyF.Audit` alone sees only its own imports. -/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut checked : Nat := 0
  for (name, _) in env.constants.toList do
    if name.toString.startsWith "PropertyF." then
      for ax in ← collectAxioms name do
        unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
          throwError "Unexpected axiom {ax} in project declaration {name}"
      checked := checked + 1
  logInfo m!"Audited {checked} integrated project declarations: no sorryAx or custom axioms."

open Lean Elab Command PropertyF.Ground.DependencyAudit in
run_cmd do
  let env ← getEnv
  match findIssue env ``PropertyF.Ground.DependencyAudit.hiddenInputWrapper with
  | some (.forbidden n) =>
      unless n == ``PropertyF.StandardInputs do
        throwError "unexpected forbidden fixture dependency {n}"
  | _ => throwError "dependency audit did not inspect an imported definition body"
  unless (findIssue env ``PropertyF.Ground.legacyCategory).isSome do
    throwError "dependency audit did not reject the old compatibility bundle"
  unless (findIssue env ``PropertyF.propertyF_implies_weaklyIntegral).isSome do
    throwError "dependency audit did not reject the imported conditional theorem"
  for n in #[``PropertyF.Ground.TargetStatement,
      ``PropertyF.Ground.unit_algebraMap_bijective,
      ``PropertyF.Ground.Example.complexVectorSpaces,
      ``PropertyF.Ground.squaredNorm_eq_of_choices,
      ``PropertyF.Ground.Dimensions.target_globalDimension_independent_simples,
      ``PropertyF.Ground.simple_strand_inclusion,
      ``PropertyF.Ground.weaklyIntegral_of_globalFPDimension_fixed,
      ``PropertyF.Ground.galois_propertyF,
      ``PropertyF.Ground.target_of_galois_invariance_and_pseudo_fixedness,
      ``PropertyF.Ground.target_of_pseudo_fixedness,
      ``PropertyF.Ground.galois_fixed_of_smaller_conjugate_witness,
      ``PropertyF.Ground.target_of_numerical_witnesses,
      ``PropertyF.Ground.target_of_bounded_conjugates_and_witness,
      ``PropertyF.Ground.Modular.conjugate_globalFPDimension,
      ``PropertyF.Ground.fpSimple_eq_fpCharacter,
      ``PropertyF.Ground.fpSimple_mul,
      ``PropertyF.Ground.globalFPDimension_presentation,
      ``PropertyF.Ground.sum_simple_presentation,
      ``PropertyF.Ground.hasPseudoUnitaryGaloisConjugate_of_pseudoUnitary,
      ``PropertyF.Ground.Dimensions.squaredNorm_independent] do
    if let some issue := findIssue env n then
      throwError "dependency audit failed for ground result {n}: {repr issue}"
  logInfo "Dependency audit passed imported positive and negative fixtures."
