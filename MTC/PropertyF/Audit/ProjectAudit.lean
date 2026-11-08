module
public meta import MTC.PropertyF.Audit.DependencyAudit
public import MTC.Fusion.UnitScalar
public import MTC.PropertyF.Theorem
public import MTC.Modular.FusionTransport
public import MTC.Fusion.Reciprocity
public import MTC.Modular.Classification
public import MTC.Braided.Cabling.Strands



















import all MTC.PropertyF.Pivotal.Centralizer
import all MTC.Algebra.ComplexTraceReciprocity
import all MTC.Braided.Cabling.ClosurePure
import all MTC.Braided.Trace.MonodromyReciprocity
import all MTC.Braided.Trace.SaturationSquare
import all MTC.Center.Braid.PivotalRegularSupport
import all MTC.Center.Normalization.PivotalTwist
import all MTC.PropertyF.Pivotal.SlopeSquare
import all MTC.Algebra.ComplexBlockTrace
import all MTC.Algebra.ComplexBraidSaturation
import all MTC.Braided.Trace.ComplexSaturation
import all MTC.Braided.Trace.ComplexTraceBound
import all MTC.Braided.Trace.InverseMonodromy
import all MTC.Braided.Trace.MonodromyBound
import all MTC.Center.Induction.PivotalFusion
import all MTC.Center.Induction.PivotalSquare
import all MTC.Center.Normalization.CharacterExtension
import all MTC.PropertyF.Pivotal.FPGlobalDimension
import all MTC.PropertyF.Pivotal.FPObject
import all MTC.PropertyF.Pivotal.Galois
import all MTC.PropertyF.Pivotal.InfiniteImages
import all MTC.PropertyF.Pivotal.SOrthogonality
import all MTC.PropertyF.Pivotal.SlopeDefect
import all MTC.PropertyF.Pivotal.Statement
import all MTC.Algebra.Arithmetic
import all MTC.Algebra.PowerBound
import all MTC.AnyonAtlas.Raw
import all MTC.AnyonAtlas.Sample
import all MTC.Braided.BraidAlgebra
import all MTC.Braided.Cabling.Generated
import all MTC.Braided.Cabling.Naturality
import all MTC.Braided.Cabling.Strands
import all MTC.Braided.Cabling.UnitPower
import all MTC.Braided.Definitions
import all MTC.Braided.Trace.BraidWeights
import all MTC.Braided.Trace.EndBlocks
import all MTC.Braided.Trace.OverlapBound
import all MTC.Braided.Trace.OverlapCoherence
import all MTC.Braided.Trace.PartialTrace
import all MTC.Braided.Trace.PositiveWeights
import all MTC.Braided.Trace.RightStrand
import all MTC.Braided.Trace.TensorPowerCoherence
import all MTC.Braided.Trace.ThreeRigidity
import all MTC.Braided.Trace.ThreeTrace
import all MTC.Braided.Trace.UnitaryBlocks
import all MTC.Algebra.BlockTrace
import all MTC.CategoryTheory.Dimensions.BiproductTrace
import all MTC.CategoryTheory.Dimensions.DefectExtension
import all MTC.CategoryTheory.Dimensions.DefectNaturality
import all MTC.CategoryTheory.Dimensions.DimensionCharacter
import all MTC.CategoryTheory.Dimensions.DoubleDualMonoidal
import all MTC.CategoryTheory.Dimensions.DoubleDualPairing
import all MTC.CategoryTheory.Dimensions.DoubleDualUnitTensor
import all MTC.CategoryTheory.Dimensions.DualBraiding
import all MTC.CategoryTheory.Dimensions.DualCoherence
import all MTC.CategoryTheory.Dimensions.DualTensorNaturality
import all MTC.CategoryTheory.Dimensions.ENOMatrices
import all MTC.CategoryTheory.Dimensions.ENOReciprocity
import all MTC.CategoryTheory.Dimensions.FourthDualUnit
import all MTC.CategoryTheory.Dimensions.FourthTensorUnit
import all MTC.CategoryTheory.Dimensions.SquaredNorm
import all MTC.CategoryTheory.Dimensions.MonodromyTensorCap
import all MTC.CategoryTheory.Dimensions.MultiplicityDefect
import all MTC.CategoryTheory.Dimensions.Pivotal
import all MTC.CategoryTheory.Dimensions.RootDualLabel
import all MTC.CategoryTheory.Dimensions.SimpleHomBasis
import all MTC.CategoryTheory.Dimensions.SimpleScalars
import all MTC.CategoryTheory.Dimensions.TensorExtension
import all MTC.CategoryTheory.Dimensions.TensorMultiplicativity
import all MTC.CategoryTheory.Dimensions.Trace
import all MTC.Center.Abelian
import all MTC.Center.Averaging
import all MTC.Center.Balancing.TwistBalancing
import all MTC.Center.Basic
import all MTC.Center.Braid.CentralityClosure
import all MTC.Center.Braid.ImageCore
import all MTC.Center.Braid.RegularSupport
import all MTC.Center.Braid.TraceSaturation
import all MTC.Center.Braid.TwistFinite
import all MTC.Center.BraidWords.TypeA
import all MTC.Center.BraidWords.TypeANormalWords
import all MTC.Center.Dimensions.PivotalTwist
import all MTC.Center.Fusion.Fusion
import all MTC.Center.Helpers
import all MTC.Center.Induction.ActualFusion
import all MTC.Center.Induction.AdjunctionAssembly
import all MTC.Center.Induction.BasisPairing
import all MTC.Center.Induction.CrossingBlocks
import all MTC.Center.Induction.CrossingCoherence
import all MTC.Center.Induction.CrossingUnit
import all MTC.Center.Induction.DrinfeldTheorem
import all MTC.Center.Induction.FiniteSimples
import all MTC.Center.Induction.ForgetDual
import all MTC.Center.Induction.ForgetDualTensor
import all MTC.Center.Induction.PivotalCentrality
import all MTC.Center.Induction.PositivePivotal
import all MTC.Center.Induction.Representatives
import all MTC.Center.Induction.SecondTriangle
import all MTC.Center.Modular.TransparencyCriterion
import all MTC.Center.Modular.Vafa
import all MTC.Center.Product
import all MTC.Center.ProductClosure
import all MTC.Center.ProductImages
import all MTC.Center.Rigid
import all MTC.Center.SymmetricIntegrality
import all MTC.Center.Trace.BraidRelations
import all MTC.Center.Trace.LeftTensorTrace
import all MTC.Center.Trace.ParityDeletion
import all MTC.Center.Trace.PermutationInsert
import all MTC.Center.Trace.ProjectorReduction
import all MTC.Center.Trace.TwistSign
import all MTC.FRSymbols.B11Dimension
import all MTC.FRSymbols.Cyclotomic
import all MTC.FRSymbols.CyclotomicMatrix
import all MTC.FRSymbols.FusionRules
import all MTC.FRSymbols.MatrixGauge
import all MTC.FRSymbols.MatrixSymbols
import all MTC.FRSymbols.Metric
import all MTC.FRSymbols.Pointed
import all MTC.FRSymbols.RootsOfUnity
import all MTC.FRSymbols.ToricCode
import all MTC.FRSymbols.ToricMatrix
import all MTC.FRSymbols.ToricModularData
import all MTC.FRSymbols.Trivial
import all MTC.Fusion.Agreement
import all MTC.Fusion.Multiplicity
import all MTC.Fusion.ObjectDimension
import all MTC.Fusion.Reciprocity
import all MTC.Fusion.SemisimpleSplit
import all MTC.Fusion.Simples
import all MTC.Fusion.SpectralIntegral
import all MTC.Fusion.UnitPower
import all MTC.Modular.BraidFunctor
import all MTC.Modular.BraidIso
import all MTC.Modular.CharacterStar
import all MTC.Modular.Classification
import all MTC.Modular.FusionTransport
import all MTC.Modular.SAdditivity
import all MTC.Modular.SMatrix
import all MTC.Modular.SSquare
import all MTC.Modular.Verlinde
import all MTC.Modular.Data.Basic
import all MTC.Modular.Data.CategoricalS
import all MTC.Fusion.Equivalence
import all MTC.Modular.Data.RepresentationCount
import all MTC.PropertyF.Audit.DependencyAudit
import all MTC.PropertyF.PseudoUnitary
import all MTC.PropertyF.Reduction.ActualCenterReduction
import all MTC.Center.Fusion.Bundled
import all MTC.PropertyF.Reduction.CharacterReality
import all MTC.PropertyF.Reduction.TwistedRigidity
import all MTC.Fusion.UnitScalar
import all MTC.PropertyF.Statement
import all MTC.PropertyF.Theorem

open MTC.Algebra

open MTC.PropertyF.Reduction

open MTC.Fusion

open MTC.Braided

/-! Scan all currently integrated project declarations, including the ground
modules. `MTC.Audit` alone sees only its own imports. -/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut checked : Nat := 0
  for (name, _) in env.constants.toList do
    let projectModule := match env.getModuleIdxFor? name with
      | some idx => env.header.modules[idx.toNat]?.any fun m =>
          m.module.toString == "MTC" || m.module.toString.startsWith "MTC."
      | none => false
    if name.toString.startsWith "MTC." || projectModule then
      if Lean.isExtern env name || (Lean.Compiler.getImplementedBy? env name).isSome then
        throwError "Unexpected foreign implementation in project declaration {name}"
      for ax in ← collectAxioms name do
        unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
          throwError "Unexpected axiom {ax} in project declaration {name}"
      checked := checked + 1
  logInfo m!"Audited {checked} integrated project declarations: no sorryAx or custom axioms."

private def auditFixture (n : Nat) : Nat := n

open Lean Elab Command MTC.DependencyAudit in
run_cmd do
  let env ← getEnv
  let modified ← match Lean.Compiler.setImplementedBy env
      ``auditFixture ``Nat.succ with
    | .ok env => pure env
    | .error err => throwError "could not create foreign-implementation test fixture: {err}"
  match findIssue modified ``auditFixture with
  | some (.foreignImplementation _) => pure ()
  | _ => throwError "dependency audit did not reject a substituted implementation"
  match findIssue env `MTC.AuditMissingFixture with
  | some (.missingDeclaration _) => pure ()
  | _ => throwError "dependency audit did not reject a missing declaration"
  match findIssue env ``MTC.DependencyAudit.hiddenInputWrapper with
  | some (.forbidden n) =>
      unless n == ``MTC.DependencyAudit.ForbiddenFixture do
        throwError "unexpected forbidden fixture dependency {n}"
  | _ => throwError "dependency audit did not inspect an imported definition body"
  match findIssue env ``MTC.DependencyAudit.hiddenProof with
  | some (.forbidden n) =>
      unless n == ``MTC.DependencyAudit.ForbiddenFixture do
        throwError "unexpected forbidden theorem fixture dependency {n}"
  | _ => throwError "dependency audit did not inspect the imported theorem proof"
  for n in #[``MTC.PropertyF.TargetStatement,
      ``MTC.Fusion.unit_algebraMap_bijective,
      ``MTC.PropertyF.Reduction.integral_eq_int_of_complex_galois_fixed,
      ``MTC.Modular.conjugate_propertyF,
      ``MTC.PropertyF.Reduction.galois_fixed_of_smaller_conjugate_witness,
      ``MTC.PropertyF.Reduction.positive_bounded_conjugates_of_fp,
      ``MTC.PropertyF.Reduction.exists_modular_witness,
      ``MTC.PropertyF.Reduction.center_witness_of_categorical_modular_data,
      ``MTC.PropertyF.Reduction.propertyF_of_galois_column,
      ``MTC.Modular.conjugate_globalFPDimension,
      ``MTC.Fusion.fpSimple_eq_fpCharacter,
      ``MTC.Fusion.fpSimple_mul,
      ``MTC.PropertyF.Reduction.ScalarTwist.labels,
      ``MTC.Fusion.fpDimension_functor,
      ``MTC.PropertyF.Reduction.center_forget_fpDimension,
      ``MTC.PropertyF.Reduction.galois_rigidity_of_propertyF,
      ``MTC.PropertyF.Reduction.weaklyIntegral_of_actual_center,
      ``MTC.Center.Induction.liftedPivotalStructure,
      ``MTC.Center.Induction.pivotalComponentsCentral_proved,
      ``MTC.Center.Induction.drinfeld_tensor,
      ``MTC.Center.Balancing.pivotal_balance_of_drinfeld_tensor,
      ``MTC.Center.Induction.center_transparent_simple_iso_unit,
      ``MTC.Center.Modular.categoricalS_det_ne_zero_of_trivial_transparency,
      ``MTC.Center.Trace.actual_symmetricCore_integrality,
      ``MTC.Center.Modular.mixed_monodromy_finite_of_pivotal_balancing,
      ``MTC.Center.Rigid.rigidCenter,
      ``MTC.Center.Balancing.doubleDualTensor_evaluation,
      ``MTC.Center.Balancing.drinfeld_tensor_of_pairing_cap,
      ``MTC.Center.Balancing.balance_of_drinfeld_tensor,
      ``MTC.PropertyF.center_globalDimension_square_of_actual_induction,
      ``MTC.Braided.Trace.actual_rigidity_of_overlap_and_galois_dimensions,
      ``MTC.CategoryTheory.Dimensions.fourthDualRootNaturalSquare_eq,
      ``MTC.PropertyF.Reduction.selfDual_character_galois_real,
      ``MTC.Braided.Trace.exists_unitary_braid_trace_blocks,
      ``MTC.CategoryTheory.Dimensions.squaredNorm_independent] do
    if let some issue := findIssue env n then
      throwError "dependency audit failed for ground result {n}: {repr issue}"
  logInfo "Dependency audit passed imported positive and negative fixtures."
