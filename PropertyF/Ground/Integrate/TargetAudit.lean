module
public import PropertyF.Ground.Final
public meta import PropertyF.Ground.Integrate.DependencyAudit


















import all PropertyF.Ground.CentreInduction.DrinfeldTheorem
import all PropertyF.Ground.Dimensions.MonodromyTensorCap
import all PropertyF.Ground.CentreModular.TransparencyCriterion
import all PropertyF.Ground.CentreCalculus.TwistSign
import all PropertyF.Ground.Centre.Modular.Vafa
import all PropertyF.Ground.CentreCabling.TwistFinite
import all PropertyF.Ground.CentreCalculus.BraidRelations
import all PropertyF.Ground.CentreCalculus.LeftTensorTrace
import all PropertyF.Ground.CentreCalculus.ParityDeletion
import all PropertyF.Ground.CentreCalculus.PermutationInsert
import all PropertyF.Ground.Centre.Calculus.TypeANormalWords
import all PropertyF.Ground.Centre.Calculus.TypeA
import all PropertyF.Ground.CentreInduction.PivotalCentrality
import all PropertyF.Ground.CentreInduction.PositivePivotal
import all PropertyF.Ground.CentreIntegrate.TwistBalancing
import all PropertyF.Ground.Dimensions.DefectExtension
import all PropertyF.Ground.Dimensions.DualBraiding
import all PropertyF.Ground.CentreInduction.ForgetDualUnit
import all PropertyF.Ground.CentreInduction.ForgetDualTensor
import all PropertyF.Ground.Centre.Rigid
import all PropertyF.Ground.CentreCabling.CentralityClosure
import all PropertyF.Ground.CentreCabling.ImageCore
import all PropertyF.Ground.CentreCabling.RegularSupport
import all PropertyF.Ground.CentreCabling.TraceSaturation
import all PropertyF.Ground.CentreCalculus.ProjectorReduction
import all PropertyF.Ground.CentreDimensions.PivotalTwist
import all PropertyF.Ground.CentreInduction.ActualFusion
import all PropertyF.Ground.CentreInduction.AdjunctionAssembly
import all PropertyF.Ground.CentreInduction.BasisPairing
import all PropertyF.Ground.CentreInduction.CrossingBlocks
import all PropertyF.Ground.CentreInduction.CrossingCoherence
import all PropertyF.Ground.CentreInduction.CrossingUnit
import all PropertyF.Ground.CentreInduction.FiniteSimples
import all PropertyF.Ground.CentreInduction.ForgetDual
import all PropertyF.Ground.CentreInduction.InjectiveFusion
import all PropertyF.Ground.CentreInduction.Representatives
import all PropertyF.Ground.CentreInduction.SecondTriangle
import all PropertyF.Ground.CentreInduction.WeakHalfBraiding
import all PropertyF.Ground.Dimensions.DefectNaturality
import all PropertyF.Ground.Dimensions.DoubleDualMonoidal
import all PropertyF.Ground.Dimensions.DoubleDualPairing
import all PropertyF.Ground.Dimensions.DoubleDualUnitTensor
import all PropertyF.Ground.Dimensions.FourthDualUnit
import all PropertyF.Ground.Dimensions.FourthTensorUnit
import all PropertyF.Ground.Dimensions.RootDualLabel
import all PropertyF.Arithmetic
import all PropertyF.BlockTrace
import all PropertyF.BraidAlgebra
import all PropertyF.CenterBasics
import all PropertyF.Definitions
import all PropertyF.Ground.Cabling.Generated
import all PropertyF.Ground.Cabling.Naturality
import all PropertyF.Ground.Cabling.Strands
import all PropertyF.Ground.Cabling.UnitPower
import all PropertyF.Ground.Calculus.BraidWeights
import all PropertyF.Ground.Calculus.EndBlocks
import all PropertyF.Ground.Calculus.OverlapBound
import all PropertyF.Ground.Calculus.OverlapCoherence
import all PropertyF.Ground.Calculus.PartialTrace
import all PropertyF.Ground.Calculus.PositiveWeights
import all PropertyF.Ground.Calculus.RightStrand
import all PropertyF.Ground.Calculus.TensorPowerCoherence
import all PropertyF.Ground.Calculus.ThreeRigidity
import all PropertyF.Ground.Calculus.ThreeTrace
import all PropertyF.Ground.Calculus.UnitaryBlocks
import all PropertyF.Ground.Centre.Abelian
import all PropertyF.Ground.Centre.Averaging
import all PropertyF.Ground.Centre.ProductClosure
import all PropertyF.Ground.Centre.Product
import all PropertyF.Ground.Centre.Basic
import all PropertyF.Ground.Centre.ProductImages
import all PropertyF.Ground.Centre.SymmetricIntegrality
import all PropertyF.Ground.CentreBundle.Fusion
import all PropertyF.Ground.Dimensions.BiproductTrace
import all PropertyF.Ground.Dimensions.DimensionCharacter
import all PropertyF.Ground.Dimensions.DimensionField
import all PropertyF.Ground.Dimensions.DualCoherence
import all PropertyF.Ground.Dimensions.DualTensorNaturality
import all PropertyF.Ground.Dimensions.ENOMatrices
import all PropertyF.Ground.Dimensions.ENOReciprocity
import all PropertyF.Ground.Dimensions.GroundNorm
import all PropertyF.Ground.Dimensions.MultiplicityDefect
import all PropertyF.Ground.Dimensions.Pivotal
import all PropertyF.Ground.Dimensions.SimpleHomBasis
import all PropertyF.Ground.Dimensions.SimpleScalars
import all PropertyF.Ground.Dimensions.TensorExtension
import all PropertyF.Ground.Dimensions.TensorMultiplicativity
import all PropertyF.Ground.Dimensions.Trace
import all PropertyF.Ground.Final
import all PropertyF.Ground.Fusion.Agreement
import all PropertyF.Ground.Fusion.Multiplicity
import all PropertyF.Ground.Fusion.ObjectDimension
import all PropertyF.Ground.Fusion.Reciprocity
import all PropertyF.Ground.Fusion.SemisimpleSplit
import all PropertyF.Ground.Fusion.Simples
import all PropertyF.Ground.Fusion.SpectralIntegral
import all PropertyF.Ground.Fusion.UnitPower
import all PropertyF.Ground.Integrate.ActualCenterReduction
import all PropertyF.Ground.Integrate.CenterBundle
import all PropertyF.Ground.Integrate.CharacterReality
import all PropertyF.Ground.Integrate.DependencyAudit
import all PropertyF.Ground.Integrate.TwistedRigidity
import all PropertyF.Ground.Integrate.UnitScalar
import all PropertyF.Ground.Modular.BraidFunctor
import all PropertyF.Ground.Modular.BraidIso
import all PropertyF.Ground.Modular.CharacterStar
import all PropertyF.Ground.Modular.Classification
import all PropertyF.Ground.Modular.SSquare
import all PropertyF.Ground.Modular.SMatrix
import all PropertyF.Ground.Modular.FusionTransport
import all PropertyF.Ground.Modular.Verlinde
import all PropertyF.Ground.Modular.SAdditivity
import all PropertyF.Ground.Target
import all PropertyF.PowerBound

/-! Explicit final-theorem gate. This module intentionally fails to build until
`PropertyF.Ground.target : PropertyF.Ground.TargetStatement` exists. It is not
part of the ordinary library build while the proof remains under development. -/

open Lean Elab Command PropertyF.Ground.DependencyAudit in
run_cmd do
  let env ← getEnv
  let targetName := `PropertyF.Ground.target
  let some ci := env.find? targetName
    | throwError "Final theorem PropertyF.Ground.target is missing"
  match ci with
  | .thmInfo _ => pure ()
  | _ => throwError "PropertyF.Ground.target must be a theorem"
  match ci.type with
  | .const n _ =>
      unless n == ``PropertyF.Ground.TargetStatement do
        throwError "Final theorem must have exactly the frozen TargetStatement type"
  | _ => throwError "Final theorem must have exactly the frozen TargetStatement type"
  if let some issue := findIssue env targetName then
    throwError "Final theorem dependency audit failed: {repr issue}"
  let axioms ← collectAxioms targetName
  for ax in axioms do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
      throwError "Final theorem depends on forbidden axiom {ax}"
  logInfo m!"Final theorem axiom dependencies: {axioms}"
