module
public import PropertyF.Ground.Integrate.ProjectAudit
public import PropertyF.Ground.Target
public import PropertyF.Ground.Integrate.UnitScalar
public import PropertyF.Ground.Fusion.Integrality
public import PropertyF.Ground.Fusion.Splitting
public import PropertyF.Ground.Fusion.FunctorDimension
public import PropertyF.Ground.Fusion.SemisimpleSplit
public import PropertyF.Ground.Fusion.SubcategoryDimension
public import PropertyF.Consequences
public import PropertyF.Descent
public import PropertyF.Transfer
public import PropertyF.Ground.Calculus.Overlap
public import PropertyF.Ground.Calculus.OverlapTrace
public import PropertyF.Ground.Calculus.ImageMaps
public import PropertyF.Ground.Calculus.BraidTraceBound
public import PropertyF.Ground.Calculus.CategoricalTrace
public import PropertyF.Ground.Calculus.PartialTraceGround
public import PropertyF.Ground.Cabling.Strands
public import PropertyF.Ground.Cabling.Pure
public import PropertyF.Ground.Cabling.Witness
public import PropertyF.Ground.Cabling.Images
public import PropertyF.Ground.Cabling.Generated
public import PropertyF.Ground.Dimensions.DimensionField
public import PropertyF.Ground.Dimensions.FusionDimensionField
public import PropertyF.Ground.Dimensions.TargetDimensionField
public import PropertyF.Ground.Dimensions.Norm
public import PropertyF.Ground.Calculus.StarSpan
public import PropertyF.Ground.Centre.Embeddings
public import PropertyF.Ground.Centre.Linear
public import PropertyF.Ground.Centre.Zero
public import PropertyF.Ground.Centre.Biproduct
public import PropertyF.Ground.Centre.ReverseBraiding
public import PropertyF.Ground.Centre.Product
public import PropertyF.Ground.Centre.ProductImages
public import PropertyF.Ground.Modular.Classification
public import PropertyF.Ground.Modular.BraidIso
public import PropertyF.Ground.Modular.BraidFunctor
public import PropertyF.Ground.Modular.Labels
public import PropertyF.Ground.Modular.FusionTransport
public import PropertyF.Ground.Modular.SMatrix
public import PropertyF.Ground.Modular.GaloisFromVerlinde
public import PropertyF.Ground.Modular.PseudoGalois
public import PropertyF.Ground.Dimensions.Pivotal
public import PropertyF.Ground.Dimensions.DualCoherence
public import PropertyF.Ground.Dimensions.TensorTrace
public import PropertyF.Ground.Dimensions.IteratedTrace
public import PropertyF.Ground.Dimensions.TensorMultiplicativity
public import PropertyF.Ground.Dimensions.Trace
public import PropertyF.Ground.Dimensions.BiproductTrace
public import PropertyF.Ground.Dimensions.CharacterBound
public import PropertyF.Ground.Dimensions.DimensionCharacter
public import PropertyF.Ground.Dimensions.PseudoUnitary
public import PropertyF.Ground.Dimensions.SphericalCriterion
public import PropertyF.Ground.Dimensions.SphericalArithmetic
public import PropertyF.Ground.Dimensions.IntrinsicNonzero
public import PropertyF.Ground.Dimensions.UnitNorm
public import PropertyF.Ground.Dimensions.PositiveSpherical
public import PropertyF.Ground.Dimensions.GroundNorm
public import PropertyF.Ground.Dimensions.GlobalInequality
public import PropertyF.Ground.Cabling.Rigidity
public import PropertyF.Ground.Cabling.DualClosure
public import PropertyF.Ground.Cabling.Inclusion
public import PropertyF.Ground.Cabling.Perron
public import PropertyF.Ground.Cabling.Primitive
public import PropertyF.Ground.Cabling.ENOArithmetic
public import PropertyF.Ground.Cabling.Blocks
public import PropertyF.Ground.Cabling.RetractAction
public import PropertyF.Ground.Cabling.Naturality
public import PropertyF.Ground.Cabling.CableRetract
public import PropertyF.Ground.Cabling.TensorDecomposition
public import PropertyF.Ground.Cabling.PureBlocks
public import PropertyF.Ground.Cabling.CablingDiagram

/-! Formalization of `paper/property-f-simplified.pdf`.
The main theorem is `PropertyF.propertyF_implies_weaklyIntegral`.
Its explicit standard-input and realization assumptions are in `PropertyF.Axioms`.
See `FORMALIZATION.md` for the complete assumption ledger.
-/

public import PropertyF.Ground.Calculus.ThreeTrace
public import PropertyF.Ground.Calculus.OverlapUnitary
