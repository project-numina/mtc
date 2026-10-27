module
public import PropertyF.Ground.Cabling.GeneratedDimension
public import PropertyF.Ground.Fusion.WeakIntegrality
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
@[expose] public noncomputable section
namespace PropertyF.Ground.Cabling
universe v u

/-- Weak integrality of the generated category forces the squared FP dimension
of its simple generator to be integral. -/
theorem generated_simple_square_integral (D : Ground.BraidedFusionCategory.{v,u})
    (X : D.Obj) [Simple X]
    (hweak : WeaklyIntegral (Ground.globalFPDimension (generatedFusion D X))) :
    ∃ z : ℤ, Ground.fpDimension D X ^ 2 = z :=
  Ground.generated_simple_square_integer D X hweak

end PropertyF.Ground.Cabling
