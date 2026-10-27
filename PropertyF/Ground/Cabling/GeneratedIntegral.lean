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
    ∃ z : ℤ, Ground.fpDimension D X ^ 2 = z := by
  let F := generatedFusionInclusion D X
  letI : ObjectProperty.IsClosedUnderSubobjects (GeneratedBy X) := {
    prop_of_mono := by
      intro A B f hf hB
      letI : Mono f := hf
      letI : IsSplitMono f := Ground.mono_splits D f
      exact generatedBy_retract hB { i := f, r := retraction f } }
  letI : F.PreservesMonomorphisms :=
    ObjectProperty.preservesMonomorphisms_ι_of_isNormalEpiCategory (GeneratedBy X)
  let Y : (generatedFusion D X).Obj := ⟨X, generatedBy_self X⟩
  letI : Simple (F.obj Y) := by change Simple X; infer_instance
  letI : Simple Y := Functor.simple_of_simple_obj F Y
  obtain ⟨z, hz⟩ := Ground.simple_fpDimension_sq_integer_of_weaklyIntegral
    (generatedFusion D X) hweak Y
  have heq := generatedFusionInclusion_fpDimension D X Y
  change Ground.fpDimension D X = Ground.fpDimension (generatedFusion D X) Y at heq
  exact ⟨z, by rw [heq]; exact hz⟩
end PropertyF.Ground.Cabling
