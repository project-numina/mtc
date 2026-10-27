module
public import PropertyF.Ground.Cabling.CablingComplete
public import PropertyF.Ground.Cabling.GeneratedIntegral
public import PropertyF.Ground.Integrate.LegacyBridge
public import PropertyF.Ground.Integrate.StrandInclusion
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
@[expose] public noncomputable section
namespace PropertyF.Ground.Cabling
universe v u

/-- Every field of the earlier generated-input interface is constructed for a
genuine ground fusion category. This is a compatibility bridge only; the
ground-category theorems do not depend on this legacy structure. -/
def generatedInputsOfGround (D : Ground.BraidedFusionCategory.{v,u}) (X : D.Obj) :
    PropertyF.GeneratedInputs (Ground.legacyCategory D) X where
  cabling := fun Y hY n => ⟨PropertyF.cablingWitness_generated (Ground.legacyCategory D) X Y hY n⟩
  category := Ground.legacyCategory (generatedFusion D X)
  inclusion := generatedFusionInclusion D X
  inclusion_braided := by
    change (generatedInclusion X).Braided
    infer_instance
  inclusion_full := by
    change (generatedInclusion X).Full
    infer_instance
  inclusion_faithful := by
    change (generatedInclusion X).Faithful
    infer_instance
  inclusion_generated := fun Y => Y.property
  generated_essential_image := fun Y hY => (generatedFusionInclusion_essentialImage D X Y).mp hY
  image_equivalence := fun Y n => ⟨generatedFusionInclusionBraidImageIso D X Y n⟩
  simple_square_integral := by
    intro hsimple hweak
    letI : Simple X := hsimple
    change WeaklyIntegral (Ground.globalFPDimension (generatedFusion D X)) at hweak
    change ∃ z : ℤ, Ground.fpDimension D X ^ 2 = z
    exact generated_simple_square_integral D X hweak
  strand_inclusion := by
    intro hsimple n m hnm
    letI : Simple X := hsimple
    exact Ground.simple_strand_inclusion D X n m hnm
end PropertyF.Ground.Cabling
