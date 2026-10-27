module
public import PropertyF.Ground.Cabling.GeneratedFusion
public import PropertyF.Ground.Cabling.CablingFinite
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open scoped BigOperators
@[expose] public noncomputable section
namespace PropertyF.Ground.Cabling
universe v u

/-- The generated fusion category has property F, once its explicit
pure-block cabling identity is established. -/
theorem generatedFusion_hasPropertyF_of_block_membership
    (D : Ground.BraidedFusionCategory.{v,u}) (X : D.Obj) (hX : ObjectPropertyF X)
    (hcable : ∀ (count : ℕ) (k : Fin count → ℕ) (n : ℕ)
      (w : pureWords n) (t : Fin (n + 2) → Fin count),
      powerSumPureBlockAction X k n (powerSum_crossing_permutesBlocks X k n) w t ∈
        braidImageAllSubgroup X (∑ i, k (t i))) :
    HasPropertyF (generatedFusion D X).Obj := by
  intro Y n
  have hY := objectPropertyF_generated_of_block_membership X hX hcable Y.obj Y.property
  letI : Finite (braidImage ((generatedFusionInclusion D X).obj Y) n) := hY n
  exact Finite.of_injective (generatedFusionInclusionBraidImageIso D X Y n)
    (generatedFusionInclusionBraidImageIso D X Y n).injective
end PropertyF.Ground.Cabling
