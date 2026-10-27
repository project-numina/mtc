module
public import PropertyF.Ground.Cabling.LocalCable
public import PropertyF.Ground.Cabling.GeneratedF
public import PropertyF.Ground.Cabling.CableRetract
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open scoped BigOperators
@[expose] public noncomputable section
namespace PropertyF
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [Abelian C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
attribute [local instance] Abelian.hasFiniteBiproducts

/-- Pure-word restrictions to every tuple block are actual X braids. -/
theorem powerSum_pureBlock_mem (X : C) (k : Fin count → ℕ) (n : ℕ)
    (w : pureWords n) (t : Fin (n+2) → Fin count) :
    powerSumPureBlockAction X k n (powerSum_crossing_permutesBlocks X k n) w t ∈
      braidImageAllSubgroup X (∑ i, k (t i)) := by
  apply powerSum_pureBlock_mem_of_generators X k n (powerSum_crossing_permutesBlocks X k n)
  exact powerSum_generator_cableHom_of_tuple_crossings X k n (powerSum_tuple_cross_cabled X k n)

/-- Property F passes to every object in the generated fusion subcategory. -/
theorem objectPropertyF_of_generated (X Y : C) (hX : ObjectPropertyF X) (hY : GeneratedBy X Y) :
    ObjectPropertyF Y :=
  objectPropertyF_generated_of_block_membership X hX
    (fun _ k n w t => powerSum_pureBlock_mem X k n w t) Y hY

/-- The actual generated fusion category inherits property F from its generator. -/
theorem Ground.Cabling.generatedFusion_hasPropertyF
    (D : Ground.BraidedFusionCategory.{v,u}) (X : D.Obj) (hX : ObjectPropertyF X) :
    HasPropertyF (Ground.Cabling.generatedFusion D X).Obj :=
  Ground.Cabling.generatedFusion_hasPropertyF_of_block_membership D X hX
    (fun _ k n w t => powerSum_pureBlock_mem X k n w t)

/-- The legacy cabling witness is constructed for every generated object. -/
theorem cablingWitness_generated_nonempty (D : BraidedFusionCategory.{v,u}) (X Y : D.Obj)
    (hY : GeneratedBy X Y) (n : ℕ) : Nonempty (CablingWitness D X Y n) := by
  obtain ⟨count, k, ⟨r⟩⟩ := hY
  let W := sumPowersCablingWitness D X k n (powerSum_crossing_permutesBlocks X k n)
    (powerSum_pureBlock_mem X k n)
  exact ⟨W.of_retract r⟩

/-- Choose the cabling witness constructed for a generated object. -/
def cablingWitness_generated (D : BraidedFusionCategory.{v,u}) (X Y : D.Obj)
    (hY : GeneratedBy X Y) (n : ℕ) : CablingWitness D X Y n :=
  Classical.choice (cablingWitness_generated_nonempty D X Y hY n)
end PropertyF
