module
public import PropertyF.Axioms
public import PropertyF.Ground.Cabling.Pure
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-! Construct the quotient portion of the cabling witness from an actual
pure-word cabling map and its kernel compatibility. -/

@[expose] public noncomputable section
open CategoryTheory
open scoped BigOperators
namespace PropertyF
universe v u

/-- Restrict the categorical braid-word action to pure words, with its image
as codomain. -/
def pureWordAction {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
    (X : C) (n : ℕ) : pureWords n →* pureBraidImage X n :=
  ((braidWordAction X n).comp (pureWords n).subtype).codRestrict _ (by
    intro w
    exact ⟨w.val, w.property, rfl⟩)

theorem pureWordAction_surjective {C : Type u} [Category.{v} C] [MonoidalCategory C]
    [BraidedCategory C] (X : C) (n : ℕ) : Function.Surjective (pureWordAction X n) := by
  rintro ⟨a, w, hw, rfl⟩
  exact ⟨⟨w, hw⟩, rfl⟩

/-- The precise remaining diagrammatic input is a homomorphism from pure words
to the product of cabled X-images whose kernel acts trivially on Y. From that
input the quotient and finite-index pieces of `CablingWitness` are constructed. -/
def cablingWitnessOfPureAction (C : BraidedFusionCategory.{v,u}) (X Y : C.Obj) (n : ℕ)
    (blockCount : ℕ) (lengths : Fin blockCount → Fin (n + 2) → ℕ)
    (cable : pureWords n →* ∀ r : Fin blockCount, braidImageAll X (∑ i, lengths r i))
    (hker : cable.ker ≤ (pureWordAction Y n).ker) : CablingWitness C X Y n where
  blockCount := blockCount
  lengths := lengths
  pureImage := pureBraidImage Y n
  finiteIndex := inferInstance
  cableImage := cable.range
  restriction := cable.rangeRestrict.liftOfSurjective cable.rangeRestrict_surjective
    ⟨pureWordAction Y n, by simpa using hker⟩
  restriction_surjective := by
    intro a
    obtain ⟨w, rfl⟩ := pureWordAction_surjective Y n a
    exact ⟨cable.rangeRestrict w, by simp⟩

end PropertyF
