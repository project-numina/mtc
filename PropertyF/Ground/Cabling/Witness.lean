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

/-- A homomorphism descends to the image of another homomorphism when the
latter's kernel acts trivially. -/
def imageFactor {G H K : Type*} [Group G] [Group H] [Group K]
    (f : G →* H) (g : G →* K) (h : f.ker ≤ g.ker) : f.range →* K :=
  (QuotientGroup.lift f.ker g h).comp (QuotientGroup.quotientKerEquivRange f).symm.toMonoidHom

@[simp] theorem imageFactor_apply {G H K : Type*} [Group G] [Group H] [Group K]
    (f : G →* H) (g : G →* K) (h : f.ker ≤ g.ker) (x : G) :
    imageFactor f g h (f.rangeRestrict x) = g x := by
  have heq : (QuotientGroup.quotientKerEquivRange f).symm (f.rangeRestrict x) =
      (QuotientGroup.mk x : G ⧸ f.ker) := by
    apply (QuotientGroup.quotientKerEquivRange f).injective
    rw [MulEquiv.apply_symm_apply]
    change f.rangeRestrict x = f.rangeRestrict x
    rfl
  simp [imageFactor, heq]

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
  restriction := imageFactor cable (pureWordAction Y n) hker
  restriction_surjective := by
    intro a
    obtain ⟨w, rfl⟩ := pureWordAction_surjective Y n a
    exact ⟨cable.rangeRestrict w, imageFactor_apply cable (pureWordAction Y n) hker w⟩

end PropertyF
