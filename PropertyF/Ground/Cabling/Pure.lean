module
public import PropertyF.Definitions
public import Mathlib.GroupTheory.FreeGroup.Basic
public import Mathlib.GroupTheory.Index
public import Mathlib.GroupTheory.Perm.Basic

/-! The permutation of a braid word and its finite-index pure image.
The free group represents words in adjacent crossings. Its permutation kernel
is the inverse image of the usual pure braid group; this construction does not
require imposing the braid relations to establish finite index. -/

@[expose] public noncomputable section
open CategoryTheory
namespace PropertyF
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]

/-- Words in the adjacent generators on `n+2` strands. -/
abbrev BraidWords (n : ℕ) := FreeGroup (Fin (n + 1))

/-- The permutation induced by a word of crossings. -/
def strandPermutation (n : ℕ) : BraidWords n →* Equiv.Perm (Fin (n + 2)) :=
  FreeGroup.lift (fun i => Equiv.swap i.castSucc i.succ)

/-- Words whose permutation of strands is the identity. -/
def pureWords (n : ℕ) : Subgroup (BraidWords n) := (strandPermutation n).ker

instance pureWords_finiteIndex (n : ℕ) : (pureWords n).FiniteIndex := by
  unfold pureWords
  infer_instance

/-- Evaluate a word in the actual categorical braid generators. -/
def braidWordAction (X : C) (n : ℕ) : BraidWords n →* braidImage X n :=
  (FreeGroup.lift (braidGenerator X n)).codRestrict (braidImage X n) (by
    intro w
    change (FreeGroup.lift (braidGenerator X n)) w ∈ Subgroup.closure (Set.range (braidGenerator X n))
    rw [← FreeGroup.range_lift_eq_closure]
    exact ⟨w, rfl⟩)

/-- Every element of the categorical braid image is represented by a word. -/
theorem braidWordAction_surjective (X : C) (n : ℕ) :
    Function.Surjective (braidWordAction X n) := by
  intro a
  have ha : a.val ∈ (FreeGroup.lift (braidGenerator X n)).range := by
    rw [FreeGroup.range_lift_eq_closure]
    exact a.property
  obtain ⟨w, hw⟩ := ha
  exact ⟨w, Subtype.ext hw⟩

/-- The image of pure words in the categorical braid image. -/
def pureBraidImage (X : C) (n : ℕ) : Subgroup (braidImage X n) :=
  (pureWords n).map (braidWordAction X n)

/-- The pure image has finite index even if the categorical representation
has a kernel: it is the image of a finite-index subgroup under a surjection. -/
instance pureBraidImage_finiteIndex (X : C) (n : ℕ) :
    (pureBraidImage X n).FiniteIndex := by
  unfold pureBraidImage
  exact Subgroup.FiniteIndex.map_of_surjective (pureWords n) (braidWordAction_surjective X n)

end PropertyF
