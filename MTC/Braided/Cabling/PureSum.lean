module
public import MTC.Braided.Cabling.Naturality
public import Mathlib.GroupTheory.Index

/-! Pure braid words and their actual categorical images. -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.BraidedCategory
namespace MTC.Braided.Cabling
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]

/-- The categorical image of words whose actual strand permutation is trivial. -/
def pureBraidImage (X : C) (n : ℕ) : Subgroup (braidImage X n) :=
  (strandPermutation n).ker.map (braidWordAction X n)

/-- The pure image has finite index in the full categorical braid image. -/
theorem pureBraidImage_finiteIndex (X : C) (n : ℕ) : (pureBraidImage X n).FiniteIndex := by
  letI : ((strandPermutation n).ker).FiniteIndex := inferInstance
  exact Subgroup.FiniteIndex.map_of_surjective ((strandPermutation n).ker) (braidWordAction_surjective X n)

/-- Once the actual pure image is finite, the full categorical image is finite. -/
theorem braidImage_finite_of_pureBraidImage_finite (X : C) (n : ℕ)
    (h : Finite (pureBraidImage X n)) : Finite (braidImage X n) := by
  letI : (pureBraidImage X n).FiniteIndex := pureBraidImage_finiteIndex X n
  exact (Subgroup.finite_iff_finite_and_finiteIndex (pureBraidImage X n)).2 ⟨h, inferInstance⟩

end MTC.Braided.Cabling
end
