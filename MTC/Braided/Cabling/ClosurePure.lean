module
public import MTC.Braided.Cabling.Naturality

/-! Pure words have finite index. Thus finite action of the pure words suffices
for finiteness of the entire actual categorical braid image. -/

@[expose] public noncomputable section
open CategoryTheory
namespace MTC.Braided
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]

/-- Words inducing the identity strand permutation. -/
def pureBraidWords (n : ℕ) : Subgroup (BraidWords n) := (strandPermutation n).ker

instance (n : ℕ) : (pureBraidWords n).FiniteIndex := by
  unfold pureBraidWords
  exact Subgroup.finiteIndex_ker (strandPermutation n)

/-- If pure words have finite image, all categorical braid words have finite image. -/
theorem finite_braidImage_of_finite_pure (X : C) (n : ℕ)
    [Finite ((pureBraidWords n).map (braidWordAction X n))] :
    Finite (braidImage X n) := by
  let H := (pureBraidWords n).map (braidWordAction X n)
  letI : H.FiniteIndex := Subgroup.FiniteIndex.map_of_surjective (pureBraidWords n) (braidWordAction_surjective X n)
  exact (Subgroup.finite_iff_finite_and_finiteIndex H).2 ⟨inferInstance, inferInstance⟩

end MTC.Braided
