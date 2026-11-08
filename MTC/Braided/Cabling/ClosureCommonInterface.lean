module
public import MTC.Braided.Cabling.ClosureReindex
public import MTC.Braided.Cabling.ClosureImage

/-! Exact common-flattening interface for tensor-power property F. -/

@[expose] public noncomputable section
open CategoryTheory
namespace MTC.Braided
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C] [Abelian C]

/-- The prefix and suffix block counts sum to the generator index bound. -/
theorem localPosition_sum (n : ℕ) (i : Fin (n+1)) : (n-i.val)+i.val = n :=
  Nat.sub_add_cancel (Nat.le_of_lt_succ i.isLt)

/-- The local position-adapted flattening, transported to a fixed common
source and target for all generators on n+2 equal-width blocks. -/
def localBlockFlattenAt (X : C) (k n : ℕ) (i : Fin (n+1)) :
    tensorPower (tensorPower X (k+1)) (n+2) ≅
      tensorPower X (((n+2)*(k+1)-2)+2) :=
  powerIndexIso (tensorPower X (k+1))
      (congrArg (fun z => z+2) (localPosition_sum n i).symm) ≪≫
    localBlockFlattenCommon X k i.val (n-i.val) ≪≫
      powerIndexIso X (congrArg (fun z => (((z+2)*(k+1)-2)+2)) (localPosition_sum n i))

/-- The explicit local block word, transported to the same common strand count. -/
def localBlockWordAt (k n : ℕ) (i : Fin (n+1)) : BraidWords ((n+2)*(k+1)-2) :=
  cast (congrArg (fun z => BraidWords (((z+2)*(k+1))-2)) (localPosition_sum n i))
    (localBlockWord k i.val (n-i.val))

set_option backward.isDefEq.respectTransparency false in
/-- Each position-adapted flattening conjugates its generator to its explicit
original-strand word, in the common source and target types. -/
theorem localBlockFlattenAt_word (X : C) (k n : ℕ) (i : Fin (n+1)) :
    (localBlockFlattenAt X k n i).conjAut (braidGenerator (tensorPower X (k+1)) n i) =
      (braidWordAction X ((n+2)*(k+1)-2) (localBlockWordAt k n i)).val := by
  simp only [localBlockFlattenAt, Iso.trans_conjAut]
  let h := (localPosition_sum n i).symm
  have hi : Fin.cast (congrArg (fun z => z+1) h) i =
      localBlockPosition i.val (n-i.val) := by
    apply Fin.ext
    rfl
  have hg := braidGenerator_reindex (tensorPower X (k+1)) h i
  rw [hi] at hg
  rw [hg, localBlockFlattenCommon_word]
  unfold localBlockWordAt
  rw [braidWordAction_cast X (congrArg (fun z => ((z+2)*(k+1))-2) (localPosition_sum n i))]

/-- If the independently constructed local flattenings agree for a fixed
block count, the actual block braid image is finite. -/
theorem finite_power_braidImage_of_common_flattening (X : C) (k n : ℕ)
    (e : tensorPower (tensorPower X (k+1)) (n+2) ≅
      tensorPower X (((n+2)*(k+1)-2)+2))
    (he : ∀ i, localBlockFlattenAt X k n i = e)
    [Finite (braidImage X ((n+2)*(k+1)-2))] :
    Finite (braidImage (tensorPower X (k+1)) n) := by
  apply finite_braidImage_of_generator_words X (tensorPower X (k+1)) n
    ((n+2)*(k+1)-2) e (localBlockWordAt k n)
  intro i
  rw [← he i]
  exact localBlockFlattenAt_word X k n i

/-- Common-flattening coherence for every block count is sufficient for
property F of every positive tensor power. -/
theorem objectPropertyF_power_of_common_flattening (X : C) (hX : ObjectPropertyF X)
    (k : ℕ)
    (he : ∀ n, ∃ e : tensorPower (tensorPower X (k+1)) (n+2) ≅
      tensorPower X (((n+2)*(k+1)-2)+2), ∀ i, localBlockFlattenAt X k n i = e) :
    ObjectPropertyF (tensorPower X (k+1)) := by
  intro n
  obtain ⟨e, he⟩ := he n
  letI := hX ((n+2)*(k+1)-2)
  exact finite_power_braidImage_of_common_flattening X k n e he

end MTC.Braided
