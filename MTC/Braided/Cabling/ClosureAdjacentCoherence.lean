module
public import MTC.Braided.Cabling.ClosureCommonInterface

/-! Local reduction of the common block-flattening coherence problem. -/

@[expose] public noncomputable section
open CategoryTheory
namespace MTC.Braided
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C] [Abelian C]

/-- It suffices to compare the flattenings at consecutive generator positions. -/
theorem common_flattening_of_adjacent (X : C) (k n : ℕ)
    (h : ∀ i : Fin n, localBlockFlattenAt X k n i.castSucc =
      localBlockFlattenAt X k n i.succ) :
    ∃ e, ∀ i : Fin (n+1), localBlockFlattenAt X k n i = e := by
  refine ⟨localBlockFlattenAt X k n 0, ?_⟩
  intro i
  induction i using Fin.induction with
  | zero => rfl
  | succ i ih => exact (h i).symm.trans ih

/-- Neighboring-position coherence for every block count gives property F
for the corresponding positive tensor power. -/
theorem objectPropertyF_power_of_adjacent_coherence (X : C) (hX : ObjectPropertyF X)
    (k : ℕ)
    (h : ∀ n, ∀ i : Fin n, localBlockFlattenAt X k n i.castSucc =
      localBlockFlattenAt X k n i.succ) :
    ObjectPropertyF (tensorPower X (k+1)) := by
  apply objectPropertyF_power_of_common_flattening X hX k
  intro n
  exact common_flattening_of_adjacent X k n (h n)

end MTC.Braided
