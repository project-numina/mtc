module
public import MTC.Braided.Cabling.ClosureColoredContext

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace MTC.Braided
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C] [Abelian C]

/-- Reindexing the number of strands preserves a braid word action heterogeneously. -/
theorem braidWordAction_cast_heq (X : C) {a b : ℕ} (h : a = b) (w : BraidWords a) :
    ((braidWordAction X b (cast (congrArg BraidWords h) w)).val).asIso ≍
      ((braidWordAction X a w).val).asIso := by
  cases h
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The first positive colored generator belongs to the actual braid image
on the total number of original strands. -/
theorem coloredPower_first_mem (X : C) (n N : ℕ) (k : ColoredPowerState n (N+2))
    (h0 : 0 < k.val 0) (h1 : 0 < k.val 1) :
    Aut.of ((coloredPowerStateFlatten X n (N+2) k).symm ≪≫
      Cabling.coloredGenerator n 0 (fun i => tensorPower X (k.val i)) ≪≫
      coloredPowerStateFlatten X n (N+2) (coloredPowerSwap n (N+2) 0 k)) ∈ braidImage X N := by
  obtain ⟨r, hr⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt h0)
  obtain ⟨s, hs⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt h1)
  have hh := coloredGenerator_zero_word_heq X n k.val r s hr hs
  let t := heterogeneousStrandCount n (fun i => k.val i.succ.succ)
  have hN : N = (s+r)+t := by
    have hk := k.property
    simp only [Fin.sum_univ_succ, ← heterogeneousStrandCount_eq_sum] at hk
    have hidx : (Fin.succ (0 : Fin (n+1)) : Fin (n+2)) = 1 := by rfl
    rw [hidx, hr, hs] at hk
    dsimp [t]
    omega
  have hsource := iso_trans_eqToIso_heq (coloredTensorPowersFlatten X (n+2) k.val)
    (congrArg (tensorPower X) k.property)
  have htarget := iso_trans_eqToIso_heq
    (coloredTensorPowersFlatten X (n+2) (coloredPowerSwap n (N+2) 0 k).val)
    (congrArg (tensorPower X) (coloredPowerSwap n (N+2) 0 k).property)
  have hiso : ((coloredPowerStateFlatten X n (N+2) k).symm ≪≫
      Cabling.coloredGenerator n 0 (fun i => tensorPower X (k.val i)) ≪≫
      coloredPowerStateFlatten X n (N+2) (coloredPowerSwap n (N+2) 0 k)) ≍
    ((braidWordAction X N (cast (congrArg BraidWords hN.symm)
      (insertRightWords (s+r) t (blockSweepWord s r)))).val).asIso := by
    apply HEq.trans _ (braidWordAction_cast_heq X hN.symm _).symm
    apply HEq.trans _ hh
    simp only [coloredPowerStateFlatten, powerIndexIso]
    congr 2
    all_goals try exact hsource
    all_goals try exact htarget
    all_goals try rfl
    all_goals try exact k.property.symm
    all_goals try exact (coloredPowerSwap n (N+2) 0 k).property.symm
    all_goals try (apply congrArg (tensorPower X); exact k.property.symm)
    all_goals try (apply congrArg (tensorPower X); exact (coloredPowerSwap n (N+2) 0 k).property.symm)
  have heq := eq_of_heq hiso
  change Aut.of _ ∈ braidImage X N
  rw [heq]
  exact (braidWordAction X N (cast (congrArg BraidWords hN.symm)
    (insertRightWords (s+r) t (blockSweepWord s r)))).property
