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
/-- The first crossing of two positive-width blocks is the explicit
rectangular braid word, transported to the fixed total. -/
theorem coloredPower_first_eq_word (X : C) {n N : ℕ} (k : ColoredPowerState n (N+2))
    {r s : ℕ} (hr : k.val 0 = r + 1) (hs : k.val 1 = s + 1)
    (hN : N = (s+r) + heterogeneousStrandCount n (fun i => k.val i.succ.succ)) :
    Aut.of ((coloredPowerStateFlatten X n (N+2) k).symm ≪≫
      Cabling.coloredGenerator n 0 (fun i => tensorPower X (k.val i)) ≪≫
      coloredPowerStateFlatten X n (N+2) (coloredPowerSwap n (N+2) 0 k)) =
    (braidWordAction X N (cast (congrArg BraidWords hN.symm)
      (insertRightWords (s+r) (heterogeneousStrandCount n (fun i => k.val i.succ.succ))
        (blockSweepWord s r)))).val := by
  have hh := coloredGenerator_zero_word_heq X n k.val r s hr hs
  have hsource := iso_trans_eqToIso_heq (coloredTensorPowersFlatten X (n+2) k.val)
    (congrArg (tensorPower X) k.property)
  have htarget := iso_trans_eqToIso_heq
    (coloredTensorPowersFlatten X (n+2) (coloredPowerSwap n (N+2) 0 k).val)
    (congrArg (tensorPower X) (coloredPowerSwap n (N+2) 0 k).property)
  apply congrArg Aut.of
  apply eq_of_heq
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
  have hN : N = (s+r) + heterogeneousStrandCount n (fun i => k.val i.succ.succ) := by
    have hk := coloredPowerState_total_eq_head_two k
    rw [hr, hs] at hk
    omega
  rw [coloredPower_first_eq_word X k hr hs hN]
  exact (braidWordAction X N _).property
