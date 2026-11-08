module
public import MTC.Braided.Cabling.ClosureFlattenConcat
public import MTC.Braided.Cabling.ClosureUnit

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace MTC.Braided
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C] [Abelian C]

set_option backward.isDefEq.respectTransparency false in
/-- The first-block flattening with any suffix is the standard flattening. -/
theorem firstBlockFlattenIndexed_heq (X : C) (k q : ℕ) :
    firstBlockFlattenIndexed X k q ≍ flattenPower X (k+1) (strandSum 2 q) := by
  have hc := flattenPower_concat_heq X (k+1) 2 q
  have hl := insertRightPowerIso_heq_join (tensorPower X (k+1)) 0 q
  have hr := insertRightPowerIso_heq_join X (k+k) (q*(k+1))
  have ht := twoBlockFlatten_heq_flattenPower X k
  apply HEq.trans _ hc.symm
  simp only [firstBlockFlattenIndexed]
  congr 2
  all_goals try simp [strandSum_eq_add, tensorPower, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, Nat.succ_mul]
  all_goals try (exact hr.trans (by congr 1; omega))
  all_goals congr 1
  all_goals try exact ht
  all_goals try omega
  all_goals
    have h : 2*(k+1) = (k+k)+2 := by omega
    rw [h]
    rfl

set_option backward.isDefEq.respectTransparency false in
/-- Any position-adapted local flattening is the standard block flattening. -/
theorem localBlockFlatten_heq (X : C) (k p q : ℕ) :
    localBlockFlatten X k p q ≍
      flattenPower X (k+1) (strandSum p (strandSum 2 q)) := by
  have hc := flattenPower_concat_heq X (k+1) p (strandSum 2 q)
  have hl := insertLeftPowerIso_heq_join (tensorPower X (k+1)) (0+q) p
  have hr := insertLeftPowerIso_heq_join X ((k+k)+(q*(k+1))) (p*(k+1))
  have ht := firstBlockFlattenIndexed_heq X k q
  apply HEq.trans _ hc.symm
  simp only [localBlockFlatten]
  congr 2
  all_goals try omega
  all_goals try (exact hl.trans (by congr 1; simp [strandSum_eq_add]; omega))
  all_goals try (exact hr.trans (by congr 1; simp [strandSum_eq_add, Nat.add_mul]; omega))
  all_goals try (congr 1; exact ht)
  all_goals try (simp only [strandSum_eq_add, Nat.add_mul, Trace.braidTensorPower]; omega)
  all_goals try (simp only [strandSum_eq_add, Nat.add_mul, Trace.braidTensorPower]; congr 2 <;> omega)
  all_goals try (congr 1; exact ht)
  all_goals try (apply congrArg (tensorPower _); simp only [strandSum_eq_add, Nat.add_mul]; omega)
  all_goals try (change tensorPower _ _ = tensorPower _ _; apply congrArg (tensorPower _); simp only [strandSum_eq_add]; omega)
  all_goals try (congr 1; try exact ht; try (apply congrArg (tensorPower _); simp only [strandSum_eq_add, Nat.add_mul]; omega))
  all_goals try (apply congrArg (tensorPower _); simp only [strandSum_eq_add, Nat.add_mul]; omega)
  all_goals try (change tensorPower _ _ = tensorPower _ _; apply congrArg (tensorPower _); simp only [strandSum_eq_add]; omega)

/-- Source transport does not change an isomorphism heterogeneously. -/
theorem eqToIso_trans_heq {A B D : C} (h : A = B) (f : B ≅ D) :
    eqToIso h ≪≫ f ≍ f := by
  cases h
  simp

set_option backward.isDefEq.respectTransparency false in
/-- Every position uses one and the same standard block flattening. -/
theorem localBlockFlattenAt_heq (X : C) (k n : ℕ) (i : Fin (n+1)) :
    localBlockFlattenAt X k n i ≍ flattenPower X (k+1) (n+2) := by
  unfold localBlockFlattenAt localBlockFlattenCommon
  simp only [powerIndexIso]
  apply HEq.trans (eqToIso_trans_heq _ _) ?_
  apply HEq.trans (iso_trans_eqToIso_heq _ _) ?_
  apply HEq.trans (eqToIso_trans_heq _ _) ?_
  apply HEq.trans (iso_trans_eqToIso_heq _ _) ?_
  apply HEq.trans (localBlockFlatten_heq X k i.val (n-i.val))
  congr 1
  simp only [strandSum_eq_add]
  have hi := i.isLt
  omega

/-- The position-adapted flattenings coincide for all generators. -/
theorem localBlockFlattenAt_eq (X : C) (k n : ℕ) (i j : Fin (n+1)) :
    localBlockFlattenAt X k n i = localBlockFlattenAt X k n j :=
  eq_of_heq ((localBlockFlattenAt_heq X k n i).trans (localBlockFlattenAt_heq X k n j).symm)

/-- Property F passes to every positive tensor power. -/
theorem objectPropertyF_positive_power (X : C) (hX : ObjectPropertyF X) (k : ℕ) :
    ObjectPropertyF (tensorPower X (k+1)) := by
  apply objectPropertyF_power_of_common_flattening X hX k
  intro n
  exact ⟨localBlockFlattenAt X k n 0, fun i => localBlockFlattenAt_eq X k n i 0⟩

/-- Property F passes to every nonnegative tensor power, including the unit. -/
theorem objectPropertyF_tensorPower (X : C) (hX : ObjectPropertyF X) : ∀ k : ℕ,
    ObjectPropertyF (tensorPower X k)
  | 0 => objectPropertyF_tensorPower_zero X
  | k+1 => objectPropertyF_positive_power X hX k
