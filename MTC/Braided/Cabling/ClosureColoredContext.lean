module
public import MTC.Braided.Cabling.ClosureColoredWords

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace MTC.Braided
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- Flatten three consecutive blocks by joining the last two first. -/
def rightTripleFlatten (X : C) (a b t : ℕ) :
    tensorPower X a ⊗ (tensorPower X b ⊗ tensorPower X t) ≅
      tensorPower X (strandSum a (strandSum b t)) :=
  (Iso.refl (tensorPower X a) ⊗ᵢ joinPowerIso X b t) ≪≫
    joinPowerIso X a (strandSum b t)

/-- Flatten three consecutive blocks by joining the first two first. -/
def leftTripleFlatten (X : C) (a b t : ℕ) :
    (tensorPower X a ⊗ tensorPower X b) ⊗ tensorPower X t ≅
      tensorPower X (strandSum (strandSum a b) t) :=
  (joinPowerIso X a b ⊗ᵢ Iso.refl (tensorPower X t)) ≪≫
    joinPowerIso X (strandSum a b) t

/-- Either grouping gives the same flattening, with the canonical associator. -/
theorem leftTripleFlatten_heq (X : C) (a b t : ℕ) :
    leftTripleFlatten X a b t ≍
      (α_ (tensorPower X a) (tensorPower X b) (tensorPower X t)) ≪≫
        rightTripleFlatten X a b t := by
  have ht := iso_trans_eqToIso_heq (leftTripleFlatten X a b t)
    (congrArg (tensorPower X) (strandSum_assoc a b t))
  have ha := joinPowerIso_assoc X a b t
  rw [← Iso.trans_assoc] at ha
  change leftTripleFlatten X a b t ≪≫ _ =
    (α_ (tensorPower X a) (tensorPower X b) (tensorPower X t)) ≪≫
      rightTripleFlatten X a b t at ha
  exact ht.symm.trans (heq_of_eq ha)

set_option backward.isDefEq.respectTransparency false in
/-- A crossing of the first two blocks can be evaluated after grouping them,
with the third block carried along unchanged. -/
theorem rightTripleCross_heq (X : C) (a b t : ℕ) [BraidedCategory C] :
    ((rightTripleFlatten X a b t).symm ≪≫
      (α_ (tensorPower X a) (tensorPower X b) (tensorPower X t)).symm ≪≫
      ((β_ (tensorPower X a) (tensorPower X b)) ⊗ᵢ Iso.refl (tensorPower X t)) ≪≫
      (α_ (tensorPower X b) (tensorPower X a) (tensorPower X t)) ≪≫
      rightTripleFlatten X b a t) ≍
    ((leftTripleFlatten X a b t).symm ≪≫
      ((β_ (tensorPower X a) (tensorPower X b)) ⊗ᵢ Iso.refl (tensorPower X t)) ≪≫
      leftTripleFlatten X b a t) := by
  have ha := leftTripleFlatten_heq X a b t
  have hb := leftTripleFlatten_heq X b a t
  have hc : ((rightTripleFlatten X a b t).symm ≪≫
      (α_ (tensorPower X a) (tensorPower X b) (tensorPower X t)).symm ≪≫
      ((β_ (tensorPower X a) (tensorPower X b)) ⊗ᵢ Iso.refl (tensorPower X t)) ≪≫
      (α_ (tensorPower X b) (tensorPower X a) (tensorPower X t)) ≪≫
      rightTripleFlatten X b a t) =
    (((α_ (tensorPower X a) (tensorPower X b) (tensorPower X t)) ≪≫
        rightTripleFlatten X a b t).symm ≪≫
      ((β_ (tensorPower X a) (tensorPower X b)) ⊗ᵢ Iso.refl (tensorPower X t)) ≪≫
      ((α_ (tensorPower X b) (tensorPower X a) (tensorPower X t)) ≪≫
        rightTripleFlatten X b a t)) := by
    apply Iso.ext
    simp [Iso.trans_hom, Iso.trans_inv, Category.assoc]
  apply HEq.trans (heq_of_eq hc)
  congr 2
  all_goals try exact ha.symm
  all_goals try exact hb.symm
  all_goals simp [strandSum_eq_add, Nat.add_assoc]

set_option backward.isDefEq.respectTransparency false in
/-- Grouped crossing is a flattened two-block crossing with an identity suffix. -/
theorem leftTripleCross_eq (X : C) (a b t : ℕ) [BraidedCategory C] :
    ((leftTripleFlatten X a b t).symm ≪≫
      ((β_ (tensorPower X a) (tensorPower X b)) ⊗ᵢ Iso.refl (tensorPower X t)) ≪≫
      leftTripleFlatten X b a t) =
    ((joinPowerIso X (strandSum a b) t).symm ≪≫
      (((joinPowerIso X a b).symm ≪≫ β_ (tensorPower X a) (tensorPower X b) ≪≫
        joinPowerIso X b a) ⊗ᵢ Iso.refl (tensorPower X t)) ≪≫
      joinPowerIso X (strandSum b a) t) := by
  apply Iso.ext
  simp only [leftTripleFlatten, Iso.trans_hom, Iso.symm_hom, Iso.trans_inv,
    tensorIso_hom, tensorIso_inv, Iso.refl_hom, Iso.refl_inv, tensorHom_id,
    Category.assoc]
  monoidal

set_option backward.isDefEq.respectTransparency false in
/-- Flatten a tuple by first flattening its suffix and then its three blocks. -/
theorem heterogeneousPowerFlatten_head_two (X : C) {n : ℕ} (k : Fin (n+2) → ℕ) :
    heterogeneousPowerFlatten X (n+2) k =
      (Iso.refl (tensorPower X (k 0)) ⊗ᵢ
        (Iso.refl (tensorPower X (k 1)) ⊗ᵢ
          heterogeneousPowerFlatten X n (fun i => k i.succ.succ))) ≪≫
        rightTripleFlatten X (k 0) (k 1)
          (heterogeneousStrandCount n (fun i => k i.succ.succ)) := by
  apply Iso.ext
  simp only [heterogeneousPowerFlatten, heterogeneousStrandCount, rightTripleFlatten,
    Iso.trans_hom, tensorIso_hom, Iso.refl_hom, id_tensorHom, whiskerLeft_comp, Category.assoc]
  congr 1

/-- The zeroth colored generator braids the first two colors and fixes the tail. -/
theorem coloredGenerator_zero (n : ℕ) [BraidedCategory C] (F : Fin (n+2) → C) :
    Cabling.coloredGenerator n 0 F ≍
      (α_ (F 0) (F 1) (Cabling.coloredTensor n (fun i => F i.succ.succ))).symm ≪≫
      ((β_ (F 0) (F 1)) ⊗ᵢ Iso.refl _) ≪≫
      (α_ (F 1) (F 0) (Cabling.coloredTensor n (fun i => F i.succ.succ))) := by
  cases n <;> rfl

/-- The zeroth swap fixes every color in its suffix. -/
theorem coloredSwap_zero_tail (n : ℕ) (i : Fin n) :
    Cabling.coloredSwap n 0 i.succ.succ = i.succ.succ := by
  cases n with
  | zero => exact Fin.elim0 i
  | succ n => rfl

set_option backward.isDefEq.respectTransparency false in
/-- Flattening a spectator suffix commutes with crossing the first two factors. -/
theorem firstCross_suffix_cancel [BraidedCategory C] {A B U T P Q : C}
    (f : U ≅ T) (j : A ⊗ (B ⊗ T) ≅ P) (k : B ⊗ (A ⊗ T) ≅ Q) :
    (((Iso.refl A ⊗ᵢ (Iso.refl B ⊗ᵢ f)) ≪≫ j).symm ≪≫
      (α_ A B U).symm ≪≫ ((β_ A B) ⊗ᵢ Iso.refl U) ≪≫ (α_ B A U) ≪≫
      ((Iso.refl B ⊗ᵢ (Iso.refl A ⊗ᵢ f)) ≪≫ k)) =
    (j.symm ≪≫ (α_ A B T).symm ≪≫ ((β_ A B) ⊗ᵢ Iso.refl T) ≪≫
      (α_ B A T) ≪≫ k) := by
  have hn : ((α_ A B U).symm ≪≫ ((β_ A B) ⊗ᵢ Iso.refl U) ≪≫ (α_ B A U)) ≪≫
      (Iso.refl B ⊗ᵢ (Iso.refl A ⊗ᵢ f)) =
      (Iso.refl A ⊗ᵢ (Iso.refl B ⊗ᵢ f)) ≪≫
        ((α_ A B T).symm ≪≫ ((β_ A B) ⊗ᵢ Iso.refl T) ≪≫ (α_ B A T)) := by
    apply Iso.ext
    have h := Cabling.colored_first_map (𝟙 A) (𝟙 B) f.hom
    simpa only [Iso.trans_hom, tensorIso_hom, Iso.refl_hom, id_tensorHom] using h
  have hnₖ := congrArg (fun t => t ≪≫ k) hn
  simp only [Iso.trans_symm, Iso.trans_assoc] at hnₖ ⊢
  rw [hnₖ]
  simp only [Iso.symm_self_id_assoc]


/-- The zeroth swap exchanges the first two colors. -/
theorem coloredSwap_zero_head (n : ℕ) :
    Cabling.coloredSwap n 0 0 = 1 ∧ Cabling.coloredSwap n 0 1 = 0 := by
  cases n <;> exact ⟨rfl, rfl⟩

/-- The colored flattening differs from recursive tuple flattening only by
source and target index transports. -/
theorem coloredTensorPowersFlatten_heq (X : C) [BraidedCategory C] [Abelian C]
    {n : ℕ} (k : Fin n → ℕ) :
    coloredTensorPowersFlatten X n k ≍ heterogeneousPowerFlatten X n k := by
  unfold coloredTensorPowersFlatten heterogeneousPowerFlattenSum
  simp only [powerIndexIso]
  exact (eqToIso_trans_heq _ _).trans (iso_trans_eqToIso_heq _ _)


/-- The actual colored tuple flattening starts with the first two blocks,
followed by the flattening of all remaining colors. -/
theorem coloredFlatten_head_two_heq (X : C) [BraidedCategory C] [Abelian C]
    {n : ℕ} (k : Fin (n+2) → ℕ) :
    coloredTensorPowersFlatten X (n+2) k ≍
      (Iso.refl (tensorPower X (k 0)) ⊗ᵢ
        (Iso.refl (tensorPower X (k 1)) ⊗ᵢ
          heterogeneousPowerFlatten X n (fun i => k i.succ.succ))) ≪≫
        rightTripleFlatten X (k 0) (k 1)
          (heterogeneousStrandCount n (fun i => k i.succ.succ)) :=
  (coloredTensorPowersFlatten_heq X k).trans
    (heq_of_eq (heterogeneousPowerFlatten_head_two X k))

set_option backward.isDefEq.respectTransparency false in
/-- The swapped tuple has the same suffix, with its first two blocks exchanged. -/
theorem coloredFlatten_swap_zero_heq (X : C) [BraidedCategory C] [Abelian C]
    {n : ℕ} (k : Fin (n+2) → ℕ) :
    coloredTensorPowersFlatten X (n+2) (fun i => k (Cabling.coloredSwap n 0 i)) ≍
      (Iso.refl (tensorPower X (k 1)) ⊗ᵢ
        (Iso.refl (tensorPower X (k 0)) ⊗ᵢ
          heterogeneousPowerFlatten X n (fun i => k i.succ.succ))) ≪≫
        rightTripleFlatten X (k 1) (k 0)
          (heterogeneousStrandCount n (fun i => k i.succ.succ)) := by
  have ht : (fun i : Fin n => k (Cabling.coloredSwap n 0 i.succ.succ)) =
      (fun i => k i.succ.succ) := by
    funext i
    rw [coloredSwap_zero_tail]
  have h := coloredFlatten_head_two_heq X (fun i => k (Cabling.coloredSwap n 0 i))
  rw [(coloredSwap_zero_head n).1, (coloredSwap_zero_head n).2, ht] at h
  exact h

set_option backward.isDefEq.respectTransparency false in
/-- The flattened first colored crossing is the crossing of its two blocks
with the flattened tuple suffix carried along. -/
theorem coloredGenerator_zero_flatten_heq (X : C) [BraidedCategory C] [Abelian C]
    (n : ℕ) (k : Fin (n+2) → ℕ) :
    ((coloredTensorPowersFlatten X (n+2) k).symm ≪≫
      Cabling.coloredGenerator n 0 (fun i => tensorPower X (k i)) ≪≫
      coloredTensorPowersFlatten X (n+2) (fun i => k (Cabling.coloredSwap n 0 i))) ≍
    ((rightTripleFlatten X (k 0) (k 1) (heterogeneousStrandCount n (fun i => k i.succ.succ))).symm ≪≫
      (α_ (tensorPower X (k 0)) (tensorPower X (k 1))
        (tensorPower X (heterogeneousStrandCount n (fun i => k i.succ.succ)))).symm ≪≫
      ((β_ (tensorPower X (k 0)) (tensorPower X (k 1))) ⊗ᵢ Iso.refl _) ≪≫
      (α_ (tensorPower X (k 1)) (tensorPower X (k 0))
        (tensorPower X (heterogeneousStrandCount n (fun i => k i.succ.succ)))) ≪≫
      rightTripleFlatten X (k 1) (k 0) (heterogeneousStrandCount n (fun i => k i.succ.succ))) := by
  have hs := coloredFlatten_head_two_heq X k
  have ht := coloredFlatten_swap_zero_heq X k
  have hg := coloredGenerator_zero n (fun i => tensorPower X (k i))
  have hf := coloredTensor_powers_eq X n (fun i => k i.succ.succ)
  have hcancel := firstCross_suffix_cancel
    (heterogeneousPowerFlatten X n (fun i => k i.succ.succ))
    (rightTripleFlatten X (k 0) (k 1) _)
    (rightTripleFlatten X (k 1) (k 0) _)
  rw [← Iso.trans_assoc (α_ (tensorPower X (k 0)) (tensorPower X (k 1))
    (heterogeneousPowerTensor X n (fun i => k i.succ.succ))).symm] at hcancel
  rw [← Iso.trans_assoc ((α_ (tensorPower X (k 0)) (tensorPower X (k 1))
    (heterogeneousPowerTensor X n (fun i => k i.succ.succ))).symm ≪≫
      ((β_ (tensorPower X (k 0)) (tensorPower X (k 1))) ⊗ᵢ Iso.refl _))] at hcancel
  apply HEq.trans _ (heq_of_eq hcancel)
  congr 2
  all_goals try exact hs
  all_goals try exact ht
  all_goals try exact hg
  all_goals try exact hf
  all_goals try simp only [hf]
  all_goals try simp [Cabling.coloredTensor, coloredTensor_powers_eq,
    coloredSwap_zero_tail, (coloredSwap_zero_head n).1, (coloredSwap_zero_head n).2,
    heterogeneousStrandCount_eq_sum, strandSum_eq_add, Fin.sum_univ_succ, Nat.add_comm,
    Nat.add_left_comm, Nat.add_assoc]
  all_goals apply HEq.trans hg
  all_goals congr 2
  all_goals try exact hf
  all_goals try simp only [hf]
  all_goals try rfl
  all_goals congr 1
  all_goals try simp [hf]
  all_goals congr 1
  all_goals exact hf

set_option backward.isDefEq.respectTransparency false in
/-- A positive rectangular crossing followed by an arbitrary strand suffix is
the corresponding explicit right-inserted braid word. -/
theorem leftTripleCross_word_heq (X : C) [BraidedCategory C] [Abelian C]
    (r s t : ℕ) :
    ((leftTripleFlatten X (r+1) (s+1) t).symm ≪≫
      ((β_ (tensorPower X (r+1)) (tensorPower X (s+1))) ⊗ᵢ Iso.refl (tensorPower X t)) ≪≫
      leftTripleFlatten X (s+1) (r+1) t) ≍
    ((braidWordAction X ((s+r)+t) (insertRightWords (s+r) t (blockSweepWord s r))).val).asIso := by
  rw [leftTripleCross_eq]
  have hc := joinCross_word_heq X r s
  have hw := joinSuffix_braidWord_iso X (s+r) t (blockSweepWord s r)
  apply HEq.trans _ (heq_of_eq hw)
  simp only [Iso.trans_symm, powerIndexIso]
  simp only [Iso.trans_assoc]
  apply HEq.trans _ (eqToIso_trans_heq _ _).symm
  all_goals try (apply congrArg (tensorPower X); simp only [strandSum_eq_add]; omega)
  rw [← Iso.trans_assoc, ← Iso.trans_assoc, ← Iso.trans_assoc, ← Iso.trans_assoc]
  apply HEq.trans _ (iso_trans_eqToIso_heq _ _).symm
  congr 2
  all_goals try exact hc
  all_goals try simp [strandSum_eq_add]
  all_goals try omega
  all_goals try (apply congrArg (tensorPower X); simp only [strandSum_eq_add]; omega)
  all_goals try (congr 1; apply congrArg (tensorPower X); simp only [strandSum_eq_add]; omega)
  all_goals try (congr 1; try exact hc; try (congr 1; simp only [strandSum_eq_add]; omega))
  all_goals try omega
  all_goals try (apply congrArg (tensorPower X); simp only [strandSum_eq_add]; omega)
  all_goals try (congr 1; try omega; try (simp only [strandSum_eq_add]; omega))
  all_goals try exact hc
  all_goals try (apply congrArg (tensorPower X); simp only [strandSum_eq_add]; omega)
  all_goals simp only [strandSum_eq_add]
  all_goals omega

/-- The actual first colored generator on positive blocks is the explicit
rectangular braid word with the tuple's original-strand suffix inserted. -/
theorem coloredGenerator_zero_word_heq (X : C) [BraidedCategory C] [Abelian C]
    (n : ℕ) (k : Fin (n+2) → ℕ) (r s : ℕ)
    (h0 : k 0 = r+1) (h1 : k 1 = s+1) :
    ((coloredTensorPowersFlatten X (n+2) k).symm ≪≫
      Cabling.coloredGenerator n 0 (fun i => tensorPower X (k i)) ≪≫
      coloredTensorPowersFlatten X (n+2) (fun i => k (Cabling.coloredSwap n 0 i))) ≍
    ((braidWordAction X ((s+r)+heterogeneousStrandCount n (fun i => k i.succ.succ))
      (insertRightWords (s+r) (heterogeneousStrandCount n (fun i => k i.succ.succ))
        (blockSweepWord s r))).val).asIso := by
  have h := coloredGenerator_zero_flatten_heq X n k
  rw [h0, h1] at h
  exact h.trans ((rightTripleCross_heq X (r+1) (s+1) _).trans
    (leftTripleCross_word_heq X r s _))
