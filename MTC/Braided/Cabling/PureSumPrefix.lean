module
public import MTC.Braided.Cabling.PureSumPositiveState
public import MTC.Braided.Cabling.ClosureInsertionCompare
public import MTC.Braided.Cabling.ClosureColoredContext
public import MTC.Braided.Cabling.ClosureColoredFirst

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace MTC.Braided.Cabling
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C] [Abelian C]

/-- Prefixing arbitrary original strands sends an element of a braid image
to the larger braid image, via the canonical join. -/
theorem braidImage_prefix_mem (X : C) (n p : ℕ)
    (a : Aut (tensorPower X (n + 2))) (ha : a ∈ braidImage X n) :
    (joinPowerIso X p (n + 2) ≪≫
      powerIndexIso X (by rw [strandSum_eq_add]; omega :
        strandSum p (n + 2) = (n + p) + 2)).conjAut
      ((tensorLeft (tensorPower X p)).mapAut (tensorPower X (n + 2)) a) ∈
        braidImage X (n + p) := by
  obtain ⟨w, hw⟩ := braidWordAction_surjective X n ⟨a, ha⟩
  have hw' := congrArg Subtype.val hw
  change (braidWordAction X n w).val = a at hw'
  rw [← hw', joinPrefix_braidWord]
  exact (braidWordAction X (n + p) _).property

set_option backward.isDefEq.respectTransparency false in
/-- Flattening a colored tuple starts by flattening its tail and joining the
first block. -/
theorem coloredFlatten_head_heq (X : C) (n : ℕ) (k : Fin (n + 1) → ℕ) :
    coloredTensorPowersFlatten X (n + 1) k ≍
      (Iso.refl (tensorPower X (k 0)) ⊗ᵢ
        coloredTensorPowersFlatten X n (fun j => k j.succ)) ≪≫
        joinPowerIso X (k 0) (∑ j : Fin n, k j.succ) := by
  have h := coloredTensorPowersFlatten_heq X (n + 1) k
  have ht := coloredTensorPowersFlatten_heq X n (fun j => k j.succ)
  apply h.trans
  simp only [heterogeneousPowerFlatten]
  congr 2
  all_goals try exact ht.symm
  all_goals try simp [heterogeneousStrandCount_eq_sum, heterogeneousPowerTensor, ← coloredTensor_powers_eq, strandSum_eq_add, Fin.sum_univ_succ]

/-- Flattening an unchanged prefix commutes with a crossing in the tail. -/
theorem prefix_crossing_cancel {A U V T S P Q : C}
    (f : U ≅ T) (g : U ≅ V) (h : V ≅ S)
    (j : A ⊗ T ≅ P) (k : A ⊗ S ≅ Q) :
    ((Iso.refl A ⊗ᵢ f) ≪≫ j).symm ≪≫ (Iso.refl A ⊗ᵢ g) ≪≫
        ((Iso.refl A ⊗ᵢ h) ≪≫ k) =
      j.symm ≪≫ (Iso.refl A ⊗ᵢ (f.symm ≪≫ g ≪≫ h)) ≪≫ k := by
  apply Iso.ext
  simp [Iso.trans_hom, Iso.trans_inv, tensorIso_hom, tensorIso_inv,
    tensorHom_comp_tensorHom, Category.assoc]

set_option backward.isDefEq.respectTransparency false in
/-- A non-first colored generator is the flattened tail generator with the
first tensor-power block prefixed. -/
theorem coloredGenerator_succ_flatten_heq (X : C) (n : ℕ)
    (i : Fin (n + 1)) (k : Fin (n + 3) → ℕ) :
    ((coloredTensorPowersFlatten X (n + 3) k).symm ≪≫
      coloredGenerator (n + 1) i.succ (fun j => tensorPower X (k j)) ≪≫
      coloredTensorPowersFlatten X (n + 3)
        (fun j => k (coloredSwap (n + 1) i.succ j))) ≍
    ((joinPowerIso X (k 0) (∑ j : Fin (n + 2), k j.succ)).symm ≪≫
      (Iso.refl (tensorPower X (k 0)) ⊗ᵢ
        ((coloredTensorPowersFlatten X (n + 2) (fun j => k j.succ)).symm ≪≫
          coloredGenerator n i (fun j => tensorPower X (k j.succ)) ≪≫
          coloredTensorPowersFlatten X (n + 2)
            (fun j => k (coloredSwap n i j).succ))) ≪≫
      joinPowerIso X (k 0) (∑ j : Fin (n + 2), k (coloredSwap n i j).succ)) := by
  have hs := coloredFlatten_head_heq X (n + 2) k
  have ht := coloredFlatten_head_heq X (n + 2)
    (fun j => k (coloredSwap (n + 1) i.succ j))
  have hc := prefix_crossing_cancel
    (coloredTensorPowersFlatten X (n + 2) (fun j => k j.succ))
    (coloredGenerator n i (fun j => tensorPower X (k j.succ)))
    (coloredTensorPowersFlatten X (n + 2) (fun j => k (coloredSwap n i j).succ))
    (joinPowerIso X (k 0) (∑ j : Fin (n + 2), k j.succ))
    (joinPowerIso X (k 0) (∑ j : Fin (n + 2), k (coloredSwap n i j).succ))
  apply HEq.trans _ (heq_of_eq hc)
  simp only [coloredGenerator, coloredSwap, Fin.cases_succ, Fin.cases_zero] at ht ⊢
  congr 2
  all_goals try exact hs
  all_goals try exact ht
  all_goals try rfl
  all_goals try simp [coloredSwap, Fin.cases_succ, Fin.cases_zero, Fin.sum_univ_succ, strandSum_eq_add]

set_option backward.isDefEq.respectTransparency false in
/-- Fixed-total flattening differs from unindexed colored flattening only by
its terminal power-index transport. -/
theorem coloredPowerStateFlatten_heq (X : C) (n N : ℕ) (s : ColoredPowerState n N) :
    coloredPowerStateFlatten X n N s ≍ coloredTensorPowersFlatten X (n + 2) s.val := by
  unfold coloredPowerStateFlatten powerIndexIso
  exact iso_trans_eqToIso_heq _ _

set_option backward.isDefEq.respectTransparency false in
/-- The fixed-total non-first crossing is the prefixed fixed-total tail crossing. -/
theorem coloredPower_succ_prefix_eq (X : C) (n m : ℕ)
    (i : Fin (n + 1)) (k : Fin (n + 3) → ℕ)
    (htail : (∑ j : Fin (n + 2), k j.succ) = m + 2)
    (hfull : (∑ j, k j) = (m + k 0) + 2) :
    let s : ColoredPowerState (n + 1) ((m + k 0) + 2) := ⟨k, hfull⟩
    let t : ColoredPowerState n (m + 2) := ⟨fun j => k j.succ, htail⟩
    Aut.of ((coloredPowerStateFlatten X (n + 1) _ s).symm ≪≫
      coloredLetter (n + 1) i.succ true (fun j => tensorPower X (s.val j)) ≪≫
      coloredPowerStateFlatten X (n + 1) _ (coloredPowerSwap (n + 1) _ i.succ s)) =
    (joinPowerIso X (k 0) (m + 2) ≪≫
      powerIndexIso X (by rw [strandSum_eq_add]; omega :
        strandSum (k 0) (m + 2) = (m + k 0) + 2)).conjAut
      ((tensorLeft (tensorPower X (k 0))).mapAut (tensorPower X (m + 2))
        (Aut.of ((coloredPowerStateFlatten X n (m + 2) t).symm ≪≫
          coloredLetter n i true (fun j => tensorPower X (t.val j)) ≪≫
          coloredPowerStateFlatten X n (m + 2) (coloredPowerSwap n (m + 2) i t)))) := by
  dsimp only
  apply Aut.ext
  apply eq_of_heq
  simp only [Iso.conjAut_apply]
  have hc := coloredGenerator_succ_flatten_heq X n i k
  have hs := coloredPowerStateFlatten_heq X (n + 1) _ ⟨k, hfull⟩
  have ht := coloredPowerStateFlatten_heq X n (m + 2) ⟨fun j => k j.succ, htail⟩
  have hs' := coloredPowerStateFlatten_heq X (n + 1) _
    (coloredPowerSwap (n + 1) _ i.succ ⟨k, hfull⟩)
  have ht' := coloredPowerStateFlatten_heq X n (m + 2)
    (coloredPowerSwap n (m + 2) i ⟨fun j => k j.succ, htail⟩)
  have hswap : (∑ j : Fin (n + 2), k (coloredSwap n i j).succ) = m + 2 := by
    rw [coloredSwap_eq_swap]
    exact (Equiv.sum_comp (Equiv.swap i.castSucc i.succ) (fun j => k j.succ)).trans htail
  have hj : ∀ (b c : ℕ), b = c → HEq (joinPowerIso X (k 0) b) (joinPowerIso X (k 0) c) := by
    intro b c h
    subst c
    rfl
  have hmap {A B : C} (f : A ≅ B) :
      (tensorLeft (tensorPower X (k 0))).mapIso f = Iso.refl _ ⊗ᵢ f := by
    apply Iso.ext
    simp [tensorIso_hom]
  refine HEq.trans ?_ (hc.trans ?_)
  all_goals simp only [coloredLetter, ↓reduceIte, Functor.mapAut, hmap]
  all_goals congr 2
  all_goals try exact hs
  all_goals try exact hs'
  all_goals try exact ht
  all_goals try exact ht'
  all_goals try simp [coloredLetter, coloredPowerSwap, coloredSwap, Fin.cases_succ,
    Fin.cases_zero, powerIndexIso, strandSum_eq_add, Fin.sum_univ_succ, htail, hswap]
  all_goals try omega
  all_goals try (congr 1 <;> omega)
  all_goals try (simpa only [htail, hswap] using (iso_trans_eqToIso_heq _ _).symm)
  all_goals congr 2
  all_goals try exact ht.symm
  all_goals try exact ht'.symm
  all_goals try simp [coloredPowerSwap, htail, hswap]
  all_goals try omega
  all_goals try (congr 1 <;> omega)
  all_goals try (simp only [htail, hswap]; exact (iso_trans_eqToIso_heq _ _).symm)
  all_goals congr 2
  all_goals try exact ht.symm
  all_goals try exact ht'.symm
  all_goals try simp [htail, hswap]
  all_goals try omega
  all_goals try (congr 1 <;> omega)
  all_goals first
    | exact (hj _ _ htail).trans (iso_trans_eqToIso_heq _ _).symm
    | exact (hj _ _ hswap).trans (iso_trans_eqToIso_heq _ _).symm

set_option backward.isDefEq.respectTransparency false in
/-- Every positive-width colored crossing is an actual original-strand braid. -/
theorem coloredPower_positive_mem (X : C) : ∀ (n r : ℕ)
    (s : ColoredPowerState n (r + 2)), (∀ j, 0 < s.val j) → ∀ i : Fin (n + 1),
    Aut.of ((coloredPowerStateFlatten X n (r + 2) s).symm ≪≫
      coloredLetter n i true (fun j => tensorPower X (s.val j)) ≪≫
      coloredPowerStateFlatten X n (r + 2) (coloredPowerSwap n (r + 2) i s)) ∈
        braidImage X r := by
  intro n
  induction n with
  | zero =>
    intro r s hp i
    have hi : i = 0 := Fin.eq_zero i
    subst i
    simpa only [coloredLetter, if_pos] using coloredPower_first_mem X 0 r s (hp 0) (hp 1)
  | succ n ih =>
    intro r s hp i
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa only [coloredLetter, if_pos] using coloredPower_first_mem X (n + 1) r s (hp 0) (hp 1)
    · rcases s with ⟨k, hf⟩
      let m := (∑ t : Fin (n + 2), k t.succ) - 2
      have hge : 2 ≤ ∑ t : Fin (n + 2), k t.succ :=
        two_le_sum_positive_widths n (fun t => k t.succ) (fun t => hp t.succ)
      have ht : (∑ t : Fin (n + 2), k t.succ) = m + 2 :=
        (Nat.sub_add_cancel hge).symm
      have hr : r = m + k 0 := by
        rw [Fin.sum_univ_succ, ht] at hf
        omega
      subst r
      let t : ColoredPowerState n (m + 2) := ⟨fun j => k j.succ, ht⟩
      have hmem := ih m t (fun j => hp j.succ) j
      have hprefix := braidImage_prefix_mem X m (k 0) _ hmem
      rw [coloredPower_succ_prefix_eq X n m j k ht hf]
      exact hprefix

end MTC.Braided.Cabling
end
