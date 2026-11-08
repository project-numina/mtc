module
public import MTC.Braided.Cabling.PureSumPositiveCabling

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
namespace MTC.Braided.Cabling
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C] [Abelian C]

/-- Swapping positive widths preserves positivity. -/
theorem coloredPowerSwap_positive (n N : ℕ) (i : Fin (n + 1))
    (s : ColoredPowerState n N) (hs : ∀ j, 0 < s.val j) :
    ∀ j, 0 < (coloredPowerSwap n N i s).val j := fun j => hs _

set_option backward.isDefEq.respectTransparency false in
/-- Signed letter membership on positive states lifts to all words from a
positive state. -/
theorem coloredPowerStateWord_mem_of_positive_letters (X : C) (n N : ℕ)
    (G : Subgroup (Aut (tensorPower X N)))
    (h : ∀ (s : ColoredPowerState n N), (∀ j, 0 < s.val j) →
      ∀ (a : Fin (n + 1) × Bool),
      Aut.of ((coloredPowerStateFlatten X n N s).symm ≪≫
        coloredLetter n a.1 a.2 (fun i => tensorPower X (s.val i)) ≪≫
        coloredPowerStateFlatten X n N (coloredPowerSwap n N a.1 s)) ∈ G) :
    ∀ (w : List (Fin (n + 1) × Bool)) (s : ColoredPowerState n N),
      (∀ j, 0 < s.val j) →
      Aut.of ((coloredPowerStateFlatten X n N s).symm ≪≫
        coloredPowerStateWordIso X n N w s ≪≫
        coloredPowerStateFlatten X n N (coloredPowerWordState n N w s)) ∈ G
  | [], s, _ => by
    have hid : Aut.of ((coloredPowerStateFlatten X n N s).symm ≪≫
        Iso.refl _ ≪≫ coloredPowerStateFlatten X n N s) = 1 := by
      apply Aut.ext
      apply Iso.ext
      simp
    change Aut.of ((coloredPowerStateFlatten X n N s).symm ≪≫
      Iso.refl _ ≪≫ coloredPowerStateFlatten X n N s) ∈ G
    rw [hid]
    exact G.one_mem
  | a :: w, s, hs => by
    have ha := h s hs a
    have hw := coloredPowerStateWord_mem_of_positive_letters X n N G h w
      (coloredPowerSwap n N a.1 s) (coloredPowerSwap_positive n N a.1 s hs)
    have hm := G.mul_mem hw ha
    convert hm using 1
    apply Aut.ext
    apply Iso.ext
    simp [coloredPowerStateWordIso, coloredPowerWordState, Iso.trans_hom, Category.assoc]

/-- Positive membership on positive-width states supplies both signs there. -/
theorem coloredPower_positive_letters_mem (X : C) (n N : ℕ)
    (G : Subgroup (Aut (tensorPower X N)))
    (h : ∀ (s : ColoredPowerState n N), (∀ j, 0 < s.val j) →
      ∀ (i : Fin (n + 1)),
      Aut.of ((coloredPowerStateFlatten X n N s).symm ≪≫
        coloredLetter n i true (fun j => tensorPower X (s.val j)) ≪≫
        coloredPowerStateFlatten X n N (coloredPowerSwap n N i s)) ∈ G) :
    ∀ (s : ColoredPowerState n N), (∀ j, 0 < s.val j) →
      ∀ (a : Fin (n + 1) × Bool),
      Aut.of ((coloredPowerStateFlatten X n N s).symm ≪≫
        coloredLetter n a.1 a.2 (fun j => tensorPower X (s.val j)) ≪≫
        coloredPowerStateFlatten X n N (coloredPowerSwap n N a.1 s)) ∈ G := by
  intro s hs ⟨i, b⟩
  cases b with
  | false =>
    rw [coloredPower_negative_eq_inverse]
    exact G.inv_mem (h (coloredPowerSwap n N i s) (coloredPowerSwap_positive n N i s hs) i)
  | true => exact h s hs i

/-- Pure colored words on positive-width tuples are cabled by actual braids
when positive generators on positive-width states are cabled. -/
theorem coloredPureWord_cabling_of_positive_states (X : C) (n r : ℕ)
    (k : Fin (n + 2) → ℕ) (hk : ∑ i, k i = r + 2) (hpos : ∀ j, 0 < k j)
    (hletter : ∀ (s : ColoredPowerState n (r + 2)), (∀ j, 0 < s.val j) →
      ∀ (i : Fin (n + 1)),
      Aut.of ((coloredPowerStateFlatten X n (r + 2) s).symm ≪≫
        coloredLetter n i true (fun j => tensorPower X (s.val j)) ≪≫
        coloredPowerStateFlatten X n (r + 2) (coloredPowerSwap n (r + 2) i s)) ∈ braidImage X r)
    (w : List (Fin (n + 1) × Bool))
    (hw : strandPermutation n (FreeGroup.mk w) = 1) :
    ∃ z : braidImage X r,
      coloredPureWordHom n w hw (fun i => tensorPower X (k i)) =
        (coloredPowerStateFlatten X n (r + 2) ⟨k, hk⟩).hom ≫ z.val.asIso.hom ≫
          (coloredPowerStateFlatten X n (r + 2) ⟨k, hk⟩).inv := by
  let s : ColoredPowerState n (r + 2) := ⟨k, hk⟩
  have hs : coloredPowerWordState n (r + 2) w.reverse s = s := by
    apply Subtype.ext
    rw [coloredPowerWordState_val, coloredWordSwap_reverse_pure n w hw]
    rfl
  have hm := coloredPowerStateWord_mem_of_positive_letters X n (r + 2) (braidImage X r)
    (coloredPower_positive_letters_mem X n (r + 2) (braidImage X r) hletter) w.reverse s hpos

  let z : braidImage X r := ⟨_, hm⟩
  refine ⟨z, ?_⟩
  have he := coloredPowerStateWordIso_heq X n (r + 2) w.reverse s
  let T : ColoredPowerState n (r + 2) → C := fun t =>
    coloredTensor (n + 2) (fun i => tensorPower X (t.val i))
  have hflat : ∀ (t : ColoredPowerState n (r + 2)) (p : t = s),
      eqToIso (congrArg T p) ≪≫ coloredPowerStateFlatten X n (r + 2) s =
        coloredPowerStateFlatten X n (r + 2) t := by
    intro t p
    cases p
    simp
  have hclose : coloredPowerStateWordIso X n (r + 2) w.reverse s ≪≫
      eqToIso (congrArg T hs) =
      coloredWordIso n w.reverse (fun i => tensorPower X (k i)) ≪≫
        eqToIso (congrArg (coloredTensor (n + 2))
          (congrArg (fun t => fun j => tensorPower X (k (t j)))
            (coloredWordSwap_reverse_pure n w hw))) := by
    apply eq_of_heq
    exact (iso_trans_eqToIso_heq _ _).trans (he.trans (iso_trans_eqToIso_heq _ _).symm)
  have hh := congrArg Iso.hom hclose
  have hf := congrArg Iso.hom (hflat _ hs)
  dsimp only [z, coloredPureWordHom]
  simp only [Iso.trans_hom, eqToIso.hom] at hh hf ⊢
  simp only [Category.assoc] at *
  rw [← hh]
  rw [← hf]
  simp [Category.assoc]


/-- Exact positive-width flattening cabling interface with positive-state
crossing membership only. -/
theorem positiveWidth_cabling_of_positive_states (X : C) (n : ℕ)
    (q : Fin (n + 2) → ℕ) (hq : ∀ j, 0 < q j)
    (hletter : ∀ (s : ColoredPowerState n (((∑ j, q j) - 2) + 2)),
      (∀ j, 0 < s.val j) → ∀ (i : Fin (n + 1)),
      Aut.of ((coloredPowerStateFlatten X n (((∑ j, q j) - 2) + 2) s).symm ≪≫
        coloredLetter n i true (fun j => tensorPower X (s.val j)) ≪≫
        coloredPowerStateFlatten X n (((∑ j, q j) - 2) + 2)
          (coloredPowerSwap n (((∑ j, q j) - 2) + 2) i s)) ∈
        braidImage X ((∑ j, q j) - 2))
    (w : List (Fin (n + 1) × Bool))
    (hw : strandPermutation n (FreeGroup.mk w) = 1) :
    ∃ z : braidImage X ((∑ j, q j) - 2),
      coloredPureWordHom n w hw (fun j => tensorPower X (q j)) =
        (positiveWidthFlatten X n q hq (coloredTensorPowersFlatten X (n + 2) q)).hom ≫
          z.val.asIso.hom ≫
        (positiveWidthFlatten X n q hq (coloredTensorPowersFlatten X (n + 2) q)).inv := by
  have h := coloredPureWord_cabling_of_positive_states X n ((∑ j, q j) - 2) q
    (Nat.sub_add_cancel (two_le_sum_positive_widths n q hq)).symm hq hletter w hw
  simpa only [positiveWidthFlatten, coloredPowerStateFlatten, powerIndexIso] using h

/-- Positive-power finite sums have property F once positive colored
crossings on positive fixed-total states are original-strand braids. -/
theorem objectPropertyF_positivePower_biproduct_of_positive_letters
    [MonoidalPreadditive C] [HasFiniteBiproducts C] {I : Type} [Fintype I] [DecidableEq I]
    (X : C) (k : I → ℕ) (hk : ∀ i, 0 < k i) (hX : ObjectPropertyF X)
    (hletter : ∀ (n r : ℕ) (s : ColoredPowerState n (r + 2)),
      (∀ j, 0 < s.val j) → ∀ (i : Fin (n + 1)),
      Aut.of ((coloredPowerStateFlatten X n (r + 2) s).symm ≪≫
        coloredLetter n i true (fun j => tensorPower X (s.val j)) ≪≫
        coloredPowerStateFlatten X n (r + 2) (coloredPowerSwap n (r + 2) i s)) ∈
          braidImage X r) :
    ObjectPropertyF (⨁ (fun i => tensorPower X (k i))) := by
  apply finite_positivePower_biproduct_of_cabling X k hk hX
    (fun n q => coloredTensorPowersFlatten X (n + 2) q)
  intro n q hq w hw
  apply positiveWidth_cabling_of_positive_states X n q hq
  · exact hletter n _

end MTC.Braided.Cabling
end
