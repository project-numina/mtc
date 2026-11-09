module
public import MTC.Braided.Cabling.ClosureColoredBridge

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace MTC.Braided
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C] [Abelian C]

/-- Color assignments with a prescribed total number of original strands. -/
def ColoredPowerState (n N : ℕ) := {k : Fin (n+2) → ℕ // ∑ i, k i = N}

/-- A fixed-total state decomposes into its first two widths and its suffix. -/
theorem coloredPowerState_total_eq_head_two {n N : ℕ} (k : ColoredPowerState n N) :
    N = k.val 0 + k.val 1 + heterogeneousStrandCount n (fun i => k.val i.succ.succ) := by
  simpa only [Fin.sum_univ_succ, ← heterogeneousStrandCount_eq_sum, Nat.add_assoc,
    Fin.succ_zero_eq_one] using k.property.symm

/-- An adjacent color swap preserves the total strand count. -/
def coloredPowerSwap (n N : ℕ) (i : Fin (n+1)) (k : ColoredPowerState n N) : ColoredPowerState n N :=
  ⟨fun j => k.val (Cabling.coloredSwap n i j), by
    rw [Cabling.coloredSwap_eq_swap]
    exact (Equiv.sum_comp (Equiv.swap i.castSucc i.succ) k.val).trans k.property⟩

/-- The color assignment after a word. -/
def coloredPowerWordState (n N : ℕ) :
    List (Fin (n+1) × Bool) → ColoredPowerState n N → ColoredPowerState n N
  | [], k => k
  | a::w, k => coloredPowerWordState n N w (coloredPowerSwap n N a.1 k)

/-- The endpoint colors agree with the concrete colored-word permutation. -/
theorem coloredPowerWordState_val {n N : ℕ} : ∀ w k,
    (coloredPowerWordState n N w k).val = fun i => k.val (Cabling.coloredWordSwap n w i)
  | [], _ => rfl
  | a::w, k => coloredPowerWordState_val w (coloredPowerSwap n N a.1 k)

/-- A pure word returns every fixed-total color state to itself. -/
theorem coloredPowerWordState_reverse_pure {n N : ℕ}
    (w : List (Fin (n + 1) × Bool))
    (hw : strandPermutation n (FreeGroup.mk w) = 1) (s : ColoredPowerState n N) :
    coloredPowerWordState n N w.reverse s = s := by
  apply Subtype.ext
  rw [coloredPowerWordState_val, Cabling.coloredWordSwap_reverse_pure n w hw]
  rfl

/-- Flatten every fixed-total color state into one common tensor power. -/
def coloredPowerStateFlatten (X : C) (n N : ℕ) (k : ColoredPowerState n N) :
    Cabling.coloredTensor (n+2) (fun i => tensorPower X (k.val i)) ≅ tensorPower X N :=
  coloredTensorPowersFlatten X (n+2) k.val ≪≫ powerIndexIso X k.property

/-- The actual categorical word, indexed by fixed-total color states. -/
def coloredPowerStateWordIso (X : C) (n N : ℕ) : ∀ w (k : ColoredPowerState n N),
    Cabling.coloredTensor (n+2) (fun i => tensorPower X (k.val i)) ≅
      Cabling.coloredTensor (n+2) (fun i => tensorPower X ((coloredPowerWordState n N w k).val i))
  | [], _ => Iso.refl _
  | a::w, k => Cabling.coloredLetter n a.1 a.2 (fun i => tensorPower X (k.val i)) ≪≫
      coloredPowerStateWordIso X n N w (coloredPowerSwap n N a.1 k)

set_option backward.isDefEq.respectTransparency false in
/-- A state invariant preserved by each colored swap lets letter membership
extend to every word beginning at an invariant state. -/
theorem coloredPowerStateWord_mem_of_invariant_letters (X : C) (n N : ℕ) (G : Subgroup (Aut (tensorPower X N)))
    (P : ColoredPowerState n N → Prop)
    (hswap : ∀ (s : ColoredPowerState n N), P s → ∀ (a : Fin (n + 1) × Bool),
      P (coloredPowerSwap n N a.1 s))
    (h : ∀ (s : ColoredPowerState n N), P s → ∀ (a : Fin (n + 1) × Bool),
      Aut.of ((coloredPowerStateFlatten X n N s).symm ≪≫
        Cabling.coloredLetter n a.1 a.2 (fun i => tensorPower X (s.val i)) ≪≫
        coloredPowerStateFlatten X n N (coloredPowerSwap n N a.1 s)) ∈ G) :
    ∀ (w : List (Fin (n + 1) × Bool)) (s : ColoredPowerState n N), P s →
      Aut.of ((coloredPowerStateFlatten X n N s).symm ≪≫
        coloredPowerStateWordIso X n N w s ≪≫
        coloredPowerStateFlatten X n N (coloredPowerWordState n N w s)) ∈ G
  | [], s, _ => by
    simpa only [coloredPowerStateWordIso, coloredPowerWordState, Iso.refl_trans,
      Iso.symm_self_id] using (show Aut.of (Iso.refl (tensorPower X N)) ∈ G from G.one_mem)
  | a :: w, s, hs => by
    have ha := h s hs a
    have hw := coloredPowerStateWord_mem_of_invariant_letters X n N G P hswap h w
      (coloredPowerSwap n N a.1 s) (hswap s hs a)
    have hm := G.mul_mem hw ha
    convert hm using 1
    apply Aut.ext
    simp [coloredPowerStateWordIso, coloredPowerWordState, Iso.trans_assoc]

set_option backward.isDefEq.respectTransparency false in
/-- If every signed colored generator becomes an original-strand braid,
then every colored word does as well. The multiplication order is the order
of categorical composition, hence opposite to automorphism multiplication. -/
theorem coloredPowerStateWord_mem_of_letters (X : C) {n : ℕ} (N : ℕ) (G : Subgroup (Aut (tensorPower X N)))
    (h : ∀ (k : ColoredPowerState n N) (a : Fin (n+1) × Bool),
      Aut.of ((coloredPowerStateFlatten X n N k).symm ≪≫
        Cabling.coloredLetter n a.1 a.2 (fun i => tensorPower X (k.val i)) ≪≫
        coloredPowerStateFlatten X n N (coloredPowerSwap n N a.1 k)) ∈ G) :
    ∀ (w : List (Fin (n+1) × Bool)) (k : ColoredPowerState n N),
      Aut.of ((coloredPowerStateFlatten X n N k).symm ≪≫
        coloredPowerStateWordIso X n N w k ≪≫
        coloredPowerStateFlatten X n N (coloredPowerWordState n N w k)) ∈ G := by
  intro w s
  exact coloredPowerStateWord_mem_of_invariant_letters X n N G (fun _ => True)
    (fun _ _ _ => trivial) (fun s _ a => h s a) w s trivial

set_option backward.isDefEq.respectTransparency false in
/-- The state-indexed word is the actual colored word, with the same letters
and the same categorical composition order. -/
theorem coloredPowerStateWordIso_heq (X : C) {n N : ℕ} : ∀ w (k : ColoredPowerState n N),
    coloredPowerStateWordIso X n N w k ≍
      Cabling.coloredWordIso n w (fun i => tensorPower X (k.val i))
  | [], _ => by rfl
  | a::w, k => by
    simp only [coloredPowerStateWordIso, Cabling.coloredWordIso]
    have ih := coloredPowerStateWordIso_heq X w (coloredPowerSwap n N a.1 k)
    congr 2
    all_goals try exact ih
    all_goals try rfl
    all_goals rw [coloredPowerWordState_val]

set_option backward.isDefEq.respectTransparency false in
/-- After closing their endpoints, the state-indexed and ordinary colored
word isomorphisms agree. -/
theorem coloredPowerStateWordIso_reverse_pure (X : C) {n N : ℕ}
    (w : List (Fin (n + 1) × Bool))
    (hw : strandPermutation n (FreeGroup.mk w) = 1) (s : ColoredPowerState n N) :
    coloredPowerStateWordIso X n N w.reverse s ≪≫
        eqToIso (congrArg (fun t : ColoredPowerState n N =>
          Cabling.coloredTensor (n + 2) (fun i => tensorPower X (t.val i)))
            (coloredPowerWordState_reverse_pure w hw s)) =
      Cabling.coloredWordIso n w.reverse (fun i => tensorPower X (s.val i)) ≪≫
        eqToIso (congrArg (Cabling.coloredTensor (n + 2))
          (congrArg (fun t => fun j => tensorPower X (s.val (t j)))
            (Cabling.coloredWordSwap_reverse_pure n w hw))) := by
  have he := coloredPowerStateWordIso_heq X w.reverse s
  apply eq_of_heq
  exact (iso_trans_eqToIso_heq _ _).trans (he.trans (iso_trans_eqToIso_heq _ _).symm)
