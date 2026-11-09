module
public import MTC.Braided.Cabling.ClosureColoredBridge

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace MTC.Braided
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C] [Abelian C]

/-- Color assignments with a prescribed total number of original strands. -/
def ColoredPowerState (n N : ℕ) := {k : Fin (n+2) → ℕ // ∑ i, k i = N}

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
theorem coloredPowerWordState_val (n N : ℕ) : ∀ w k,
    (coloredPowerWordState n N w k).val = fun i => k.val (Cabling.coloredWordSwap n w i)
  | [], _ => rfl
  | a::w, k => coloredPowerWordState_val n N w (coloredPowerSwap n N a.1 k)

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
/-- If every signed colored generator becomes an original-strand braid,
then every colored word does as well. The multiplication order is the order
of categorical composition, hence opposite to automorphism multiplication. -/
theorem coloredPowerStateWord_mem_of_letters (X : C) (n N : ℕ) (G : Subgroup (Aut (tensorPower X N)))
    (h : ∀ (k : ColoredPowerState n N) (a : Fin (n+1) × Bool),
      Aut.of ((coloredPowerStateFlatten X n N k).symm ≪≫
        Cabling.coloredLetter n a.1 a.2 (fun i => tensorPower X (k.val i)) ≪≫
        coloredPowerStateFlatten X n N (coloredPowerSwap n N a.1 k)) ∈ G) :
    ∀ (w : List (Fin (n+1) × Bool)) (k : ColoredPowerState n N),
      Aut.of ((coloredPowerStateFlatten X n N k).symm ≪≫
        coloredPowerStateWordIso X n N w k ≪≫
        coloredPowerStateFlatten X n N (coloredPowerWordState n N w k)) ∈ G
  | [], k => by
    simpa only [coloredPowerStateWordIso, coloredPowerWordState, Iso.refl_trans,
      Iso.symm_self_id] using (show Aut.of (Iso.refl (tensorPower X N)) ∈ G from G.one_mem)
  | a::w, k => by
    have ha := h k a
    have hw := coloredPowerStateWord_mem_of_letters X n N G h w (coloredPowerSwap n N a.1 k)
    have hm := G.mul_mem hw ha
    convert hm using 1
    apply Aut.ext
    simp [coloredPowerStateWordIso, coloredPowerWordState, Iso.trans_assoc]

set_option backward.isDefEq.respectTransparency false in
/-- The state-indexed word is the actual colored word, with the same letters
and the same categorical composition order. -/
theorem coloredPowerStateWordIso_heq (X : C) (n N : ℕ) : ∀ w (k : ColoredPowerState n N),
    coloredPowerStateWordIso X n N w k ≍
      Cabling.coloredWordIso n w (fun i => tensorPower X (k.val i))
  | [], _ => by rfl
  | a::w, k => by
    simp only [coloredPowerStateWordIso, Cabling.coloredWordIso]
    have ih := coloredPowerStateWordIso_heq X n N w (coloredPowerSwap n N a.1 k)
    congr 2
    all_goals try exact ih
    all_goals try rfl
    all_goals rw [coloredPowerWordState_val]
