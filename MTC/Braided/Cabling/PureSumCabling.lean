module
public import MTC.Braided.Cabling.ClosureColoredWords
public import MTC.Braided.Cabling.PureSumPreservation

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace MTC.Braided.Cabling
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C] [Abelian C]

/-- Closing a pure colored word identifies its action with the fixed-total
word action transported through the canonical flattening. -/
theorem coloredPureWord_eq_stateWord (X : C) (n r : ℕ)
    (k : Fin (n + 2) → ℕ) (hk : ∑ i, k i = r + 2)
    (w : List (Fin (n + 1) × Bool))
    (hw : strandPermutation n (FreeGroup.mk w) = 1) :
    let s : ColoredPowerState n (r + 2) := ⟨k, hk⟩
    coloredPureWordHom n w hw (fun i => tensorPower X (k i)) =
      (coloredPowerStateFlatten X n (r + 2) s).hom ≫
        (Aut.of ((coloredPowerStateFlatten X n (r + 2) s).symm ≪≫
          coloredPowerStateWordIso X n (r + 2) w.reverse s ≪≫
          coloredPowerStateFlatten X n (r + 2)
            (coloredPowerWordState n (r + 2) w.reverse s))).asIso.hom ≫
      (coloredPowerStateFlatten X n (r + 2) s).inv := by
  let s : ColoredPowerState n (r + 2) := ⟨k, hk⟩
  have hs : coloredPowerWordState n (r + 2) w.reverse s = s := by
    apply Subtype.ext
    rw [coloredPowerWordState_val, coloredWordSwap_reverse_pure n w hw]
    rfl
  have he := coloredPowerStateWordIso_heq X n (r + 2) w.reverse s
  let T : ColoredPowerState n (r + 2) → C := fun t =>
    coloredTensor (n + 2) (fun i => tensorPower X (t.val i))
  have hclose : coloredPowerStateWordIso X n (r + 2) w.reverse s ≪≫
      eqToIso (congrArg T hs) =
      coloredWordIso n w.reverse (fun i => tensorPower X (k i)) ≪≫
        eqToIso (congrArg (coloredTensor (n + 2))
          (congrArg (fun t => fun j => tensorPower X (k (t j)))
            (coloredWordSwap_reverse_pure n w hw))) := by
    apply eq_of_heq
    exact (iso_trans_eqToIso_heq _ _).trans (he.trans (iso_trans_eqToIso_heq _ _).symm)
  have hh := congrArg Iso.hom hclose
  have hf := eqToHom_iso_hom_naturality (coloredPowerStateFlatten X n (r + 2)) hs
  simp only [eqToHom_refl, Category.comp_id] at hf
  dsimp only [coloredPureWordHom]
  simp only [Iso.trans_hom, eqToIso.hom] at hh hf ⊢
  simp only [Category.assoc] at *
  rw [← hh]
  rw [hf]
  simp [Category.assoc, s]

/-- The fixed-total word construction produces an original-strand braid for each
closed colored word, provided the signed colored letters do so. -/
theorem coloredPureWord_cabling_of_letters (X : C) (n r : ℕ)
    (k : Fin (n + 2) → ℕ) (hk : ∑ i, k i = r + 2)
    (hletter : ∀ (s : ColoredPowerState n (r + 2)) (a : Fin (n + 1) × Bool),
      Aut.of ((coloredPowerStateFlatten X n (r + 2) s).symm ≪≫
        coloredLetter n a.1 a.2 (fun i => tensorPower X (s.val i)) ≪≫
        coloredPowerStateFlatten X n (r + 2) (coloredPowerSwap n (r + 2) a.1 s)) ∈ braidImage X r)
    (w : List (Fin (n + 1) × Bool))
    (hw : strandPermutation n (FreeGroup.mk w) = 1) :
    ∃ z : braidImage X r,
      coloredPureWordHom n w hw (fun i => tensorPower X (k i)) =
        (coloredPowerStateFlatten X n (r + 2) ⟨k, hk⟩).hom ≫ z.val.asIso.hom ≫
          (coloredPowerStateFlatten X n (r + 2) ⟨k, hk⟩).inv := by
  let s : ColoredPowerState n (r + 2) := ⟨k, hk⟩
  have hm := coloredPowerStateWord_mem_of_letters X n (r + 2) (braidImage X r) hletter w.reverse s
  exact ⟨⟨_, hm⟩, coloredPureWord_eq_stateWord X n r k hk w hw⟩

end MTC.Braided.Cabling
end
