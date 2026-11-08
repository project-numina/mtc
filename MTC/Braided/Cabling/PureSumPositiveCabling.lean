module
public import MTC.Braided.Cabling.PureSumCabling
public import MTC.Braided.Cabling.PureSumSigned
public import MTC.Braided.Cabling.ColorBiproductPositive

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace MTC.Braided.Cabling
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C] [Abelian C]

/-- Positive fixed-total generator membership supplies the exact pure-word
cabling premise for the canonical flattening of positive-width tuples. -/
theorem positiveWidth_cabling_of_positive_letters (X : C) (n : ℕ)
    (q : Fin (n + 2) → ℕ) (hq : ∀ j, 0 < q j)
    (hletter : ∀ (s : ColoredPowerState n (((∑ j, q j) - 2) + 2))
      (i : Fin (n + 1)),
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
  have h := coloredPureWord_cabling_of_letters X n ((∑ j, q j) - 2) q
    (Nat.sub_add_cancel (two_le_sum_positive_widths n q hq)).symm
    (coloredPower_letters_mem_of_positive X n _ _ hletter) w hw
  simpa only [positiveWidthFlatten, coloredPowerStateFlatten, powerIndexIso] using h

end MTC.Braided.Cabling
end
