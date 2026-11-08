module
public import MTC.Braided.Cabling.ColorBiproductPositive
public import MTC.Braided.Cabling.PureSumCabling

/-! Finite positive-power sums from explicit fixed-total colored letters. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open scoped BigOperators
namespace MTC.Braided.Cabling
universe v u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {C : Type u} [Category.{v} C] [Preadditive C] [MonoidalCategory C]
  [MonoidalPreadditive C] [HasFiniteBiproducts C] [BraidedCategory C] [Abelian C]

/-- Fixed-total signed-letter cabling gives property F for each finite sum
of strictly positive powers. The remaining hypothesis concerns the actual
colored crossing and an actual original-strand braid-image element. -/
theorem finite_positivePower_biproduct_of_letter_cabling
    {I : Type} [Fintype I] [DecidableEq I] (X : C) (k : I → ℕ)
    (hk : ∀ i, 0 < k i) (hX : ObjectPropertyF X)
    (hletter : ∀ (n r : ℕ) (s : ColoredPowerState n (r + 2))
      (a : Fin (n + 1) × Bool),
      Aut.of ((coloredPowerStateFlatten X n (r + 2) s).symm ≪≫
        coloredLetter n a.1 a.2 (fun i => tensorPower X (s.val i)) ≪≫
        coloredPowerStateFlatten X n (r + 2) (coloredPowerSwap n (r + 2) a.1 s)) ∈
          braidImage X r) :
    ObjectPropertyF (⨁ (fun i => tensorPower X (k i))) := by
  apply finite_positivePower_biproduct_of_cabling X k hk hX
    (fun n q => coloredTensorPowersFlatten X (n + 2) q)
  intro n q hq w hw
  let r := (∑ j, q j) - 2
  have hsum : ∑ j, q j = r + 2 :=
    (Nat.sub_add_cancel (two_le_sum_positive_widths n q hq)).symm
  have h := coloredPureWord_cabling_of_letters X n r q hsum (hletter n r) w hw
  exact h

end MTC.Braided.Cabling
end
