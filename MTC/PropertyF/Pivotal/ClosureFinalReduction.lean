module
public import MTC.PropertyF.Pivotal.PositiveClosure
public import MTC.Braided.Cabling.ColorBiproductLetters
public import MTC.Braided.Cabling.PureSumSigned
public import MTC.PropertyF.Pivotal.ObjectwiseMain
public import MTC.Braided.Cabling.PureSumPositiveState

/-! # Closure and objectwise results reduced to positive crossing cabling -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
open MTC.Fusion MTC.Braided MTC.Braided.Cabling
open scoped BigOperators
namespace MTC.PropertyF.Pivotal
universe v u
attribute [local instance] Abelian.hasFiniteBiproducts

/-- The closure lemma follows from the concrete categorical claim that each
flattened positive colored crossing belongs to the original braid image. -/
theorem closureStatement_of_positive_crossing_cabling
    (hcross : ∀ (C : BraidedFusionCategory.{v,u}) (X : C.Obj) (n r : ℕ)
      (s : ColoredPowerState n (r+2)) (i : Fin (n+1)),
      Aut.of ((coloredPowerStateFlatten X n (r+2) s).symm ≪≫
        coloredLetter n i true (fun j => tensorPower X (s.val j)) ≪≫
        coloredPowerStateFlatten X n (r+2) (coloredPowerSwap n (r+2) i s)) ∈
          braidImage X r) : ClosureStatement.{v,u} := by
  apply closureStatement_of_positive_power_sums
  intro C X hF m k hk
  apply finite_positivePower_biproduct_of_letter_cabling X k hk hF
  intro n r
  exact coloredPower_letters_mem_of_positive X (r+2) (braidImage X r) (hcross C X n r)

/-- The full objectwise corollary follows from that same concrete crossing
cabling claim. -/
theorem objectwiseStatement_of_positive_crossing_cabling
    (hcross : ∀ (C : BraidedFusionCategory.{v,u}) (X : C.Obj) (n r : ℕ)
      (s : ColoredPowerState n (r+2)) (i : Fin (n+1)),
      Aut.of ((coloredPowerStateFlatten X n (r+2) s).symm ≪≫
        coloredLetter n i true (fun j => tensorPower X (s.val j)) ≪≫
        coloredPowerStateFlatten X n (r+2) (coloredPowerSwap n (r+2) i s)) ∈
          braidImage X r) : ObjectwiseStatement.{v,u} :=
  objectwiseStatement_of_closure (closureStatement_of_positive_crossing_cabling hcross)

/-- It is enough to cable positive crossings between positive-width blocks;
zero generators and unit summands are handled separately by retracts. -/
theorem closureStatement_of_positive_state_crossing_cabling
    (hcross : ∀ (C : BraidedFusionCategory.{v,u}) (X : C.Obj) (n r : ℕ)
      (s : ColoredPowerState n (r+2)), (∀ j, 0 < s.val j) → ∀ i : Fin (n+1),
      Aut.of ((coloredPowerStateFlatten X n (r+2) s).symm ≪≫
        coloredLetter n i true (fun j => tensorPower X (s.val j)) ≪≫
        coloredPowerStateFlatten X n (r+2) (coloredPowerSwap n (r+2) i s)) ∈
          braidImage X r) : ClosureStatement.{v,u} := by
  apply closureStatement_of_positive_power_sums
  intro C X hF m k hk
  apply finite_positivePower_biproduct_of_cabling X k hk hF
    (fun n q => coloredTensorPowersFlatten X (n+2) q)
  intro n q hq w hw
  exact positiveWidth_cabling_of_positive_states X n q hq
    (hcross C X n ((∑ j, q j) - 2)) w hw

end MTC.PropertyF.Pivotal
end
