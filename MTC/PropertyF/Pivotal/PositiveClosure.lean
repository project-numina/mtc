module
public import MTC.PropertyF.Pivotal.PositivePowers
public import MTC.PropertyF.Pivotal.Statement

/-! # Closure reduced to sums of positive powers -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open MTC.Fusion MTC.Braided
namespace MTC.PropertyF.Pivotal
universe v u
attribute [local instance] Abelian.hasFiniteBiproducts

/-- The closure lemma follows from property F for finite sums of positive
powers of every object with property F. Zero generators and zero exponents
are handled without any cabling assumption. -/
theorem closureStatement_of_positive_power_sums
    (hsums : ∀ (C : BraidedFusionCategory.{v,u}) (X : C.Obj), ObjectPropertyF X →
      ∀ (m : ℕ) (l : Fin m → ℕ), (∀ i, 0 < l i) →
        ObjectPropertyF (⨁ fun i => tensorPower X (l i))) : ClosureStatement.{v,u} := by
  intro C X Y hF hY
  classical
  by_cases hX : IsZero X
  · exact objectPropertyF_of_generatedBy_zero C hX hY
  · obtain ⟨m, k, ⟨r⟩⟩ := hY
    obtain ⟨l, hl, ⟨q⟩⟩ := powerSum_retract_positive_of_nonzero C X hX m k
    exact objectPropertyF_of_retract (r.trans q) (hsums C X hF m l hl)

end MTC.PropertyF.Pivotal
end
