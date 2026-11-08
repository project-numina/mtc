module
public import MTC.Braided.Cabling.ClosureFlattenLocalCompare
public import MTC.Braided.Cabling.Generated

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open scoped ZeroObject
namespace MTC.Braided
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C] [Abelian C]
attribute [local instance] Abelian.hasFiniteBiproducts

/-- The zero object has property F, by its retract into the tensor unit. -/
theorem objectPropertyF_zero : ObjectPropertyF (0 : C) := by
  apply objectPropertyF_of_retract _ (objectPropertyF_unit (C := C))
  exact { i := 0, r := 0, retract := by simp }

/-- A finite-sum theorem for actual powers gives the generated-object
closure by the categorical braid-image retract map. -/
theorem objectPropertyF_of_generatedBy_of_power_sums {X Y : C}
    (hY : GeneratedBy X Y)
    (hsum : ∀ (n : ℕ) (k : Fin n → ℕ),
      ObjectPropertyF (⨁ fun i => tensorPower X (k i))) : ObjectPropertyF Y := by
  obtain ⟨n, k, ⟨r⟩⟩ := hY
  exact objectPropertyF_of_retract r (hsum n k)

/-- The empty biproduct has property F; its braid image is finite even when
there are no summands and no generator is available. -/
theorem objectPropertyF_empty_biproduct (f : Fin 0 → C) : ObjectPropertyF (⨁ f) := by
  apply objectPropertyF_of_retract _ (objectPropertyF_unit (C := C))
  refine { i := 0, r := 0, retract := ?_ }
  apply biproduct.hom_ext
  intro i
  exact Fin.elim0 i
