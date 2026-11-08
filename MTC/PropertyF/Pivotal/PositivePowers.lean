module
public import MTC.Fusion.UnitPower
public import MTC.Braided.Cabling.Naturality
public import MTC.Center.Normalization.MugerLabels
public import MTC.PropertyF.Pivotal.SymmetricPropertyF

/-! # Replacing zero tensor powers by positive powers -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open MTC.Fusion MTC.Braided
namespace MTC.PropertyF.Pivotal
set_option backward.isDefEq.respectTransparency false
universe v u
variable (C : BraidedFusionCategory.{v,u})
attribute [local instance] Abelian.hasFiniteBiproducts

/-- If the generator is zero, every object in its generated category has
property F because it is transparent. -/
theorem objectPropertyF_of_generatedBy_zero {X Y : C.Obj}
    (hX : IsZero X) (hY : GeneratedBy X Y) : ObjectPropertyF Y := by
  have r : Retract X (𝟙_ C.Obj) := ⟨0, 0, by
    simpa using hX.eq_of_src (0 : X ⟶ X) (𝟙 X)⟩
  apply objectPropertyF_of_transparent
  exact MTC.Center.Normalization.transparent_generatedBy
    (MTC.Center.Normalization.transparent_of_retract r
      MTC.Center.Normalization.transparent_unit) hY

/-- Every nonzero object in a braided fusion category has a positive tensor
power containing the tensor unit as an actual retract. -/
theorem unit_retract_positive_power_of_nonzero (X : C.Obj) (hX : ¬ IsZero X) :
    ∃ n, Nonempty (Retract (𝟙_ C.Obj) (tensorPower X (n+1))) := by
  obtain ⟨i, s, t, _, ht⟩ := exists_retract_of_biproduct_decomposition
    (simples_decompose C X) (by simpa [IsZero.iff_id_eq_zero] using hX)
  let r : Retract (simples C i) X := ⟨t, s, ht⟩
  letI : Simple (simples C i) := simples_simple C i
  obtain ⟨n, ⟨q⟩⟩ := MTC.Fusion.unit_retract_tensorPower (simples C i)
  let rpow : Retract (tensorPower (simples C i) (n+1)) (tensorPower X (n+1)) :=
    ⟨tensorPowerMap r.i (n+1), tensorPowerMap r.r (n+1), by
      rw [← tensorPowerMap_comp, r.retract, tensorPowerMap_id]⟩
  exact ⟨n, ⟨q.trans rpow⟩⟩

/-- Every finite sum of nonnegative powers of a nonzero object is a retract
of a finite sum of strictly positive powers. -/
theorem powerSum_retract_positive_of_nonzero (X : C.Obj) (hX : ¬ IsZero X)
    (m : ℕ) (k : Fin m → ℕ) :
    ∃ l : Fin m → ℕ, (∀ i, 0 < l i) ∧
      Nonempty (Retract (⨁ fun i => tensorPower X (k i))
        (⨁ fun i => tensorPower X (l i))) := by
  classical
  obtain ⟨n, ⟨q⟩⟩ := unit_retract_positive_power_of_nonzero C X hX
  let l : Fin m → ℕ := fun i => if k i = 0 then n+1 else k i
  have hl : ∀ i, 0 < l i := by
    intro i
    dsimp [l]
    split_ifs with h
    · omega
    · exact Nat.pos_of_ne_zero h
  have r (i : Fin m) : Retract (tensorPower X (k i)) (tensorPower X (l i)) := by
    by_cases h : k i = 0
    · simpa [l, h, tensorPower] using q
    · simp only [l, if_neg h]
      exact Retract.refl _
  refine ⟨l, hl, ⟨?_, ?_, ?_⟩⟩
  · exact biproduct.map fun i => (r i).i
  · exact biproduct.map fun i => (r i).r
  · apply biproduct.hom_ext
    intro i
    simp [Category.assoc, (r i).retract]

end MTC.PropertyF.Pivotal
end
