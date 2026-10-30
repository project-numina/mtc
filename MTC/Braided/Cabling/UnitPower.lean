module
public import MTC.Braided.Cabling.Generated
public import Mathlib.CategoryTheory.Monoidal.Rigid.OfEquivalence
public import Mathlib.CategoryTheory.Monoidal.Rigid.Braided
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import MTC.Fusion.Reciprocity
public import MTC.Fusion.Simples

open MTC.Braided

/-!
# Duals in generated closures

Finite sums of right mates and generation of a simple object’s dual.
-/

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open scoped BigOperators
@[expose] public noncomputable section
namespace MTC
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [Preadditive C]
  [MonoidalPreadditive C]
/-- Taking right mates commutes with finite sums. -/
theorem rightAdjointMate_sum {A B : C} [HasRightDual A] [HasRightDual B] {ι : Type} [Fintype ι]
    (f : ι → (A ⟶ B)) : (∑ i, f i)ᘁ = ∑ i, (f i)ᘁ := by
  simp [rightAdjointMate, sum_whiskerRight,
    whiskerLeft_sum, Preadditive.comp_sum, Preadditive.sum_comp]

end MTC

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
@[expose] public noncomputable section
namespace MTC.Braided.Cabling
universe v u
variable {D : Type u} [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]
  [Abelian D] [Linear ℂ D] [RigidCategory D] [MonoidalPreadditive D] [MonoidalLinear ℂ D]
  [MTC.IsFusionCategory D]

set_option backward.isDefEq.respectTransparency false in
/-- A positive tensor power containing the unit makes the simple generator's
right dual a retract of a lower tensor power. -/
theorem generatedBy_rightDual_of_unit_power {X : D} [Simple X] {n : ℕ}
    (r : Retract (𝟙_ D) (tensorPower X (n + 1))) :
    GeneratedBy X (Xᘁ) :=
  let _ : Simple (𝟙_ D) := MTC.IsFusionCategory.unit_simple
  let _ : Simple (Xᘁ) := MTC.simple_rightDual X
  let _ : IsSplitMono r.i := r.instIsSplitMonoI
  let f : Xᘁ ⊗ 𝟙_ D ⟶ tensorPower X n :=
    (MTC.tensorLeftHomLinearEquiv (k := ℂ) (𝟙_ D) X (Xᘁ) (tensorPower X n)).symm r.i
  let hf : f ≠ 0 := (MTC.tensorLeftHomLinearEquiv
    (𝟙_ D) X (Xᘁ) (tensorPower X n)).symm.map_ne_zero_iff.mpr
      (MTC.mono_ne_zero_of_id_ne_zero r.i (id_nonzero (𝟙_ D)))
  let g : Xᘁ ⟶ tensorPower X n := (ρ_ (Xᘁ)).inv ≫ f
  let ⟨s, hs⟩ := MTC.split_from_simple g (by simpa [g] using hf)
  generatedBy_retract (generatedBy_tensorPower X n) { i := g, r := s, retract := hs }
end MTC.Braided.Cabling
