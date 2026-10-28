module
public import PropertyF.Ground.Cabling.Generated
public import Mathlib.CategoryTheory.Monoidal.Rigid.OfEquivalence
public import Mathlib.CategoryTheory.Monoidal.Rigid.Braided
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import PropertyF.Ground.Fusion.Reciprocity
public import PropertyF.Ground.Fusion.Simples

/-!
# Duals in generated closures

Finite sums of right mates and generation of a simple object’s dual.
-/

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open scoped BigOperators
@[expose] public noncomputable section
namespace PropertyF
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [Abelian C] [MonoidalPreadditive C] [RigidCategory C]
attribute [local instance] Abelian.hasFiniteBiproducts

omit [BraidedCategory C] in
/-- Taking right mates commutes with finite sums. -/
theorem rightAdjointMate_sum {A B : C} {ι : Type} [Fintype ι]
    (f : ι → (A ⟶ B)) : (∑ i, f i)ᘁ = ∑ i, (f i)ᘁ := by
  simp [rightAdjointMate, sum_whiskerRight,
    whiskerLeft_sum, Preadditive.comp_sum, Preadditive.sum_comp]

end PropertyF

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
@[expose] public noncomputable section
namespace PropertyF.Ground.Cabling
universe v u

set_option backward.isDefEq.respectTransparency false in
/-- A positive tensor power containing the unit makes the simple generator's
right dual a retract of a lower tensor power. -/
theorem generatedBy_rightDual_of_unit_power (D : BraidedFusionCategory.{v,u})
    {X : D.Obj} [Simple X] {n : ℕ} (r : Retract (𝟙_ D.Obj) (tensorPower X (n + 1))) :
    GeneratedBy X (Xᘁ) := by
  let _ : Simple (𝟙_ D.Obj) := Ground.IsFusionCategory.unit_simple
  let _ : Simple (Xᘁ) := Ground.simple_rightDual D X
  have hi : r.i ≠ 0 := by
    intro h
    apply id_nonzero (𝟙_ D.Obj)
    simpa [h] using r.retract.symm
  let f : Xᘁ ⊗ 𝟙_ D.Obj ⟶ tensorPower X n :=
    (tensorLeftHomEquiv (𝟙_ D.Obj) X (Xᘁ) (tensorPower X n)).symm r.i
  have hf : f ≠ 0 := by
    intro h
    apply hi
    have he := congrArg (tensorLeftHomEquiv (𝟙_ D.Obj) X (Xᘁ) (tensorPower X n)) h
    dsimp only [f] at he
    rw [Equiv.apply_symm_apply] at he
    simpa [tensorLeftHomEquiv] using he
  let g : Xᘁ ⟶ tensorPower X n := (ρ_ (Xᘁ)).inv ≫ f
  have hg : g ≠ 0 := by simpa [g] using hf
  obtain ⟨s, hs⟩ := Ground.split_from_simple g hg
  exact generatedBy_retract (generatedBy_tensorPower X n) { i := g, r := s, retract := hs }
end PropertyF.Ground.Cabling
