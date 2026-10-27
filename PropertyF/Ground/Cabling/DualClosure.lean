module
public import PropertyF.Ground.Cabling.Rigidity
public import Mathlib.CategoryTheory.Preadditive.Biproducts
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

/-- The dual of a finite biproduct is a retract of the biproduct of duals. -/
def dualBiproductRetract (n : ℕ) (f : Fin n → C) :
    Retract ((⨁ f)ᘁ) (⨁ fun i => (f i)ᘁ) where
  i := biproduct.lift fun i => (biproduct.ι f i)ᘁ
  r := biproduct.desc fun i => (biproduct.π f i)ᘁ
  retract := by
    rw [biproduct.lift_desc]
    simp only [← comp_rightAdjointMate, ← rightAdjointMate_sum, biproduct.total,
      rightAdjointMate_id]
/-- If the dual of the generator is generated, duals of its powers are generated. -/
theorem generatedBy_dualPower (X : C) (h : GeneratedBy X (Xᘁ)) :
    ∀ n, GeneratedBy X ((tensorPower X n)ᘁ)
  | 0 => by
      apply generatedBy_of_iso (generatedBy_unit X)
      let p : ExactPairing (tensorPower X 0) ((tensorPower X 0)ᘁ) := inferInstance
      let q : ExactPairing (tensorPower X 0) (𝟙_ C) := by
        change ExactPairing (𝟙_ C) (𝟙_ C)
        infer_instance
      exact rightDualIso p q
  | n + 1 => by
      apply generatedBy_of_iso
        (generatedBy_tensor X ((tensorPower X n)ᘁ) (Xᘁ) (generatedBy_dualPower X h n) h)
      exact rightDualTensorIso X (tensorPower X n)

/-- Closure under right duals reduces to the right dual of the generator. -/
theorem generatedBy_dual_of_generator_dual (X : C) (h : GeneratedBy X (Xᘁ))
    (Y : C) (hY : GeneratedBy X Y) : GeneratedBy X (Yᘁ) := by
  obtain ⟨n, k, ⟨r⟩⟩ := hY
  let B := ⨁ fun i => tensorPower X (k i)
  let rd : Retract (Yᘁ) (Bᘁ) := {
    i := r.rᘁ
    r := r.iᘁ
    retract := by rw [← comp_rightAdjointMate, r.retract, rightAdjointMate_id] }
  let rb := dualBiproductRetract n (fun i => tensorPower X (k i))
  have hg : GeneratedBy X (⨁ fun i => (tensorPower X (k i))ᘁ) :=
    generatedBy_biproduct X n _ (fun i => generatedBy_dualPower X h (k i))
  exact generatedBy_retract hg (rd.trans rb)
/-- The generated category is rigid as soon as the generator's right dual is
itself generated. -/
@[instance_reducible] def generatedCategoryRigidOfGeneratorDual (X : C)
    (h : GeneratedBy X (Xᘁ)) : RigidCategory (generatedCategory X) :=
  generatedCategoryRigidOfDualClosure X (generatedBy_dual_of_generator_dual X h)

end PropertyF
