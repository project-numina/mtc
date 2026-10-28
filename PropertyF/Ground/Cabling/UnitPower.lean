module
public import PropertyF.Ground.Cabling.Generated
public import Mathlib.CategoryTheory.Monoidal.Rigid.OfEquivalence
public import Mathlib.CategoryTheory.Monoidal.Rigid.Braided
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import PropertyF.Ground.Fusion.Reciprocity
public import PropertyF.Ground.Fusion.Splitting

/-! Rigidity of the generated subcategory from closure under right duals. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [Abelian C] [MonoidalPreadditive C] [RigidCategory C]

/-- If the generated objects are closed under ambient right duals, the full
subcategory is right rigid, with the evaluation and coevaluation lifted along
the fully faithful monoidal inclusion. -/
@[instance_reducible] def generatedCategoryRightRigidOfDualClosure (X : C)
    (hdual : ∀ Y : C, GeneratedBy X Y → GeneratedBy X (Yᘁ)) :
    RightRigidCategory (generatedCategory X) where
  rightDual Y := {
    rightDual := ⟨Y.objᘁ, hdual Y.obj Y.property⟩
    exact := by
      let _ : ExactPairing ((generatedInclusion X).obj Y)
          ((generatedInclusion X).obj ⟨Y.objᘁ, hdual Y.obj Y.property⟩) :=
        inferInstanceAs (ExactPairing Y.obj Y.objᘁ)
      exact ExactPairing.ofFullyFaithful (generatedInclusion X) _ _
  }

/-- Braiding turns right rigidity into full rigidity. -/
@[instance_reducible] def generatedCategoryRigidOfDualClosure (X : C)
    (hdual : ∀ Y : C, GeneratedBy X Y → GeneratedBy X (Yᘁ)) :
    RigidCategory (generatedCategory X) := by
  let _ := generatedCategoryRightRigidOfDualClosure X hdual
  exact BraidedCategory.rigidCategoryOfRightRigidCategory

end PropertyF

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
def dualBiproductRetract {ι : Type} [Fintype ι] (f : ι → C) :
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
  let rb := dualBiproductRetract (fun i => tensorPower X (k i))
  have hg : GeneratedBy X (⨁ fun i => (tensorPower X (k i))ᘁ) :=
    generatedBy_biproduct X n _ (fun i => generatedBy_dualPower X h (k i))
  exact generatedBy_retract hg (rd.trans rb)
/-- The generated category is rigid as soon as the generator's right dual is
itself generated. -/
@[instance_reducible] def generatedCategoryRigidOfGeneratorDual (X : C)
    (h : GeneratedBy X (Xᘁ)) : RigidCategory (generatedCategory X) :=
  generatedCategoryRigidOfDualClosure X (generatedBy_dual_of_generator_dual X h)

end PropertyF

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
@[expose] public noncomputable section
namespace PropertyF.Ground.Cabling
universe v u

set_option backward.isDefEq.respectTransparency false in
/-- A positive tensor power containing the unit makes the simple generator's
right dual a retract of a lower tensor power. -/
theorem generatedBy_rightDual_of_unit_power (D : Ground.BraidedFusionCategory.{v,u})
    (X : D.Obj) [Simple X] (n : ℕ) (r : Retract (𝟙_ D.Obj) (tensorPower X (n + 1))) :
    GeneratedBy X (Xᘁ) := by
  let _ : Simple (𝟙_ D.Obj) := Ground.IsFusionCategory.unit_simple
  let _ : Simple (Xᘁ) := Ground.simple_rightDual D X
  have hi : r.i ≠ 0 := by
    intro h
    have hr := r.retract
    rw [h, zero_comp] at hr
    exact id_nonzero (𝟙_ D.Obj) hr.symm
  let f : Xᘁ ⊗ 𝟙_ D.Obj ⟶ tensorPower X n :=
    (tensorLeftHomEquiv (𝟙_ D.Obj) X (Xᘁ) (tensorPower X n)).symm r.i
  have hf : f ≠ 0 := by
    intro h
    let e := tensorLeftHomEquiv (𝟙_ D.Obj) X (Xᘁ) (tensorPower X n)
    have he0 : e 0 = 0 := by simp [e, tensorLeftHomEquiv]
    have he := congrArg e h
    apply hi
    change e (e.symm r.i) = e 0 at he
    rw [Equiv.apply_symm_apply, he0] at he
    exact he
  let g : Xᘁ ⟶ tensorPower X n := (ρ_ (Xᘁ)).inv ≫ f
  have hg : g ≠ 0 := by
    intro h
    apply hf
    have hh := congrArg (fun z => (ρ_ (Xᘁ)).hom ≫ z) h
    simpa [g, Category.assoc] using hh
  obtain ⟨s, hs⟩ := Ground.split_from_simple g hg
  exact generatedBy_retract (generatedBy_tensorPower X n) { i := g, r := s, retract := hs }
end PropertyF.Ground.Cabling
