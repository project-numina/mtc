module
public import PropertyF.Ground.Cabling.DualClosure
public import PropertyF.Ground.Fusion.Reciprocity
public import PropertyF.Ground.Fusion.Splitting
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
