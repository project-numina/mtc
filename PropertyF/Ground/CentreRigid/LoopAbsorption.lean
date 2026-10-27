module
public import PropertyF.Ground.CentreRigid.WindingDecomposition
public import PropertyF.Ground.Fusion.Agreement

/-! FP-weighted absorption of fusion strands by closed centre windings. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
namespace PropertyF.Ground.CentreRigid
open scoped BigOperators
universe v u
attribute [local instance] Abelian.hasFiniteBiproducts
set_option backward.isDefEq.respectTransparency false in
/-- The FP weights are a left eigenvector for a simple fusion matrix. -/
theorem fp_weight_identity (C : BraidedFusionCategory.{v,u}) (k j : Fin (rank C)) :
    (∑ i, (fpSimple C i : ℂ) * (fusionCoeff C k i j : ℂ)) =
      (fpSimple C k : ℂ) * fpSimple C j := by
  have hc (i : Fin (rank C)) : fusionCoeff C k i j = fusionCoeff C (dualIndex C k) j i := by
    rw [fusionCoeff_comm C k i, fusionCoeff_reciprocity_labels, fusionCoeff_comm]
  have hf := congrArg (fun x : ℝ => (x : ℂ)) (fpSimple_mul C (dualIndex C k) j)
  rw [fpSimple_dual] at hf
  push_cast at hf
  rw [hf]
  apply Finset.sum_congr rfl
  intro i _
  rw [hc]
  ring

set_option backward.isDefEq.respectTransparency false in
/-- An FP-weighted sum of closed windings absorbs a simple tensor factor. -/
theorem fp_loop_absorption (C : BraidedFusionCategory.{v,u}) (p : Dimensions.PivotalStructure (C := C.Obj))
    (X Y : Center C.Obj) (f : X.1 ⟶ Y.1) (k : Fin (rank C)) :
    (∑ i, (fpSimple C i : ℂ) • CentreInduction.partialTraceHom p X.1 Y.1
      (simples C k ⊗ simples C i)
      (CentreInduction.winding C X Y (simples C k ⊗ simples C i) f)) =
    (fpSimple C k : ℂ) • (∑ j, (fpSimple C j : ℂ) •
      CentreInduction.partialTraceHom p X.1 Y.1 (simples C j)
        (CentreInduction.winding C X Y (simples C j) f)) := by
  calc
    _ = ∑ i, (fpSimple C i : ℂ) • ∑ j, (fusionCoeff C k i j : ℂ) •
      CentreInduction.partialTraceHom p X.1 Y.1 (simples C j)
        (CentreInduction.winding C X Y (simples C j) f) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [CentreRigid.trace_winding_simple_decomposition]
      rfl
    _ = _ := by
      simp only [Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      rw [← Finset.sum_smul, fp_weight_identity]

set_option backward.isDefEq.respectTransparency false in
/-- For FP-valued pivotal dimensions, the actual Kirby loop absorbs a simple tensor factor. -/
theorem loop_absorption (C : BraidedFusionCategory.{v,u}) (p : Dimensions.PivotalStructure (C := C.Obj))
    (hp : ∀ i, Modular.simpleDimension C p i = (fpSimple C i : ℂ))
    (X Y : Center C.Obj) (f : X.1 ⟶ Y.1) (k : Fin (rank C)) :
    (∑ i, Modular.simpleDimension C p i • CentreInduction.partialTraceHom p X.1 Y.1
      (simples C k ⊗ simples C i)
      (CentreInduction.winding C X Y (simples C k ⊗ simples C i) f)) =
    Modular.simpleDimension C p k • CentreInduction.loopSum C p X Y f := by
  simpa only [hp, CentreInduction.loopSum] using fp_loop_absorption C p X Y f k

end PropertyF.Ground.CentreRigid
