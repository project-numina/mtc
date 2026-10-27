module
public import PropertyF.Ground.CentreRigid.NestedTrace
public import PropertyF.Ground.CentreRigid.LoopAbsorption

/-! The FP-normalized Kirby loop is an idempotent on underlying Hom spaces. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
namespace PropertyF.Ground.CentreRigid
open scoped BigOperators
universe v u
set_option backward.isDefEq.respectTransparency false in
/-- Linear winding map on underlying centre Hom spaces. -/
def windingLinear (C : BraidedFusionCategory.{v,u}) (X Y : Center C.Obj)
    (T : C.Obj) : (X.1 ⟶ Y.1) →ₗ[ℂ] (X.1 ⊗ T ⟶ Y.1 ⊗ T) where
  toFun f := CentreInduction.winding C X Y T f
  map_add' f g := by simp [CentreInduction.winding]
  map_smul' c f := by simp [CentreInduction.winding]

/-- Linear closed winding map on underlying centre Hom spaces. -/
def closedWinding (C : BraidedFusionCategory.{v,u})
    (p : Dimensions.PivotalStructure (C := C.Obj)) (X Y : Center C.Obj) (T : C.Obj) :
    (X.1 ⟶ Y.1) →ₗ[ℂ] (X.1 ⟶ Y.1) :=
  (CentreInduction.partialTraceHom p X.1 Y.1 T).comp (windingLinear C X Y T)

set_option backward.isDefEq.respectTransparency false in
/-- Closed winding on a tensor product is composition of closed winding maps. -/
theorem closedWinding_tensor (C : BraidedFusionCategory.{v,u}) (p : Dimensions.PivotalStructure (C := C.Obj))
    (X Y : Center C.Obj) (f : X.1 ⟶ Y.1) (T U : C.Obj) :
    closedWinding C p X Y (T ⊗ U) f =
      closedWinding C p X Y T (closedWinding C p X Y U f) := by
  dsimp [closedWinding, windingLinear]
  rw [CentreRigid.partialTraceHom_nested, CentreRigid.trace_inner_winding_tensor]

set_option backward.isDefEq.respectTransparency false in
/-- Each simple closed winding scales the FP-weighted Kirby loop. -/
theorem loop_eigen (C : BraidedFusionCategory.{v,u}) (p : Dimensions.PivotalStructure (C := C.Obj))
    (hp : ∀ i, Modular.simpleDimension C p i = (fpSimple C i : ℂ))
    (X Y : Center C.Obj) (f : X.1 ⟶ Y.1) (k : Fin (rank C)) :
    closedWinding C p X Y (simples C k) (CentreInduction.loopSum C p X Y f) =
      (fpSimple C k : ℂ) • CentreInduction.loopSum C p X Y f := by
  have h := CentreRigid.loop_absorption C p hp X Y f k
  change (∑ i, Modular.simpleDimension C p i • closedWinding C p X Y
      (simples C k ⊗ simples C i) f) = _ at h
  simp only [closedWinding_tensor] at h
  have he : CentreInduction.loopSum C p X Y f =
      ∑ i, Modular.simpleDimension C p i • closedWinding C p X Y (simples C i) f := rfl
  rw [he] at h ⊢
  rw [map_sum]
  simp only [map_smul]
  simpa only [hp] using h

set_option backward.isDefEq.respectTransparency false in
/-- The unnormalized Kirby loop squares to global FP dimension times itself. -/
theorem loop_square (C : BraidedFusionCategory.{v,u}) (p : Dimensions.PivotalStructure (C := C.Obj))
    (hp : ∀ i, Modular.simpleDimension C p i = (fpSimple C i : ℂ))
    (X Y : Center C.Obj) (f : X.1 ⟶ Y.1) :
    CentreInduction.loopSum C p X Y (CentreInduction.loopSum C p X Y f) =
      (globalFPDimension C : ℂ) • CentreInduction.loopSum C p X Y f := by
  change (∑ i, Modular.simpleDimension C p i • closedWinding C p X Y (simples C i)
    (CentreInduction.loopSum C p X Y f)) = _
  simp_rw [loop_eigen C p hp]
  simp only [hp, smul_smul, ← Finset.sum_smul]
  congr 1
  simp [globalFPDimension, Complex.ofReal_sum, pow_two]

set_option backward.isDefEq.respectTransparency false in
/-- The normalized loop is idempotent, without assuming its output is central. -/
theorem normalized_loop_idempotent (C : BraidedFusionCategory.{v,u}) (p : Dimensions.PivotalStructure (C := C.Obj))
    (hp : ∀ i, Modular.simpleDimension C p i = (fpSimple C i : ℂ))
    (X Y : Center C.Obj) (f : X.1 ⟶ Y.1) :
    let d : ℂ := globalFPDimension C
    let a := fun g : X.1 ⟶ Y.1 => d⁻¹ • CentreInduction.loopSum C p X Y g
    a (a f) = a f := by
  let d : ℂ := globalFPDimension C
  have hd : d ≠ 0 := by
    dsimp [d]
    exact_mod_cast (ne_of_gt (lt_of_lt_of_le zero_lt_one (one_le_globalFPDimension C)))
  have hs (c : ℂ) (g : X.1 ⟶ Y.1) :
      CentreInduction.loopSum C p X Y (c • g) = c • CentreInduction.loopSum C p X Y g := by
    change (∑ i, Modular.simpleDimension C p i • closedWinding C p X Y (simples C i) (c • g)) = _
    change (∑ i, Modular.simpleDimension C p i • closedWinding C p X Y (simples C i) (c • g)) =
      c • (∑ i, Modular.simpleDimension C p i • closedWinding C p X Y (simples C i) g)
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [map_smul, smul_comm]
  change d⁻¹ • CentreInduction.loopSum C p X Y (d⁻¹ • CentreInduction.loopSum C p X Y f) = _
  rw [hs, loop_square C p hp]
  change d⁻¹ • (d⁻¹ • (d • CentreInduction.loopSum C p X Y f)) = d⁻¹ • CentreInduction.loopSum C p X Y f
  simp [smul_smul, hd]

end PropertyF.Ground.CentreRigid
