module
public import PropertyF.Ground.Calculus.UnitaryBlocks
public import PropertyF.Ground.Calculus.CyclicTrace
public import PropertyF.Ground.Dimensions.Trace

/-! Categorical pivotal traces in matrix-block presentations. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
open scoped BigOperators
namespace PropertyF.Ground.Calculus

universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
  [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]

/-- The actual pivotal trace, evaluated using an identification of the unit
endomorphism algebra with the complex numbers. -/
def pivotalTraceLinear (p : Dimensions.PivotalStructure (C := C))
    (scalar : End (𝟙_ C) ≃ₐ[ℂ] ℂ) (X : C) : End X →ₗ[ℂ] ℂ where
  toFun x := scalar (p.rightTrace x.asHom)
  map_add' x y := by simp [Dimensions.PivotalStructure.rightTrace_add]
  map_smul' z x := by simp [Dimensions.PivotalStructure.rightTrace_smul]

/-- Pivotal trace is cyclic on the categorical endomorphism algebra. -/
theorem pivotalTraceLinear_cyclic (p : Dimensions.PivotalStructure (C := C))
    (scalar : End (𝟙_ C) ≃ₐ[ℂ] ℂ) (X : C) (a b : End X) :
    pivotalTraceLinear p scalar X (a * b) = pivotalTraceLinear p scalar X (b * a) := by
  change scalar (p.rightTrace (b.asHom ≫ a.asHom)) =
    scalar (p.rightTrace (a.asHom ≫ b.asHom))
  rw [p.rightTrace_cyclic]

variable [BraidedCategory C]

/-- The actual pivotal trace on the braid algebra, written in any matrix-block
presentation, is a weighted sum of ordinary traces. The weights are complex;
their categorical formula and reality are further obligations. -/
theorem pivotalTrace_braidBlocks (p : Dimensions.PivotalStructure (C := C))
    (scalar : End (𝟙_ C) ≃ₐ[ℂ] ℂ) (X : C) (n r : ℕ) (d : Fin r → ℕ)
    (e : braidAlgebra X n ≃ₐ[ℂ] ∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ) :
    ∃ w : Fin r → ℂ, ∀ a : braidAlgebra X n,
      pivotalTraceLinear p scalar (tensorPower X (n + 2)) a =
        ∑ i, w i * (e a i).trace := by
  let T : (∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ) →ₗ[ℂ] ℂ :=
    (pivotalTraceLinear p scalar (tensorPower X (n + 2))).comp
      ((braidAlgebra X n).val.toLinearMap.comp e.symm.toLinearEquiv.toLinearMap)
  have hT : ∀ a b, T (a * b) = T (b * a) := by
    intro a b
    change pivotalTraceLinear p scalar _ ((e.symm (a * b) : braidAlgebra X n) : End (tensorPower X (n + 2))) =
      pivotalTraceLinear p scalar _ ((e.symm (b * a) : braidAlgebra X n) : End (tensorPower X (n + 2)))
    simp only [map_mul, Subalgebra.coe_mul]
    exact pivotalTraceLinear_cyclic p scalar _ _ _
  obtain ⟨w, hw⟩ := cyclic_block_trace d T hT
  refine ⟨w, fun a => ?_⟩
  have h := hw (e a)
  change pivotalTraceLinear p scalar _ ((e.symm (e a) : braidAlgebra X n) : End (tensorPower X (n + 2))) = _ at h
  rw [e.symm_apply_apply] at h
  exact h

end PropertyF.Ground.Calculus
