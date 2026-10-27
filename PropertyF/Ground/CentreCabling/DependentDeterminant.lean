module
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.StdBasis
public import Mathlib.Data.Complex.Basic

/-! Determinants of componentwise scalar maps on dependent products. -/
@[expose] public noncomputable section
open scoped BigOperators
namespace PropertyF.Ground.CentreCabling

/-- A componentwise scalar map on a finite dependent product has determinant
 equal to the product of the scalars, counted by each component dimension. -/
theorem det_dependent_pi_scalar {ι : Type*} [Fintype ι] (V : ι → Type*)
    [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
    [∀ i, FiniteDimensional ℂ (V i)] (c : ι → ℂ) :
    (LinearMap.pi (fun i => (c i • (1 : V i →ₗ[ℂ] V i)).comp
      (LinearMap.proj i))).det = ∏ i, c i ^ Module.finrank ℂ (V i) := by
  classical
  let b : ∀ i, Module.Basis (Fin (Module.finrank ℂ (V i))) ℂ (V i) :=
    fun i => Module.finBasis ℂ (V i)
  let B := Pi.basis b
  let f := LinearMap.pi (fun i => (c i • (1 : V i →ₗ[ℂ] V i)).comp
      (LinearMap.proj i))
  have hm : LinearMap.toMatrix B B f = Matrix.diagonal (fun q => c q.1) := by
    ext ⟨i, k⟩ ⟨j, l⟩
    dsimp only [B, f]
    simp only [LinearMap.toMatrix_apply, Matrix.diagonal_apply, Pi.basis_apply,
      Pi.basis_repr, LinearMap.pi_apply, LinearMap.coe_comp, Function.comp_apply,
      LinearMap.smul_apply, LinearMap.coe_proj, Function.eval, LinearMap.id_coe,
      id_eq]
    by_cases h : i = j
    · subst j
      simp [Finsupp.single_apply, eq_comm]
    · simp [Pi.single_apply, h, Ne.symm h]
  rw [← LinearMap.det_toMatrix B, hm, Matrix.det_diagonal, Fintype.prod_sigma]
  simp

end PropertyF.Ground.CentreCabling
