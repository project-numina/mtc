module
public import PropertyF.Ground.Calculus.Unitarization
public import PropertyF.UnitaryTrace
public import Mathlib.GroupTheory.OrderOfElement

/-! Finite-order matrices have unitary representatives. -/

@[expose] public noncomputable section
open scoped BigOperators
namespace PropertyF.Ground.CentreCabling

/-- A finite-order complex matrix can be conjugated to a unitary matrix. -/
theorem finiteOrder_matrix_unitarizable {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℂ) (hM : IsOfFinOrder M) :
    ∃ P : (Matrix ι ι ℂ)ˣ, ((P : Matrix ι ι ℂ) * M * (↑(P⁻¹) : Matrix ι ι ℂ)) ∈ Matrix.unitaryGroup ι ℂ := by
  classical
  let u : (Matrix ι ι ℂ)ˣ := hM.isUnit.unit
  have hu : (u : Matrix ι ι ℂ) = M := hM.isUnit.unit_spec
  have hufin : IsOfFinOrder u := by
    obtain ⟨n, hn, hp⟩ := hM.exists_pow_eq_one
    apply isOfFinOrder_iff_pow_eq_one.mpr
    refine ⟨n, hn, ?_⟩
    apply Units.ext
    simpa [hu] using hp
  let G := Subgroup.zpowers u
  letI : Finite G := hufin.finite_zpowers
  letI : Fintype G := Fintype.ofFinite G
  obtain ⟨P, hP⟩ := Calculus.exists_unitarizing_basis G.subtype
  let g : G := ⟨u, Subgroup.mem_zpowers u⟩
  exact ⟨P, by simpa [g, hu] using hP g⟩

/-- A finite-order matrix has real trace at most its size, with equality
only for the identity. -/
theorem finiteOrder_matrix_trace_saturation {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℂ) (hM : IsOfFinOrder M) :
    M.trace.re ≤ Fintype.card ι ∧
      (M.trace.re = Fintype.card ι → M = 1) := by
  obtain ⟨P, hP⟩ := finiteOrder_matrix_unitarizable M hM
  let U : Matrix ι ι ℂ := (P : Matrix ι ι ℂ) * M * (↑(P⁻¹) : Matrix ι ι ℂ)
  have ht : U.trace = M.trace := by
    dsimp [U]
    rw [Matrix.trace_mul_cycle]
    simp [← Units.val_mul]
  have hu : PropertyF.ColumnUnitary U := PropertyF.columnUnitary_of_unitary hP
  constructor
  · rw [← ht]
    exact (Complex.re_le_norm _).trans (PropertyF.norm_trace_le_card hu)
  · intro heq
    have hU : U = 1 := PropertyF.eq_one_of_re_trace_eq_card hu (by rw [ht]; exact heq)
    have hh := congrArg (fun A : Matrix ι ι ℂ => (↑(P⁻¹) : Matrix ι ι ℂ) * A * (P : Matrix ι ι ℂ)) hU
    simpa [U, Matrix.mul_assoc, ← Units.val_mul] using hh

end PropertyF.Ground.CentreCabling
