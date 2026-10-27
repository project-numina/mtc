module
public import PropertyF.Ground.Modular.SSquare

/-! Separate the linear-algebra part of nondegeneracy from the categorical
proof that centre Hopf-link characters separate simple objects. -/
@[expose] public noncomputable section
open scoped BigOperators
namespace PropertyF.Ground.CentreModular
open Modular

/-- Distinct fusion characters form an invertible evaluation matrix. -/
theorem character_matrix_det_ne_zero {ι : Type*} [Fintype ι] [DecidableEq ι]
    (N : FusionRules ι) (dual : ι → ι)
    (hdual : ∀ i j k, N.coeff i j k = N.coeff (dual i) k j)
    (cols : ι → Character N) (hinj : Function.Injective cols) :
    (Matrix.of fun i j => (cols j).value i).det ≠ 0 := by
  classical
  let A : Matrix ι ι ℂ := fun i j => (cols j).value i
  let B : Matrix ι ι ℂ := fun i j => starRingEnd ℂ ((cols i).value j)
  let w : ι → ℂ := fun i => ∑ k, starRingEnd ℂ ((cols i).value k) * (cols i).value k
  have hw (i : ι) : w i ≠ 0 := by
    let r : ℝ := ∑ j, Complex.normSq ((cols i).value j)
    have hr : 0 < r := by
      have hh := Finset.single_le_sum (f := fun j => Complex.normSq ((cols i).value j))
        (fun j _ => Complex.normSq_nonneg _) (Finset.mem_univ N.unit)
      have : 1 ≤ r := by simpa [r, (cols i).unit_eq] using hh
      linarith
    have he : w i = (r : ℂ) := by
      simp only [w, r, Complex.ofReal_sum, Complex.normSq_eq_conj_mul_self]
    rw [he]
    exact_mod_cast ne_of_gt hr
  have hBA : B * A = Matrix.diagonal w := by
    ext i j
    rw [Matrix.mul_apply, Matrix.diagonal_apply]
    by_cases h : i = j
    · subst j
      simp [A, B, w]
    · simp only [h, ite_false]
      exact character_orthogonal N dual hdual (cols i) (cols j) (fun he => h (hinj he))
  have hd : (B * A).det ≠ 0 := by
    rw [hBA, Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.mpr (fun i _ => hw i)
  rw [Matrix.det_mul] at hd
  exact (mul_ne_zero_iff.mp hd).2

/-- For any braided pivotal fusion category, categorical S is invertible iff
its normalized Hopf-link columns separate simple labels. The separation of
centre labels is a separate categorical obligation. -/
theorem categoricalS_det_ne_zero_iff_columns_injective
    (C : BraidedFusionCategory) (p : Dimensions.PivotalStructure (C := C.Obj)) :
    (categoricalS C p).det ≠ 0 ↔
      Function.Injective (fun j i => categoricalS C p i j / simpleDimension C p j) := by
  classical
  constructor
  · exact categoricalS_character_injective C p
  · intro hinj
    let rules : FusionRules (Fin (rank C)) := ⟨unitIndex C, fusionCoeff C⟩
    let cols (j : Fin (rank C)) : Character rules := {
      value := fun i => categoricalS C p i j / simpleDimension C p j
      unit_eq := by rw [categoricalS_symmetric C p, categoricalS_unit]; exact div_self (simpleDimension_ne_zero C p j)
      mul_eq := fun i k => categoricalS_verlinde C p i k j }
    have hc : Function.Injective cols := by
      intro i j h
      exact hinj (congrArg Character.value h)
    have hd := character_matrix_det_ne_zero rules (dualIndex C) (fusionCoeff_dual_adjoint C) cols hc
    let A : Matrix (Fin (rank C)) (Fin (rank C)) ℂ := fun i j => (cols j).value i
    have hS : categoricalS C p = A * Matrix.diagonal (simpleDimension C p) := by
      ext i j
      rw [Matrix.mul_diagonal]
      change categoricalS C p i j = categoricalS C p i j / simpleDimension C p j * simpleDimension C p j
      exact (div_mul_cancel₀ _ (simpleDimension_ne_zero C p j)).symm
    rw [hS, Matrix.det_mul, Matrix.det_diagonal]
    apply mul_ne_zero hd
    exact Finset.prod_ne_zero_iff.mpr (fun i _ => simpleDimension_ne_zero C p i)

end PropertyF.Ground.CentreModular
