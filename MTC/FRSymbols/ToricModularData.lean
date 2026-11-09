module
public import MTC.FRSymbols.ToricCode
public import MTC.Modular.Data.Basic

/-!
# Toric-code modular data from R symbols

With the canonical pointed ribbon structure, the unnormalized Hopf-link
matrix is the double braiding `R(a,b) R(b,a)` and the twist is the
self-braiding `R(a,a)`. This is the Atlas convention `S[0,0] = 1`.
We verify the numerical modular-data axioms over the exact field `ℚ`.
This is a numerical bridge and does not claim a reconstruction of the category.

Reference: Etingof, Gelaki, Nikshych and Ostrik, *Tensor Categories*, Section
8.4 (pointed braided categories) and Section 8.13 (modular data).
-/

@[expose] public section
open scoped BigOperators
namespace MTC.FRSymbols.Pointed.ToricCode

/-- The order of the four simples is vacuum, electric, magnetic, fermion. -/
def label : Fin 4 → Label := ![(0, 0), (1, 0), (0, 1), (1, 1)]

/-- Unnormalized Hopf-link matrix, computed from the double braiding. -/
def hopfLink : Matrix (Fin 4) (Fin 4) ℚ := fun i j =>
  (symbols.R (label i) (label j) * symbols.R (label j) (label i) : ℚˣ)

/-- The canonical twist of each pointed simple object. -/
def twist (i : Fin 4) : ℚ := (symbols.R (label i) (label i) : ℚˣ)

/-- Multiplicity of `k` in the fusion of `i` and `j`. -/
def fusion (i j k : Fin 4) : ℕ := if Nat.xor i.val j.val = k.val then 1 else 0

/-- The bitwise fusion table agrees with addition of the simple labels. -/
theorem fusion_eq_label_add (i j k : Fin 4) :
    fusion i j k = if label i + label j = label k then 1 else 0 := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;> decide

/-- The toric-code F/R solution determines these exact modular data. -/
def modularData : MTC.Modular.Data ℚ 4 where
  vacuum := 0
  dual := id
  dual_involutive := by intro i; rfl
  dual_vacuum := rfl
  S := hopfLink
  twist := twist
  fusion := fusion
  S_symmetric := by ext i j; change hopfLink j i = hopfLink i j; simp [hopfLink, mul_comm]
  unit_normalized := by norm_num [hopfLink, label, symbols, braiding]
  unit_row_ne_zero := by intro i; fin_cases i <;> norm_num [hopfLink, label, symbols, braiding]
  dimension_ne_zero := by norm_num [hopfLink, label, symbols, braiding, Fin.sum_univ_succ]
  twist_vacuum := by norm_num [twist, label, symbols, braiding]
  twist_unitary := by intro i; fin_cases i <;> norm_num [twist, label, symbols, braiding]
  twist_finite := ⟨2, by decide, by intro i; fin_cases i <;>
    norm_num [twist, label, symbols, braiding]⟩
  unitary := by
    ext i j
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.smul_apply,
      Matrix.one_apply]
    fin_cases i <;> fin_cases j <;>
      norm_num [hopfLink, label, symbols, braiding, Fin.sum_univ_succ]
  square := by
    intro i j
    simp only [Matrix.mul_apply]
    fin_cases i <;> fin_cases j <;>
      norm_num [hopfLink, label, symbols, braiding, Fin.sum_univ_succ]
  modular_relation := by
    ext i j
    simp only [pow_succ, pow_zero, one_mul, Matrix.mul_apply, Matrix.smul_apply]
    fin_cases i <;> fin_cases j <;>
      norm_num [hopfLink, twist, label, symbols, braiding,
        Matrix.diagonal_apply, Fin.sum_univ_succ]
  verlinde := by
    intro i j k
    fin_cases i <;> fin_cases j <;> fin_cases k <;>
      norm_num [hopfLink, fusion, label, symbols, braiding, Fin.sum_univ_succ]

/-- The total squared quantum dimension is four. -/
theorem globalDimension : modularData.globalDimension = 4 := by
  norm_num [MTC.Modular.Data.globalDimension, modularData, hopfLink, label, symbols,
    braiding, Fin.sum_univ_succ]

end MTC.FRSymbols.Pointed.ToricCode
