module
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Tactic

/-!
# Exact modular data

We use the unnormalized convention of the Anyon Atlas: `S 0 0 = 1`, the
unit row contains quantum dimensions, and `S * S = D² C`. The scalar field
may be a decidable exact cyclotomic field with its complex conjugation. This is
an algebraic interface: it does not assert that the data are realized by a
ribbon fusion category. The conditions here are necessary, not a complete
axiomatization of realizability.

Reference: arXiv:1310.7050, Section 2.2.6, and
https://anyonatlas.org/documentation (derived data conventions).
-/

@[expose] public section
open scoped BigOperators
namespace MTC

/-- Unnormalized modular data over a field with conjugation. Labels are `Fin n`;
`vacuum` need not be the first label. The Verlinde equation is cleared of the
global-dimension denominator, but retains the nonzero unit-row denominators. -/
structure ModularData (K : Type*) [Field K] [StarRing K] (n : ℕ) where
  vacuum : Fin n
  dual : Fin n → Fin n
  dual_involutive : Function.Involutive dual
  dual_vacuum : dual vacuum = vacuum
  S : Matrix (Fin n) (Fin n) K
  twist : Fin n → K
  fusion : Fin n → Fin n → Fin n → ℕ
  S_symmetric : S.transpose = S
  unit_normalized : S vacuum vacuum = 1
  unit_row_ne_zero : ∀ i, S vacuum i ≠ 0
  dimension_ne_zero : (∑ i, S vacuum i ^ 2) ≠ 0
  twist_vacuum : twist vacuum = 1
  twist_unitary : ∀ i, star (twist i) * twist i = 1
  twist_finite : ∃ N : ℕ, 0 < N ∧ ∀ i, twist i ^ N = 1
  unitary : S * S.conjTranspose = (∑ i, S vacuum i ^ 2) • 1
  square : ∀ i j, (S * S) i j =
    if dual i = j then ∑ k, S vacuum k ^ 2 else 0
  modular_relation : (S * Matrix.diagonal twist) ^ 3 =
    (∑ i, S vacuum i ^ 2 * twist i) • (S * S)
  verlinde : ∀ i j k, ∑ x, S i x * S j x * S (dual k) x / S vacuum x =
    (∑ x, S vacuum x ^ 2) * (fusion i j k : K)

namespace ModularData
variable {K : Type*} [Field K] [StarRing K] {n : ℕ} (d : ModularData K n)

/-- The square of the total quantum dimension in the chosen normalization. -/
def globalDimension : K := ∑ i, d.S d.vacuum i ^ 2

/-- The positive Gauss sum in the chosen normalization. -/
def gaussSum : K := ∑ i, d.S d.vacuum i ^ 2 * d.twist i

@[simp] theorem globalDimension_ne_zero : d.globalDimension ≠ 0 := d.dimension_ne_zero

@[simp] theorem vacuum_dimension : d.S d.vacuum d.vacuum = 1 := d.unit_normalized

include d in
/-- A modular datum has at least one label: the tensor unit. -/
theorem rank_pos : 0 < n := Fin.pos_iff_nonempty.mpr ⟨d.vacuum⟩

end ModularData
end MTC

namespace MTC.ModularData

/-- The modular data of the trivial rank-one theory over any exact scalar field. -/
def trivial (K : Type*) [Field K] [StarRing K] : ModularData K 1 where
  vacuum := 0
  dual := id
  dual_involutive := by intro i; rfl
  dual_vacuum := rfl
  S := 1
  twist := fun _ => 1
  fusion := fun _ _ _ => 1
  S_symmetric := by simp
  unit_normalized := by simp
  unit_row_ne_zero := by intro i; fin_cases i; norm_num [Matrix.one_apply]
  dimension_ne_zero := by simp
  twist_vacuum := rfl
  twist_unitary := by intro i; simp
  twist_finite := ⟨1, by decide, by intro i; simp⟩
  unitary := by ext i j; fin_cases i; fin_cases j; simp
  square := by intro i j; fin_cases i; fin_cases j; simp
  modular_relation := by
    ext i j
    fin_cases i
    fin_cases j
    simp [Matrix.diagonal_one]
  verlinde := by intro i j k; fin_cases i; fin_cases j; fin_cases k; norm_num [Matrix.one_apply]

@[simp] theorem trivial_globalDimension (K : Type*) [Field K] [StarRing K] :
    (trivial K).globalDimension = 1 := by
  simp [globalDimension, trivial]

/-- The trivial datum also exists over the decidable exact field of rationals. -/
example : (trivial ℚ).globalDimension = 1 := by
  norm_num [globalDimension, trivial]

end MTC.ModularData
