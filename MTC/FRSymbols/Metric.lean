module
public import MTC.FRSymbols.MatrixSymbols
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Tactic

/-!
# Unitarity with nonorthonormal fusion bases

A unitary category may be expressed in bases that are not orthonormal. In
such a basis F and R need not be ordinary unitary matrices. This file defines
positive Hermitian Gram matrices on the trivalent fusion spaces and their
factorized forms on the two three-object fusion trees. F and R must preserve
these Gram matrices. The definition makes the consistency of the bases
explicit; an arbitrary independently chosen metric for each F block would be
too weak.

This is a necessary matrix-level condition, not a reconstruction theorem.
In particular, it does not establish triangle, rigidity, or compatibility
with a dagger structure on all morphisms.
-/

@[expose] public section
open scoped BigOperators
namespace MTC.FRSymbols

/-- A finite Hermitian Gram matrix is positive definite if its quadratic form
has positive real part on every nonzero vector. -/
def PositiveHermitian {I : Type*} [Fintype I] (H : Matrix I I ℂ) : Prop :=
  (∀ i j, H i j = star (H j i)) ∧
  ∀ v : I → ℂ, v ≠ 0 → 0 < (∑ i, ∑ j, star (v i) * H i j * v j).re

/-- The standard Hermitian metric on a one-dimensional fusion space is positive. -/
theorem positiveHermitian_one_dim : PositiveHermitian (1 : Matrix (Fin 1) (Fin 1) ℂ) := by
  constructor
  · intro i j
    fin_cases i
    fin_cases j
    simp
  · intro v hv
    have hv0 : v 0 ≠ 0 := by
      intro h
      apply hv
      funext i
      fin_cases i
      simpa using h
    have hp := Complex.normSq_pos.mpr hv0
    simp only [Fin.sum_univ_one, Matrix.one_apply, ite_true, mul_one]
    change 0 < ((starRingEnd ℂ (v 0)) * v 0).re
    rw [← Complex.normSq_eq_conj_mul_self]
    exact hp

variable {L K : Type*} [Fintype L] [DecidableEq L] [CommSemiring K]
variable {n : FusionRules L}

/-- Compatible positive metrics making all F and R blocks isometries, relative
to an embedding of the coefficients into ℂ. The tree metrics are required to
factor through the same trivalent metrics and to make distinct intermediate
simple labels orthogonal. Combine this with `MatrixSymbols.Invertible` and the
coherence equations when checking a complete symbol system. -/
structure MatrixSymbols.UnitaryMetric (s : MatrixSymbols n K) (ι : K →+* ℂ) where
  vertex : ∀ a b c, Matrix (Fin (n.N a b c)) (Fin (n.N a b c)) ℂ
  left : ∀ a b c d, Matrix (LeftTree n a b c d) (LeftTree n a b c d) ℂ
  right : ∀ a b c d, Matrix (RightTree n a b c d) (RightTree n a b c d) ℂ
  vertex_positive : ∀ a b c, PositiveHermitian (vertex a b c)
  left_positive : ∀ a b c d, PositiveHermitian (left a b c d)
  right_positive : ∀ a b c d, PositiveHermitian (right a b c d)
  left_orthogonal : ∀ a b c d (i j : LeftTree n a b c d),
    i.1 ≠ j.1 → left a b c d i j = 0
  right_orthogonal : ∀ a b c d (i j : RightTree n a b c d),
    i.1 ≠ j.1 → right a b c d i j = 0
  left_factor : ∀ a b c d e (u u' : Fin (n.N a b e)) (v v' : Fin (n.N e c d)),
    left a b c d ⟨e, u, v⟩ ⟨e, u', v'⟩ = vertex a b e u u' * vertex e c d v v'
  right_factor : ∀ a b c d e (u u' : Fin (n.N b c e)) (v v' : Fin (n.N a e d)),
    right a b c d ⟨e, u, v⟩ ⟨e, u', v'⟩ = vertex b c e u u' * vertex a e d v v'
  F_isometry : ∀ a b c d (i j : LeftTree n a b c d),
    left a b c d i j = ∑ k : RightTree n a b c d, ∑ l : RightTree n a b c d,
      star (ι (s.F a b c d i k)) * right a b c d k l * ι (s.F a b c d j l)
  R_isometry : ∀ a b c (i j : Fin (n.N a b c)),
    vertex a b c i j = ∑ k : Fin (n.N b a c), ∑ l : Fin (n.N b a c),
      star (ι (s.R a b c i k)) * vertex b a c k l * ι (s.R a b c j l)

end MTC.FRSymbols
