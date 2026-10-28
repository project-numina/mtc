module
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Tactic

/-!
# The rank-11 Atlas example: exact global dimension

The first row of the unnormalized S matrix in The Anyon Atlas,
arXiv:2610.25439, equations (5.2)–(5.3), gives the positive dimensions of
B11-00119. The paper reports a unitary categorification in Section 5, so the
sum of squares is its global Frobenius–Perron dimension. These scalar
expressions do not encode the full S matrix or assert a categorification.

Here `c35 k = ζ₃₅^k + ζ₃₅^(-k)` under the standard embedding. In particular,
`c35 14 = ζ₅² + ζ₅⁻²` and `c35 7 = ζ₅ + ζ₅⁻¹`.
-/

@[expose] public noncomputable section
namespace MTC.FRSymbols.AtlasB11

/-- The real cyclotomic expression `ζ₃₅^k + ζ₃₅^(-k)`. -/
def c35 (k : ℕ) : ℝ := 2 * Real.cos (2 * Real.pi * k / 35)

/-- The value `a` in the Atlas B11-00119 vacuum row. -/
def a : ℝ := 2 + c35 4 + c35 6 - c35 8 + c35 9 - c35 12 - c35 14 - c35 17
/-- The value `b` in the Atlas B11-00119 vacuum row. -/
def b : ℝ := 2*c35 2 + 2*c35 3 + c35 4 + c35 6 + c35 9 + 2*c35 13 - 3*c35 14
/-- The value `c` in the Atlas B11-00119 vacuum row. -/
def c : ℝ := b - c35 14
/-- The value `d` in the Atlas B11-00119 vacuum row. -/
def d : ℝ := c + 1
/-- The value `e` in the Atlas B11-00119 vacuum row. -/
def e : ℝ := 2 + 3*c35 2 + 3*c35 3 + 2*c35 4 + 2*c35 6 + 2*c35 9 + 3*c35 13 - 4*c35 14
/-- The value `f` in the Atlas B11-00119 vacuum row. -/
def f : ℝ := e + c35 7

/-- Sum of squares of the dimension row `(1,a,a,a,b,c,d,d,d,e,f)`. -/
def globalDimension : ℝ := 1 + 3*a^2 + b^2 + c^2 + 3*d^2 + e^2 + f^2

/-- The vacuum contributes one, and every other contribution is nonnegative. -/
theorem one_le_globalDimension : 1 ≤ globalDimension := by
  unfold globalDimension
  nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg c, sq_nonneg d, sq_nonneg e, sq_nonneg f]

end MTC.FRSymbols.AtlasB11
