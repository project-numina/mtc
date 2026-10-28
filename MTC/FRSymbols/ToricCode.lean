module
public import MTC.FRSymbols.Pointed
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic

/-!
# Toric code F and R symbols

The simple labels are `(electric, magnetic)` in `ℤ/2 × ℤ/2`; the tensor
product adds labels. In a standard skeletal gauge the associator is trivial
and `R((a,b),(c,d)) = (-1)^(a*d)`. This is the untwisted quantum double of
`ℤ/2`, also known as the toric code. Coefficients lie in `ℚ`, hence in every
cyclotomic extension of `ℚ`. The proofs check the complete pentagon and both
hexagons, not a floating-point approximation.

See Kitaev, *Fault-tolerant quantum computation by anyons*,
arXiv:quant-ph/9707021, Section 8, and Etingof et al., *Tensor Categories*,
Section 8.4 for the pointed cocycle convention.
-/

@[expose] public section
namespace MTC.FRSymbols.Pointed.ToricCode

abbrev Label := ZMod 2 × ZMod 2

/-- The nontrivial crossing is an electric charge passing a magnetic flux. -/
def braiding (a b : Label) : ℚˣ :=
  if a.1 = 1 ∧ b.2 = 1 then -1 else 1

private theorem bit_cases (x : ZMod 2) : x = 0 ∨ x = 1 := by
  fin_cases x <;> first | exact Or.inl rfl | exact Or.inr rfl

/-- Exact toric-code F and R symbols. -/
def symbols : Symbols Label ℚˣ where
  F := fun _ _ _ => 1
  R := braiding
  F_zero_left := by intros; rfl
  F_zero_middle := by intros; rfl
  F_zero_right := by intros; rfl
  R_zero_left := by decide
  R_zero_right := by decide
  pentagon := by intros; simp
  hexagon₁ := by
    intro ⟨a, a'⟩ ⟨b, b'⟩ ⟨c, c'⟩
    rcases bit_cases a with rfl | rfl <;>
      rcases bit_cases b' with rfl | rfl <;>
      rcases bit_cases c' with rfl | rfl <;>
      simp [braiding, show (0 : ZMod 2) ≠ 1 by decide,
        show (1 : ZMod 2) + 1 = 0 by decide]
  hexagon₂ := by
    intro ⟨a, a'⟩ ⟨b, b'⟩ ⟨c, c'⟩
    rcases bit_cases a with rfl | rfl <;>
      rcases bit_cases b with rfl | rfl <;>
      rcases bit_cases c' with rfl | rfl <;>
      simp [braiding, show (0 : ZMod 2) ≠ 1 by decide,
        show (1 : ZMod 2) + 1 = 0 by decide]

/-- A nontrivial exchange and its opposite, fixing the R-symbol convention. -/
theorem electric_magnetic : symbols.R (1, 0) (0, 1) = -1 := by decide

theorem magnetic_electric : symbols.R (0, 1) (1, 0) = 1 := by decide

/-- The exact solution is unitary in the standard complex embedding of `ℚ`. -/
theorem unitary : IsUnitary (algebraMap ℚ ℂ) symbols := by
  constructor
  · intro a b c
    norm_num [symbols, IsUnitary]
  · intro a b
    simp only [symbols, braiding]
    split <;> norm_num [Complex.normSq_apply]

end MTC.FRSymbols.Pointed.ToricCode
