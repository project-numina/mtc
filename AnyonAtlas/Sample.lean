module
public import AnyonAtlas.Raw
public import MTC.ModularData.Basic
public import Mathlib.Analysis.Complex.Exponential

/-!
# A small Atlas sample

The first bosonic record is the rank-one trivial theory. Its exported S and T
entries are both 1. The equality below connects this exact raw encoding to the
independently verified `MTC.ModularData.trivial`, whose structure fields include
all of the shared interface's modular-data axioms.
-/

@[expose] public section
namespace AnyonAtlas

/-- The exact first record from the Atlas export. -/
def rankOne : RawRecord where
  id := "B01-00000"
  kind := "bosonic"
  rank := 1
  s := [[[⟨1, 1, 0, 1⟩]]]
  t := [[⟨1, 1, 0, 1⟩]]

/-- Interpret the raw cyclotomic syntax in the standard complex embedding. -/
noncomputable def CyclotomicTerm.value (x : CyclotomicTerm) : ℂ :=
  ((x.coeffNum : ℂ) / (x.coeffDen : ℂ)) *
    Complex.exp (2 * Real.pi * Complex.I * ((x.phaseNum : ℂ) / (x.phaseDen : ℂ)))

/-- Evaluate a finite sum of exact cyclotomic terms. -/
noncomputable def CyclotomicExpression.value (x : CyclotomicExpression) : ℂ :=
  (x.map CyclotomicTerm.value).sum

example : rankOne.id = "B01-00000" ∧ rankOne.rank = 1 := by decide

/-- The exported S entry agrees with the checked modular-data example. -/
theorem rankOne_s : (((rankOne.s[0]!)[0]!).value) = (MTC.ModularData.trivial ℂ).S 0 0 := by
  norm_num [rankOne, CyclotomicExpression.value, CyclotomicTerm.value,
    MTC.ModularData.trivial, Matrix.one_apply]

/-- The exported T entry agrees with the checked modular-data example. -/
theorem rankOne_t : ((rankOne.t[0]!).value) = (MTC.ModularData.trivial ℂ).twist 0 := by
  norm_num [rankOne, CyclotomicExpression.value, CyclotomicTerm.value,
    MTC.ModularData.trivial]

end AnyonAtlas
