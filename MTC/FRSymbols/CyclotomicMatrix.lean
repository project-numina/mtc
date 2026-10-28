module
public import MTC.FRSymbols.MatrixSymbols
public import MTC.FRSymbols.Cyclotomic

/-!
# Exact and complex unitarity

The involution on the cyclotomic quotient agrees with complex conjugation in
the standard embedding. The unitarity conditions on exact F/R blocks can
therefore be checked in the coefficient field, including for `n = 70`.
-/

@[expose] public noncomputable section
namespace MTC.FRSymbols

variable {L : Type*} [Fintype L] [DecidableEq L] {rules : FusionRules L}

/-- Matrix unitarity over the exact field is equivalent to unitarity after
embedding its coefficients in the complex numbers. -/
theorem cyclotomic_unitary_iff (n : ℕ) [NeZero n]
    (s : MatrixSymbols rules (ExactCyclotomic n)) :
    s.UnitaryVia (cyclotomicEmbedding n) ↔ s.Unitary := by
  apply s.unitaryVia_iff (cyclotomicEmbedding n)
  · exact (cyclotomicEmbedding n).injective
  · exact cyclotomicEmbedding_map_star n

end MTC.FRSymbols
