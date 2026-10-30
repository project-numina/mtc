module
public import MTC.PropertyF.Statement

open MTC.Braided

/-!
# Galois divisibility for simple FP dimensions

Status: open
Source: Ostrik, arXiv:0810.3242, Remark 1.9(i).
Declaration: MTC.Conjectures.Galois.simpleFPDimension_dNumber

Is the FP dimension of every simple object of a braided fusion category a
`d`-number? The assertion below records a positive answer: every Galois
conjugate is divisible by the dimension in the algebraic integers. The
numerator and denominator are nonzero for standard FP dimensions. The
nonbraided analogue fails for an example related to the Haagerup subfactor,
while the squared categorical norm is known to be a d-number in the braided
case (Ostrik, Theorem 1.8). Matching the frozen spectral-radius definition
with the usual FP dimension and proving its positivity are separate tasks.
-/

@[expose] public noncomputable section
namespace MTC.Conjectures.Galois
open MTC
universe v u

/-- A proposed positive answer to Ostrik's braided d-number question. -/
theorem simpleFPDimension_dNumber (C : BraidedFusionCategory.{v,u})
    (i : Fin (rank C)) :
    fpSimple C i ≠ 0 ∧ IsIntegral ℤ (fpSimple C i) ∧
      ∀ σ : ℂ ≃+* ℂ,
        IsIntegral ℤ (σ (fpSimple C i : ℂ) / (fpSimple C i : ℂ)) := by
  sorry

/-- Dimension one meets the divisibility condition. -/
example (σ : ℂ ≃+* ℂ) : IsIntegral ℤ (σ (1 : ℂ) / 1) := by
  simpa using (isIntegral_one : IsIntegral ℤ (1 : ℂ))

end MTC.Conjectures.Galois
