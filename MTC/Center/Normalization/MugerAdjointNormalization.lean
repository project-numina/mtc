module
public import MTC.Center.Normalization.AdjointQuotient
public import MTC.Center.Normalization.MugerLabels

open MTC.Fusion MTC.Braided MTC.CategoryTheory.Dimensions

/-! # Normalization on the Müger centre from adjoint positivity

The group-theoretic normalization is complete at the level of actual fusion
labels. The remaining norm-saturation premise is the symmetric-fusion-category
input; it is not derived in this file.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace MTC.Center.Normalization
universe v u
variable (C : BraidedFusionCategory.{v,u})

/-- Positivity on the intersection of actual transparent labels and the
adjoint fusion subring yields a pivotal structure normalized on the Müger
centre, once FP norm saturation for transparent simples is available. -/
theorem normalize_pivotal_on_muger_of_adjoint_positivity
    (p : PivotalStructure (C := C.Obj))
    (hsat : ∀ i, MTC.Center.Transparent (simples C i) →
      ‖pivotalDimension C p (simples C i)‖ = fpSimple C i)
    (hpositive : ∀ i, MTC.Center.Transparent (simples C i) → IsAdjointLabel C i →
      ∃ r : ℝ, 0 < r ∧ pivotalDimension C p (simples C i) = r) :
    ∃ q : PivotalStructure (C := C.Obj), ∀ i,
      MTC.Center.Transparent (simples C i) →
      pivotalDimension C q (simples C i) = (fpSimple C i : ℂ) :=
  normalize_pivotal_on_muger_of_norm_saturation C p hsat (fun i ht hn ↦
    hpositive i ht ((fusionDegree_zero_iff_adjointLabel C i).mp hn))

end MTC.Center.Normalization
end
