module
public import MTC.PropertyF.NondegenerateSpherical

/-!
# Rank-finiteness for global FP-dimension values

Status: solved
Source: Bruillard–Ng–Rowell–Wang, arXiv:1310.7050, Theorem 3.1 and Corollary 3.13.
Declaration: MTC.Conjectures.RankFiniteness.dimensionValuesFinite

At fixed rank, the possible global FP dimensions of modular categories form a
finite set. This is a numerical consequence of rank-finiteness, not the full
statement that the categories themselves are finite up to equivalence. The
hypothesis uses a spherical pivotal structure and nondegenerate categorical S.
A formal category-level equivalence relation, the construction of the ribbon
structure, and invariance and identification of the frozen `rank` and
`globalFPDimension` remain to be proved before the literature proof can be
transported to this exact statement. In particular, this file makes no claim
that numerical data classify categories.

The rank-one trivial category is a mathematical instance, but a Lean instance
satisfying these categorical hypotheses is not constructed here. This result
implies an abstract upper bound, whereas an explicit computable bound is the
separate open effective-dimension question.
-/

@[expose] public noncomputable section
open PropertyF.Ground MTC.PropertyF

namespace MTC.Conjectures.RankFiniteness
universe v u

/-- Fixed rank admits only finitely many global FP-dimension values. -/
theorem dimensionValuesFinite (r : ℕ) :
    {d : ℝ | ∃ C : BraidedFusionCategory.{v,u}, rank C = r ∧
      HasNondegenerateSphericalStructure C ∧
      globalFPDimension C = d}.Finite := by
  sorry

end MTC.Conjectures.RankFiniteness
