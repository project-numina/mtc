module
public import MTC.PropertyF.NondegenerateSpherical
public import Mathlib.Computability.Partrec

/-!
# Effective bounds for Frobenius–Perron dimension

Status: open
Source: Bruillard–Ng–Rowell–Wang, arXiv:1310.7050, Question 4.6.
Declaration: MTC.Conjectures.RankFiniteness.effectiveDimension

The question asks for an explicit upper bound on global FP dimension depending
only on rank. Here effectiveness is expressed as the existence of a computable
natural-valued bound. The hypothesis is a spherical pivotal structure with
nondegenerate categorical S-matrix on the frozen braided fusion category.
This is the usual nondegeneracy criterion for modularity, but the construction
of its associated ribbon structure and a categorical equivalence interface
are not supplied by this file. The rank and FP dimension are the existing
chosen definitions; the remaining identification obligations for these
frozen definitions must be discharged before transferring a literature result.

Rank-finiteness gives an abstract bound, but does not by itself exhibit a
computable one. The trivial category is a mathematical example; a Lean
construction satisfying the categorical hypotheses remains to be supplied.
-/

@[expose] public noncomputable section
open PropertyF.Ground MTC.PropertyF

namespace MTC.Conjectures.RankFiniteness
universe v u

/-- There is a computable rank-dependent bound on global FP dimension for
spherical braided fusion categories with nondegenerate categorical S. -/
theorem effectiveDimension :
    ∃ f : ℕ → ℕ, Computable f ∧
      ∀ C : BraidedFusionCategory.{v,u},
        HasNondegenerateSphericalStructure C →
        globalFPDimension C ≤ (f (rank C) : ℝ) := by
  sorry

end MTC.Conjectures.RankFiniteness
