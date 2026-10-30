module
public import MTC.Fusion.Equivalence
public import MTC.Modular.SMatrix
public import Mathlib.Computability.Partrec

open MTC.PropertyF.Reduction

open MTC.Fusion

open MTC.Braided

/-!
# Effective counting of braided equivalence classes

Status: open
Source: Bruillard–Ng–Rowell–Wang, arXiv:1310.7050, Question 4.4 and Remark 4.2.
Declaration: MTC.Conjectures.RankFiniteness.effectiveCategoryCount

Ask for a computable upper bound in terms of rank for the number of braided
monoidal equivalence classes underlying modular categories. The explicit
finite cover makes both the objects and the counting convention clear. Since
pivotal or ribbon structures are not preserved by this equivalence, this is
weaker than a corresponding effective count of modular categories up to
ribbon equivalence. The paper asks for better asymptotic bounds and notes that
counting modular categories effectively is not supplied by its algorithm.
Its rank-finiteness theorem gives existence of a finite cover at each rank but
does not by itself provide the computable function required here.

The hypothesis uses a spherical pivotal structure and nondegenerate
categorical S; the equivalence with standard categorical modularity and a
Lean rank-one category example remain future work.
-/

@[expose] public noncomputable section
open MTC MTC.PropertyF MTC.Modular

namespace MTC.Conjectures.RankFiniteness
universe v u

/-- A computable bound for finite covers by braided tensor equivalence. -/
theorem effectiveCategoryCount :
    ∃ f : ℕ → ℕ, Computable f ∧ ∀ r : ℕ,
      ∃ (n : ℕ) (reps : Fin n → BraidedFusionCategory.{v,u}),
        n ≤ f r ∧
        (∀ i, rank (reps i) = r ∧ HasNondegenerateSphericalStructure (reps i)) ∧
        ∀ C : BraidedFusionCategory.{v,u}, rank C = r →
          HasNondegenerateSphericalStructure C →
          ∃ i, Nonempty (MTC.Fusion.BraidedTensorEquivalence C (reps i)) := by
  sorry

end MTC.Conjectures.RankFiniteness
