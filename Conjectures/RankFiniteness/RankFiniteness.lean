module
public import MTC.ModularData.Equivalence
public import PropertyF.Ground.Modular.SMatrix

/-!
# Rank-finiteness for modular categories

Status: solved
Source: Bruillard–Ng–Rowell–Wang, arXiv:1310.7050, Theorem 3.1.
Declaration: MTC.Conjectures.RankFiniteness.rankFiniteness

For each rank, finitely many representatives cover the spherical braided
fusion categories with nondegenerate categorical S, up to complex-linear
braided monoidal equivalence. This is a weaker equivalence than equivalence of
modular categories with specified ribbon structures: the representatives and
the equivalences here do not retain a chosen pivotal or ribbon structure.
The literature theorem implies the intended formulation once the present
pivotal and nondegeneracy conditions are connected to the standard ribbon
notion, and invariance and identification of the frozen chosen `rank` are
proved. These connections have not been formalized in this file.

Mathematically the trivial category satisfies the hypotheses at rank one;
the project does not yet provide a Lean construction of that category. The
finite cover formulation avoids an unproved setoid or an assumption that S and
T determine the category. It does not provide an effective bound on its size.
-/

@[expose] public noncomputable section
open PropertyF.Ground PropertyF.Ground.Dimensions PropertyF.Ground.Modular

namespace MTC.Conjectures.RankFiniteness
universe v u

/-- There are finitely many braided tensor equivalence classes at each rank. -/
theorem rankFiniteness (r : ℕ) :
    ∃ (n : ℕ) (reps : Fin n → BraidedFusionCategory.{v,u}),
      (∀ i, rank (reps i) = r ∧
        ∃ p : PivotalStructure (C := (reps i).Obj),
          p.IsSpherical ∧ (categoricalS (reps i) p).det ≠ 0) ∧
      ∀ C : BraidedFusionCategory.{v,u}, rank C = r →
        (∃ p : PivotalStructure (C := C.Obj),
          p.IsSpherical ∧ (categoricalS C p).det ≠ 0) →
        ∃ i, Nonempty (MTC.BraidedTensorEquivalence C (reps i)) := by
  sorry

end MTC.Conjectures.RankFiniteness
