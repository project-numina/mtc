module
public import PropertyF.Ground.Target

/-!
# FP dimensions of dual simple objects

Status: solved
Source: Etingof–Nikshych–Ostrik, arXiv:math/0203060, Section 8.
Declaration: MTC.Conjectures.Fusion.dual_dimensions

Dual simple objects have the same Frobenius–Perron dimension. This symmetry is
necessary for the fusion-rule involution and is checkable on exact modular data.
The ground interface does not select a duality permutation, so this statement
uses an explicit isomorphism to the right dual. The correspondence between its
spectral radius and standard FP dimension remains a proof obligation.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace MTC.Conjectures.Fusion
open PropertyF.Ground
universe v u

/-- Dual representatives have equal FP dimensions. -/
theorem dual_dimensions (C : BraidedFusionCategory.{v,u})
    (i j : Fin (rank C))
    (h : Nonempty (simples C j ≅ (simples C i)ᘁ)) :
    fpSimple C i = fpSimple C j := by
  sorry

/-- The equality is automatic for a self-dual label. -/
example (C : BraidedFusionCategory.{v,u}) (i : Fin (rank C)) :
    fpSimple C i = fpSimple C i := rfl

end MTC.Conjectures.Fusion
