module
public import PropertyF.Ground.Target

/-!
# Realization of pointed fusion rules

Every finite abelian group occurs as the group of simple objects of a braided
complex fusion category, with tensor product given by the group law. A model
is the category of finite-dimensional group-graded complex vector spaces,
with trivial associator and the flip braiding. This is a first category-level
entry point for realizing pointed F/R data; the theorem does not yet assert
that an arbitrary supplied cocycle is represented by the constructed category.

Status: solved
Source: Etingof, Gelaki, Nikshych and Ostrik, Tensor Categories, Sections 2.6 and 8.4, https://math.mit.edu/~etingof/egnobookfinal.pdf.
Declaration: MTC.Conjectures.Realizability.pointedFusionRules

The categorical proof is not formalized here. The simple labels chosen by the
frozen target are identified with the group by an equivalence, and the
fusion multiplicity convention is exactly `PropertyF.Ground.fusionMatrix`.
-/

@[expose] public noncomputable section
namespace MTC.Conjectures.Realizability

open PropertyF.Ground

/-- Finite abelian groups are the fusion rings of pointed braided fusion categories. -/
theorem pointedFusionRules (G : Type) [Fintype G] [DecidableEq G] [AddCommGroup G] :
    ∃ C : BraidedFusionCategory.{0, 0}, ∃ e : Fin (rank C) ≃ G,
      ∀ i j k : Fin (rank C),
        fusionMatrix C i k j = if e i + e j = e k then 1 else 0 := by
  sorry

/-- Any such identification forces the categorical rank to be positive. -/
theorem pointed_rank_pos {G : Type} [AddCommGroup G] (C : BraidedFusionCategory.{0, 0})
    (e : Fin (rank C) ≃ G) : 0 < rank C := by
  exact Fin.pos_iff_nonempty.mpr ⟨e.symm 0⟩

end MTC.Conjectures.Realizability
