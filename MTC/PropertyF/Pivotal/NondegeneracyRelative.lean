module
public import MTC.PropertyF.Pivotal.NondegeneracyHaarSlide
public import MTC.Center.Normalization.FusionSubringSupport

open MTC.Fusion MTC.Modular MTC.Center.Braid MTC.Center.Normalization
open MTC.CategoryTheory.Dimensions
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace MTC.PropertyF.Pivotal
universe v u
variable (C : BraidedFusionCategory.{v,u}) (p : PivotalStructure (C := C.Obj))

/-- Numerical S-centrality with a fusion subring implies actual monodromy
centrality with any object whose simple constituents belong to the subring. -/
theorem relative_fusionSubring_numerical_centrality_supported
    (A : Finset (Fin (rank C))) (hA : IsFusionSubring C A)
    (y : Fin (rank C)) (hs : ∀ a ∈ A, sCentralizes C p a y)
    (U : C.Obj) (hU : ∀ a, 0 < simpleMultiplicity C a U → a ∈ A) :
    doubleBraiding U (simples C y) = 𝟙 _ := by
  apply doubleBraiding_eq_id_of_restricted_sTest C p A
    ⟨unitIndex C, hA.unit⟩ U y
  · intro i hi
    exact hs (dualIndex C i) (hA.dual i hi)
  · intro j hj i hi
    exact fusionSubring_forward_finrank_zero_of_supported C A hA j hj U hU i hi
  · intro i hi j hj
    exact fusionSubring_dualLabel_finrank_zero_of_supported C A hA U hU i hi j hj

/-- Numerical S-centrality with a fusion subring implies actual monodromy
centrality with every simple object in that subring, for an arbitrary pivotal
structure. -/
theorem relative_fusionSubring_numerical_centrality
    (A : Finset (Fin (rank C))) (hA : IsFusionSubring C A)
    (y : Fin (rank C)) (hs : ∀ a ∈ A, sCentralizes C p a y)
    (a : Fin (rank C)) (ha : a ∈ A) :
    doubleBraiding (simples C a) (simples C y) = 𝟙 _ := by
  apply relative_fusionSubring_numerical_centrality_supported C p A hA y hs (simples C a)
  intro i hi
  have : i = a := by
    by_contra hne
    simp [simpleMultiplicity, finrank_simples_hom, hne] at hi
  simpa [this] using ha

end MTC.PropertyF.Pivotal
end
