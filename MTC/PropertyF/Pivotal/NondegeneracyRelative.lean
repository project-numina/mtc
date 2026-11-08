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
centrality with every simple object in that subring, for an arbitrary pivotal
structure. -/
theorem relative_fusionSubring_numerical_centrality
    (A : Finset (Fin (rank C))) (hA : IsFusionSubring C A)
    (y : Fin (rank C)) (hs : ∀ a ∈ A, sCentralizes C p a y)
    (a : Fin (rank C)) (ha : a ∈ A) :
    doubleBraiding (simples C a) (simples C y) = 𝟙 _ := by
  apply doubleBraiding_eq_id_of_restricted_sTest C p A
    ⟨unitIndex C, hA.unit⟩ (simples C a) y
  · intro i hi
    exact hs (dualIndex C i) (hA.dual i hi)
  · intro j hj i hi
    exact fusionSubring_forward_finrank_zero C A hA j a hj ha i hi
  · intro i hi j hj
    exact fusionSubring_dualLabel_finrank_zero C A hA a i ha hi j hj

end MTC.PropertyF.Pivotal
end
