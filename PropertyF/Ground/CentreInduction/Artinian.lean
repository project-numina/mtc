module
public import PropertyF.Ground.CentreInduction.Splitting
public import PropertyF.Ground.Centre.Abelian
public import Mathlib.CategoryTheory.Subobject.ArtinianObject
public import Mathlib.CategoryTheory.Subobject.NoetherianObject
public import Mathlib.RingTheory.Artinian.Module
public import Mathlib.CategoryTheory.Abelian.Exact

/-! Finite Hom spaces and split monomorphisms force Artinian objects. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace PropertyF.Ground.CentreInduction
universe v u
variable {D : Type u} [Category.{v} D] [Preadditive D] [Linear ℂ D]

/-- Associate to a subobject the subspace of endomorphisms factoring through
its embedding. -/
def subobjectEndRange (X : D) (P : Subobject X) : Submodule ℂ (X ⟶ X) :=
  LinearMap.range (Linear.rightComp ℂ X P.arrow)

/-- If all subobjects of X split, their factoring subspaces detect the
subobject order. -/
def subobjectEndRangeEmbedding (X : D)
    (hsplit : ∀ (P : Subobject X), IsSplitMono P.arrow) :
    Subobject X ↪o Submodule ℂ (X ⟶ X) :=
  OrderEmbedding.ofMapLEIff (subobjectEndRange X) (by
    intro P Q
    constructor
    · intro h
      letI : IsSplitMono P.arrow := hsplit P
      have hm : retraction P.arrow ≫ P.arrow ∈ subobjectEndRange X P :=
        ⟨retraction P.arrow, rfl⟩
      obtain ⟨g, hg⟩ := h hm
      change g ≫ Q.arrow = retraction P.arrow ≫ P.arrow at hg
      apply Subobject.le_of_comm (P.arrow ≫ g)
      rw [Category.assoc, hg, ← Category.assoc, IsSplitMono.id, Category.id_comp]
    · intro h x hx
      obtain ⟨g, rfl⟩ := hx
      refine ⟨g ≫ Subobject.ofLE P Q h, ?_⟩
      change (g ≫ Subobject.ofLE P Q h) ≫ Q.arrow = g ≫ P.arrow
      rw [Category.assoc, Subobject.ofLE_arrow])

/-- In a Hom-finite linear category, an object whose subobjects all split
has no infinite descending chain of subobjects. -/
theorem artinian_of_split_subobjects (X : D) [FiniteDimensional ℂ (X ⟶ X)]
    (hsplit : ∀ (P : Subobject X), IsSplitMono P.arrow) : IsArtinianObject X := by
  exact ⟨(subobjectEndRangeEmbedding X hsplit).wellFoundedLT⟩

/-- The same order embedding also gives the ascending chain condition. -/
theorem noetherian_of_split_subobjects (X : D) [FiniteDimensional ℂ (X ⟶ X)]
    (hsplit : ∀ (P : Subobject X), IsSplitMono P.arrow) : IsNoetherianObject X := by
  exact ⟨(subobjectEndRangeEmbedding X hsplit).wellFoundedGT⟩

/-- Under the stated loop-sliding identity, every object of the actual centre
is Artinian. -/
theorem center_artinian_of_loop_centrality (C : BraidedFusionCategory.{v,u})
    (p : Dimensions.PivotalStructure (C := C.Obj)) (hp : p.IsSpherical)
    (hslide : SimpleLoopCentrality C p) (hne : globalDimension C ≠ 0)
    (X : CategoryTheory.Center C.Obj) : IsArtinianObject X := by
  letI : FiniteDimensional ℂ (X.1 ⟶ X.1) := IsFusionCategory.hom_finite _ _
  letI : FiniteDimensional ℂ (X ⟶ X) := Centre.finiteDimensional_hom ℂ X X
  apply artinian_of_split_subobjects X
  intro P
  exact mono_splits_of_loop_centrality C p hp hslide hne P.arrow

/-- Under the same hypotheses every nonzero centre object has a simple
retract. This is one step toward its finite semisimple decomposition. -/
theorem exists_simple_retract_of_loop_centrality (C : BraidedFusionCategory.{v,u})
    (p : Dimensions.PivotalStructure (C := C.Obj)) (hp : p.IsSpherical)
    (hslide : SimpleLoopCentrality C p) (hne : globalDimension C ≠ 0)
    (X : CategoryTheory.Center C.Obj) (hX : ¬ IsZero X) :
    ∃ S : CategoryTheory.Center C.Obj, Simple S ∧ Nonempty (Retract S X) := by
  letI : IsArtinianObject X := center_artinian_of_loop_centrality C p hp hslide hne X
  obtain ⟨P, hP⟩ := exists_simple_subobject hX
  letI : IsSplitMono P.arrow := mono_splits_of_loop_centrality C p hp hslide hne P.arrow
  exact ⟨P, hP, ⟨{ i := P.arrow, r := retraction P.arrow }⟩⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Every nonzero centre object splits as the direct sum of a simple object
and a complement, assuming the loop-sliding identity. -/
theorem exists_simple_biprod_of_loop_centrality (C : BraidedFusionCategory.{v,u})
    (p : Dimensions.PivotalStructure (C := C.Obj)) (hp : p.IsSpherical)
    (hslide : SimpleLoopCentrality C p) (hne : globalDimension C ≠ 0)
    (X : CategoryTheory.Center C.Obj) (hX : ¬ IsZero X) :
    ∃ S K : CategoryTheory.Center C.Obj, Simple S ∧ Nonempty (X ≅ S ⊞ K) := by
  letI : IsArtinianObject X := center_artinian_of_loop_centrality C p hp hslide hne X
  obtain ⟨P, hP⟩ := exists_simple_subobject hX
  letI : IsSplitMono P.arrow := mono_splits_of_loop_centrality C p hp hslide hne P.arrow
  let E := ShortComplex.cokernelSequence P.arrow
  let split : E.Splitting := ShortComplex.Splitting.ofExactOfRetraction E
    (ShortComplex.cokernelSequence_exact P.arrow) (retraction P.arrow)
    (IsSplitMono.id P.arrow) inferInstance
  exact ⟨P, cokernel P.arrow, hP, ⟨split.isoBinaryBiproduct⟩⟩

end PropertyF.Ground.CentreInduction
