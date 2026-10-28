module
public import PropertyF.Ground.Dimensions.DimensionCharacter

/-! # A criterion for sphericality

Biproduct trace formulas reduce sphericality to the dimensions of simple objects.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open scoped BigOperators
namespace PropertyF.Ground.Dimensions
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RigidCategory C]
  [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]

/-- Left pivotal trace as a linear map on an endomorphism space. -/
def leftTraceLinear (p : PivotalStructure (C := C)) (X : C) :
    (X ⟶ X) →ₗ[ℂ] End (𝟙_ C) where
  toFun := p.leftTrace
  map_add' := p.leftTrace_add
  map_smul' := p.leftTrace_smul

/-- If diagonal blocks are scalar, the left trace is their dimension-weighted sum. -/
theorem leftTrace_biproduct_scalar_blocks {ι : Type*} [Fintype ι]
    (F : ι → C) [HasBiproduct F] (p : PivotalStructure (C := C))
    (f : (⨁ F) ⟶ (⨁ F)) (c : ι → ℂ)
    (hc : ∀ i, biproduct.ι F i ≫ f ≫ biproduct.π F i = c i • 𝟙 (F i)) :
    p.leftTrace f = ∑ i, c i • p.leftTrace (𝟙 (F i)) :=
  cyclicTrace_biproduct_scalar_blocks (leftTraceLinear p)
    (fun f g => leftTrace_cyclic p f g) F f c hc

end PropertyF.Ground.Dimensions

namespace PropertyF.Ground.Dimensions
universe v u

variable (C : BraidedFusionCategory.{v,u})
attribute [local instance] Abelian.hasFiniteBiproducts

/-- In a fusion category it suffices to compare left and right dimensions on
simple representatives to verify sphericality on all endomorphisms. -/
theorem isSpherical_iff_simple_dimensions
    (p : PivotalStructure (C := C.Obj)) :
    p.IsSpherical ↔ ∀ i : Fin (rank C),
      p.leftTrace (𝟙 (simples C i)) = p.rightTrace (𝟙 (simples C i)) := by
  constructor
  · intro h i
    exact h _ _
  · intro hs X f
    classical
    let m (i : Fin (rank C)) := Module.finrank ℂ (simples C i ⟶ X)
    let V : (Σ i, Fin (m i)) → C.Obj := fun a => simples C a.1
    obtain ⟨e⟩ := exists_canonical_decomposition C X
    let g : (⨁ V) ⟶ (⨁ V) := e.inv ≫ f ≫ e.hom
    have hleft : p.leftTrace f = p.leftTrace g := by
      simpa [g, Category.assoc] using (leftTrace_cyclic p e.hom (e.inv ≫ f))
    have hright : p.rightTrace f = p.rightTrace g := by
      simpa [g, Category.assoc] using (p.rightTrace_cyclic e.hom (e.inv ≫ f))
    have hsimple : ∀ a, Simple (V a) := fun a => simples_simple C a.1
    have hfinite : ∀ a, FiniteDimensional ℂ (V a ⟶ V a) := fun a =>
      IsFusionCategory.hom_finite _ _
    obtain ⟨c, hc, htrace⟩ := rightTrace_biproduct_simple V hsimple hfinite p g
    rw [hleft, hright, htrace, leftTrace_biproduct_scalar_blocks V p g c hc]
    apply Finset.sum_congr rfl
    intro a _
    rw [hs a.1]

end PropertyF.Ground.Dimensions
