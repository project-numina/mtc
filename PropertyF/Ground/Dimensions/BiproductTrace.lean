module
public import PropertyF.Ground.Dimensions.Trace
public import Mathlib.CategoryTheory.Preadditive.Biproducts

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open scoped BigOperators
namespace PropertyF.Ground.Dimensions
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
  [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]

/-- Right pivotal trace as a linear map on an endomorphism space. -/
def rightTraceLinear (p : PivotalStructure (C := C)) (X : C) :
    (X ⟶ X) →ₗ[ℂ] End (𝟙_ C) where
  toFun := p.rightTrace
  map_add' := p.rightTrace_add
  map_smul' := p.rightTrace_smul

/-- The trace on a finite direct sum is the sum of traces of diagonal blocks. -/
theorem rightTrace_biproduct {ι : Type*} [Fintype ι] (F : ι → C) [HasBiproduct F]
    (p : PivotalStructure (C := C)) (f : (⨁ F) ⟶ (⨁ F)) :
    p.rightTrace f = ∑ i, p.rightTrace (biproduct.ι F i ≫ f ≫ biproduct.π F i) := by
  classical
  calc
    _ = p.rightTrace ((∑ i, biproduct.π F i ≫ biproduct.ι F i) ≫ f) := by rw [biproduct.total]; simp
    _ = ∑ i, p.rightTrace ((biproduct.π F i ≫ biproduct.ι F i) ≫ f) := by
      rw [Preadditive.sum_comp]
      exact map_sum (rightTraceLinear p _) _ _
    _ = ∑ i, p.rightTrace (biproduct.ι F i ≫ f ≫ biproduct.π F i) := by
      apply Finset.sum_congr rfl
      intro i _
      simp only [Category.assoc]
      simpa only [Category.assoc] using p.rightTrace_cyclic (biproduct.π F i) (biproduct.ι F i ≫ f)

/-- Categorical dimensions are additive on finite direct sums. -/
theorem rightDimension_biproduct {ι : Type*} [Fintype ι] (F : ι → C) [HasBiproduct F]
    (p : PivotalStructure (C := C)) :
    p.rightTrace (𝟙 (⨁ F)) = ∑ i, p.rightTrace (𝟙 (F i)) := by
  rw [rightTrace_biproduct F p]
  simp

end PropertyF.Ground.Dimensions
