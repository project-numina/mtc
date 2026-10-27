module
public import PropertyF.Ground.Dimensions.Trace
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Mathlib.CategoryTheory.Preadditive.Schur
public import Mathlib.Analysis.Complex.Polynomial.Basic

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

/-- The right trace decomposes across a finite family of maps summing to the identity. -/
theorem rightTrace_decomposition {ι : Type*} [Fintype ι] (p : PivotalStructure (C := C))
    (X : C) (Y : ι → C) (i : ∀ j, Y j ⟶ X) (q : ∀ j, X ⟶ Y j)
    (h : ∑ j, q j ≫ i j = 𝟙 X) (f : X ⟶ X) :
    p.rightTrace f = ∑ j, p.rightTrace (i j ≫ f ≫ q j) := by
  calc
    _ = p.rightTrace ((∑ j, q j ≫ i j) ≫ f) := by rw [h, Category.id_comp]
    _ = ∑ j, p.rightTrace ((q j ≫ i j) ≫ f) := by
      rw [Preadditive.sum_comp]
      exact map_sum (rightTraceLinear p _) _ _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j _
      simpa only [Category.assoc] using p.rightTrace_cyclic (q j) (i j ≫ f)

/-- The trace on a finite direct sum is the sum of traces of diagonal blocks. -/
theorem rightTrace_biproduct {ι : Type*} [Fintype ι] (F : ι → C) [HasBiproduct F]
    (p : PivotalStructure (C := C)) (f : (⨁ F) ⟶ (⨁ F)) :
    p.rightTrace f = ∑ i, p.rightTrace (biproduct.ι F i ≫ f ≫ biproduct.π F i) :=
  rightTrace_decomposition p _ F (biproduct.ι F) (biproduct.π F) biproduct.total f

/-- Categorical dimensions are additive on finite direct sums. -/
theorem rightDimension_biproduct {ι : Type*} [Fintype ι] (F : ι → C) [HasBiproduct F]
    (p : PivotalStructure (C := C)) :
    p.rightTrace (𝟙 (⨁ F)) = ∑ i, p.rightTrace (𝟙 (F i)) := by
  rw [rightTrace_biproduct F p]
  simp

/-- If diagonal blocks are scalar, trace is their dimension-weighted sum. -/
theorem rightTrace_biproduct_scalar_blocks {ι : Type*} [Fintype ι]
    (F : ι → C) [HasBiproduct F] (p : PivotalStructure (C := C))
    (f : (⨁ F) ⟶ (⨁ F)) (c : ι → ℂ)
    (hc : ∀ i, biproduct.ι F i ≫ f ≫ biproduct.π F i = c i • 𝟙 (F i)) :
    p.rightTrace f = ∑ i, c i • p.rightTrace (𝟙 (F i)) := by
  rw [rightTrace_biproduct F p]
  apply Finset.sum_congr rfl
  intro i _
  rw [hc i, p.rightTrace_smul]

/-- Schur's lemma gives the scalar diagonal blocks of any endomorphism of a
finite direct sum of simple objects, and hence its weighted trace formula. -/
theorem rightTrace_biproduct_simple [HasKernels C] {ι : Type*} [Fintype ι]
    (F : ι → C) [HasBiproduct F] (hs : ∀ i, Simple (F i))
    (hfinite : ∀ i, FiniteDimensional ℂ (F i ⟶ F i))
    (p : PivotalStructure (C := C)) (f : (⨁ F) ⟶ (⨁ F)) :
    ∃ c : ι → ℂ,
      (∀ i, biproduct.ι F i ≫ f ≫ biproduct.π F i = c i • 𝟙 (F i)) ∧
      p.rightTrace f = ∑ i, c i • p.rightTrace (𝟙 (F i)) := by
  classical
  have h : ∀ i, ∃ c : ℂ, biproduct.ι F i ≫ f ≫ biproduct.π F i = c • 𝟙 (F i) := by
    intro i
    let : Simple (F i) := hs i
    let : FiniteDimensional ℂ (F i ⟶ F i) := hfinite i
    obtain ⟨c, hc⟩ := endomorphism_simple_eq_smul_id ℂ (biproduct.ι F i ≫ f ≫ biproduct.π F i)
    exact ⟨c, hc.symm⟩
  choose c hc using h
  exact ⟨c, hc, rightTrace_biproduct_scalar_blocks F p f c hc⟩

end PropertyF.Ground.Dimensions
