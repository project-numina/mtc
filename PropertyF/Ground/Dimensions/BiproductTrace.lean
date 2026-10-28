module
public import PropertyF.Ground.Dimensions.Trace
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Mathlib.CategoryTheory.Preadditive.Schur
public import Mathlib.Analysis.Complex.Polynomial.Basic

/-! # Traces of biproducts

Pivotal traces decompose over finite biproducts and their scalar blocks.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open scoped BigOperators
namespace PropertyF.Ground.Dimensions
universe v u
section CyclicTrace
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
variable {A : Type*} [AddCommMonoid A] [Module ℂ A]

/-- A family of linear maps on endomorphisms is cyclic under composition. -/
abbrev IsCyclicTrace (trace : ∀ X : C, (X ⟶ X) →ₗ[ℂ] A) : Prop :=
  ∀ {X Y : C} (f : X ⟶ Y) (g : Y ⟶ X), trace X (f ≫ g) = trace Y (g ≫ f)

/-- A cyclic linear trace decomposes over maps whose composites sum to the identity. -/
theorem cyclicTrace_decomposition {ι : Type*} [Fintype ι]
    (trace : ∀ X : C, (X ⟶ X) →ₗ[ℂ] A)
    (hcyclic : IsCyclicTrace trace)
    {X : C} {Y : ι → C} (i : ∀ j, Y j ⟶ X) (q : ∀ j, X ⟶ Y j)
    (h : ∑ j, q j ≫ i j = 𝟙 X) (f : X ⟶ X) :
    trace X f = ∑ j, trace (Y j) (i j ≫ f ≫ q j) := by
  classical
  calc
    _ = trace X ((∑ j, q j ≫ i j) ≫ f) := by rw [h, Category.id_comp]
    _ = ∑ j, trace X ((q j ≫ i j) ≫ f) := by
      rw [Preadditive.sum_comp]
      exact map_sum (trace X) _ _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j _
      simpa only [Category.assoc] using hcyclic (q j) (i j ≫ f)

/-- Each diagonal block on a biproduct of simple objects is a scalar. -/
theorem simple_biproduct_diagonal [HasKernels C] {ι : Type*}
    {F : ι → C} [HasBiproduct F] (hs : ∀ i, Simple (F i))
    (hfinite : ∀ i, FiniteDimensional ℂ (F i ⟶ F i)) (f : (⨁ F) ⟶ (⨁ F)) :
    ∃ c : ι → ℂ, ∀ i, biproduct.ι F i ≫ f ≫ biproduct.π F i = c i • 𝟙 (F i) := by
  classical
  have h : ∀ i, ∃ c : ℂ, biproduct.ι F i ≫ f ≫ biproduct.π F i = c • 𝟙 (F i) := by
    intro i
    let : Simple (F i) := hs i
    let : FiniteDimensional ℂ (F i ⟶ F i) := hfinite i
    obtain ⟨c, hc⟩ := endomorphism_simple_eq_smul_id ℂ (biproduct.ι F i ≫ f ≫ biproduct.π F i)
    exact ⟨c, hc.symm⟩
  exact Classical.skolem.mp h
/-- Scalar diagonal blocks give the corresponding weighted cyclic trace. -/
theorem cyclicTrace_biproduct_scalar_blocks {ι : Type*} [Fintype ι]
    (trace : ∀ X : C, (X ⟶ X) →ₗ[ℂ] A)
    (hcyclic : IsCyclicTrace trace)
    {F : ι → C} [HasBiproduct F] (f : (⨁ F) ⟶ (⨁ F)) {c : ι → ℂ}
    (hc : ∀ i, biproduct.ι F i ≫ f ≫ biproduct.π F i = c i • 𝟙 (F i)) :
    trace (⨁ F) f = ∑ i, c i • trace (F i) (𝟙 (F i)) := by
  rw [cyclicTrace_decomposition trace hcyclic (biproduct.ι F) (biproduct.π F) biproduct.total f]
  simp_rw [hc, map_smul]

/-- A cyclic trace on a biproduct of simples is a weighted sum of simple traces. -/
theorem cyclicTrace_biproduct_simple [HasKernels C] {ι : Type*} [Fintype ι]
    (trace : ∀ X : C, (X ⟶ X) →ₗ[ℂ] A)
    (hcyclic : IsCyclicTrace trace)
    {F : ι → C} [HasBiproduct F] (hs : ∀ i, Simple (F i))
    (hfinite : ∀ i, FiniteDimensional ℂ (F i ⟶ F i)) (f : (⨁ F) ⟶ (⨁ F)) :
    ∃ c : ι → ℂ,
      (∀ i, biproduct.ι F i ≫ f ≫ biproduct.π F i = c i • 𝟙 (F i)) ∧
      trace (⨁ F) f = ∑ i, c i • trace (F i) (𝟙 (F i)) :=
  (simple_biproduct_diagonal hs hfinite f).imp fun _c hc ↦
    ⟨hc, cyclicTrace_biproduct_scalar_blocks trace hcyclic f hc⟩

end CyclicTrace

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
    {X : C} {Y : ι → C} (i : ∀ j, Y j ⟶ X) (q : ∀ j, X ⟶ Y j)
    (h : ∑ j, q j ≫ i j = 𝟙 X) (f : X ⟶ X) :
    p.rightTrace f = ∑ j, p.rightTrace (i j ≫ f ≫ q j) :=
  cyclicTrace_decomposition (rightTraceLinear p) (fun f g => p.rightTrace_cyclic f g) i q h f

/-- The trace on a finite direct sum is the sum of traces of diagonal blocks. -/
theorem rightTrace_biproduct {ι : Type*} [Fintype ι] (F : ι → C) [HasBiproduct F]
    (p : PivotalStructure (C := C)) (f : (⨁ F) ⟶ (⨁ F)) :
    p.rightTrace f = ∑ i, p.rightTrace (biproduct.ι F i ≫ f ≫ biproduct.π F i) :=
  rightTrace_decomposition p (biproduct.ι F) (biproduct.π F) biproduct.total f

/-- Categorical dimensions are additive on finite direct sums. -/
theorem rightDimension_biproduct {ι : Type*} [Fintype ι] (F : ι → C) [HasBiproduct F]
    (p : PivotalStructure (C := C)) :
    p.rightTrace (𝟙 (⨁ F)) = ∑ i, p.rightTrace (𝟙 (F i)) := by
  rw [rightTrace_biproduct F p]
  simp

/-- Schur's lemma gives the scalar diagonal blocks of any endomorphism of a
finite direct sum of simple objects, and hence its weighted trace formula. -/
theorem rightTrace_biproduct_simple [HasKernels C] {ι : Type*} [Fintype ι]
    {F : ι → C} [HasBiproduct F] (hs : ∀ i, Simple (F i))
    (hfinite : ∀ i, FiniteDimensional ℂ (F i ⟶ F i))
    (p : PivotalStructure (C := C)) (f : (⨁ F) ⟶ (⨁ F)) :
    ∃ c : ι → ℂ,
      (∀ i, biproduct.ι F i ≫ f ≫ biproduct.π F i = c i • 𝟙 (F i)) ∧
      p.rightTrace f = ∑ i, c i • p.rightTrace (𝟙 (F i)) :=
  cyclicTrace_biproduct_simple (rightTraceLinear p) (fun f g => p.rightTrace_cyclic f g)
    hs hfinite f

end PropertyF.Ground.Dimensions
