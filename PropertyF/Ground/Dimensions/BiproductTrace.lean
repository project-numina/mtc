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
variable {k : Type*} [CommSemiring k] {C : Type u} [Category.{v} C] [Preadditive C] [Linear k C]
variable {A : Type*} [AddCommMonoid A] [Module k A]
variable {ι : Type*} [Fintype ι]

/-- An endomorphism of a biproduct has the given scalars on its diagonal blocks. -/
abbrev HasScalarDiagonal (F : ι → C) [HasBiproduct F]
    (f : (⨁ F) ⟶ (⨁ F)) (c : ι → k) : Prop :=
  ∀ i, biproduct.ι F i ≫ f ≫ biproduct.π F i = c i • 𝟙 (F i)

/-- A family of linear maps on endomorphisms is cyclic under composition. -/
abbrev IsCyclicTrace (trace : ∀ X : C, (X ⟶ X) →ₗ[k] A) : Prop :=
  ∀ {X Y : C} (f : X ⟶ Y) (g : Y ⟶ X), trace X (f ≫ g) = trace Y (g ≫ f)

variable (trace : ∀ X : C, (X ⟶ X) →ₗ[k] A) (hcyclic : IsCyclicTrace trace)
include hcyclic

/-- A cyclic linear trace decomposes over maps whose composites sum to the identity. -/
theorem cyclicTrace_decomposition
    {X : C} {Y : ι → C} (i : ∀ j, Y j ⟶ X) (q : ∀ j, X ⟶ Y j)
    (h : ∑ j, q j ≫ i j = 𝟙 X) (f : X ⟶ X) :
    trace X f = ∑ j, trace (Y j) (i j ≫ f ≫ q j) := by
  conv_lhs => rw [← Category.id_comp f, ← h, Preadditive.sum_comp, map_sum]
  exact Finset.sum_congr rfl fun j _ ↦ by
    simpa only [Category.assoc] using hcyclic (q j) (i j ≫ f)

/-- Scalar diagonal blocks give the corresponding weighted cyclic trace. -/
theorem cyclicTrace_biproduct_scalar_blocks
    {F : ι → C} [HasBiproduct F] (f : (⨁ F) ⟶ (⨁ F)) {c : ι → k}
    (hc : HasScalarDiagonal F f c) :
    trace (⨁ F) f = ∑ i, c i • trace (F i) (𝟙 (F i)) :=
  by simpa only [hc, map_smul] using
    cyclicTrace_decomposition trace hcyclic (biproduct.ι F) (biproduct.π F) biproduct.total f

end CyclicTrace

section SimpleTrace
variable {k : Type*} [Field k] [IsAlgClosed k]
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear k C]
variable {A : Type*} [AddCommMonoid A] [Module k A]
variable {ι : Type*} [Fintype ι]

omit [Fintype ι] in
/-- Each diagonal block on a biproduct of simple objects is a scalar. -/
theorem simple_biproduct_diagonal [HasKernels C]
    {F : ι → C} [HasBiproduct F] (hs : ∀ i, Simple (F i))
    (hfinite : ∀ i, FiniteDimensional k (F i ⟶ F i)) (f : (⨁ F) ⟶ (⨁ F)) :
    ∃ c : ι → k, HasScalarDiagonal F f c :=
  Classical.skolem.mp fun i ↦
    let : Simple (F i) := hs i
    let : FiniteDimensional k (F i ⟶ F i) := hfinite i
    (endomorphism_simple_eq_smul_id k (biproduct.ι F i ≫ f ≫ biproduct.π F i)).imp fun _ ↦ Eq.symm
/-- A cyclic trace on a biproduct of simples is a weighted sum of simple traces. -/
theorem cyclicTrace_biproduct_simple [HasKernels C]
    (trace : ∀ X : C, (X ⟶ X) →ₗ[k] A)
    (hcyclic : IsCyclicTrace trace)
    {F : ι → C} [HasBiproduct F] (hs : ∀ i, Simple (F i))
    (hfinite : ∀ i, FiniteDimensional k (F i ⟶ F i)) (f : (⨁ F) ⟶ (⨁ F)) :
    ∃ c : ι → k, HasScalarDiagonal F f c ∧
      trace (⨁ F) f = ∑ i, c i • trace (F i) (𝟙 (F i)) :=
  (simple_biproduct_diagonal hs hfinite f).imp fun _c hc ↦
    ⟨hc, cyclicTrace_biproduct_scalar_blocks trace hcyclic f hc⟩

end SimpleTrace

section
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
  [Preadditive C] [MonoidalPreadditive C]
variable {ι : Type*} [Fintype ι]

local instance : MonoidalLinear ℤ C where
  whiskerLeft_smul := by
    intro X Y Z r f
    exact (tensorLeft X).map_zsmul
  smul_whiskerRight := by
    intro r Y Z f X
    exact (tensorRight X).map_zsmul

/-- The right trace decomposes across a finite family of maps summing to the identity. -/
theorem rightTrace_decomposition (p : PivotalStructure (C := C))
    {X : C} {Y : ι → C} (i : ∀ j, Y j ⟶ X) (q : ∀ j, X ⟶ Y j)
    (h : ∑ j, q j ≫ i j = 𝟙 X) (f : X ⟶ X) :
    p.rightTrace f = ∑ j, p.rightTrace (i j ≫ f ≫ q j) :=
  cyclicTrace_decomposition (fun X ↦ rightTraceWithLinear (k := ℤ) (p.iso X))
    (fun f g ↦ p.rightTrace_cyclic f g) i q h f

/-- The trace on a finite direct sum is the sum of traces of diagonal blocks. -/
theorem rightTrace_biproduct (F : ι → C) [HasBiproduct F]
    (p : PivotalStructure (C := C)) (f : (⨁ F) ⟶ (⨁ F)) :
    p.rightTrace f = ∑ i, p.rightTrace (biproduct.ι F i ≫ f ≫ biproduct.π F i) :=
  rightTrace_decomposition p (biproduct.ι F) (biproduct.π F) biproduct.total f

variable {F : ι → C} [HasBiproduct F]

/-- Categorical dimensions are additive on finite direct sums. -/
theorem rightDimension_biproduct (p : PivotalStructure (C := C)) :
    p.rightTrace (𝟙 (⨁ F)) = ∑ i, p.rightTrace (𝟙 (F i)) :=
  by simpa using rightTrace_biproduct F p (𝟙 (⨁ F))

end

section
variable {k : Type*} [Field k] [IsAlgClosed k]
  {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
  [Preadditive C] [Linear k C] [MonoidalPreadditive C] [MonoidalLinear k C]
  {ι : Type*} [Fintype ι]

/-- Schur's lemma gives the scalar diagonal blocks of any endomorphism of a
finite direct sum of simple objects, and hence its weighted trace formula. -/
theorem rightTrace_biproduct_simple [HasKernels C]
    {F : ι → C} [HasBiproduct F] (hs : ∀ i, Simple (F i))
    (hfinite : ∀ i, FiniteDimensional k (F i ⟶ F i))
    (p : PivotalStructure (C := C)) (f : (⨁ F) ⟶ (⨁ F)) :
    ∃ c : ι → k, HasScalarDiagonal F f c ∧
      p.rightTrace f = ∑ i, c i • p.rightTrace (𝟙 (F i)) :=
  cyclicTrace_biproduct_simple (fun X ↦ rightTraceWithLinear (p.iso X))
    (fun f g ↦ p.rightTrace_cyclic f g) hs hfinite f

end

end PropertyF.Ground.Dimensions
