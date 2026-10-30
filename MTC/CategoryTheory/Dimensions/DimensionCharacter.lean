module
public import MTC.CategoryTheory.Dimensions.BiproductTrace
public import MTC.CategoryTheory.Dimensions.DualCoherence
public import MTC.CategoryTheory.Dimensions.TensorMultiplicativity
public import MTC.Fusion.ObjectDimension
public import MTC.CategoryTheory.Dimensions.GroundNorm

/-! # Pivotal dimension characters

Pivotal dimension is additive and multiplicative; simple dimensions determine sphericality.

## Main results

* `pivotalDimension`: defines the scalar pivotal trace of an object.
* `pivotalDimension_character`: shows that dimensions satisfy the fusion multiplication rules.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open scoped BigOperators
namespace MTC.Dimensions
universe v u

variable (C : BraidedFusionCategory.{v,u})
attribute [local instance] Abelian.hasFiniteBiproducts

/-- Complex pivotal dimension obtained using the canonical unit scalar map. -/
def pivotalDimension (C : BraidedFusionCategory.{v,u})
    (p : PivotalStructure (C := C.Obj)) (X : C.Obj) : ℂ :=
  unitScalar C (p.rightTrace (𝟙 X))

/-- A spherical structure whose simple dimensions are the FP dimensions. -/
abbrev HasFPSphericalStructure (C : BraidedFusionCategory.{v,u}) : Prop :=
  ∃ p : PivotalStructure (C := C.Obj), p.IsSpherical ∧ ∀ i,
    pivotalDimension C p (simples C i) = (fpSimple C i : ℂ)

variable (p : PivotalStructure (C := C.Obj))

variable {X : C.Obj} in
/-- Pivotal dimension is a sum of simple dimensions with the actual Hom-space
multiplicities, for any pivotal structure. -/
theorem pivotalDimension_decomposition :
    pivotalDimension C p X = ∑ i, (simpleMultiplicity C i X : ℂ) *
      pivotalDimension C p (simples C i) :=
  (exists_canonical_decomposition C X).elim fun e ↦ by
    simp [pivotalDimension, MTC.unitScalar_eq_equiv, p.rightTrace_id_iso e,
      rightDimension_biproduct, Fintype.sum_sigma]

/-- Agreement with FP dimension on simples extends to all objects. -/
theorem pivotalDimension_eq_fp {C : BraidedFusionCategory.{v,u}} {p : PivotalStructure (C := C.Obj)}
    (hsimple : ∀ i, pivotalDimension C p (simples C i) = (fpSimple C i : ℂ))
    (X : C.Obj) : pivotalDimension C p X = (fpDimension C X : ℂ) := by
  simpa only [fpDimension, Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_natCast,
    hsimple] using pivotalDimension_decomposition C p (X := X)

variable {C} in
/-- Pivotal dimensions multiply under tensor products. -/
theorem pivotalDimension_tensor (X Y : C.Obj) :
    pivotalDimension C p (X ⊗ Y) = pivotalDimension C p X * pivotalDimension C p Y := by
  simpa [pivotalDimension, MTC.unitScalar_eq_equiv] using
    pivotalTrace_tensor p (MTC.unitScalarEquiv C) (𝟙 X) (𝟙 Y)

/-- Pivotal simple dimensions form a fusion character. -/
theorem pivotalDimension_character :
    IsFusionMultiplicative C (fun i => pivotalDimension C p (simples C i)) :=
  fun i j ↦ (pivotalDimension_tensor p (simples C i) (simples C j)).symm.trans
    (pivotalDimension_decomposition C p (X := _))

variable {C} in
/-- Pivotal dimension is invariant under object isomorphism. -/
theorem pivotalDimension_iso
    {X Y : C.Obj} (e : X ≅ Y) :
    pivotalDimension C p X = pivotalDimension C p Y :=
  congrArg (unitScalar C) (p.rightTrace_id_iso e)

/-- The pivotal dimension of the simple representative of the unit is one. -/
theorem pivotalDimension_unitIndex :
    pivotalDimension C p (simples C (unitIndex C)) = 1 :=
  (unitIndex_iso C).elim fun e ↦ (pivotalDimension_iso p e).trans (by
    simpa [pivotalDimension, rightTrace_unit] using unitScalar_algebraMap C 1)

end MTC.Dimensions

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open scoped BigOperators
namespace MTC.Dimensions
universe v u
variable {k : Type*} [CommSemiring k] {C : Type u} [Category.{v} C] [MonoidalCategory C] [RigidCategory C]
  [Preadditive C] [Linear k C] [MonoidalPreadditive C] [MonoidalLinear k C]

/-- Left pivotal trace as a linear map on an endomorphism space. -/
def leftTraceLinear (p : PivotalStructure (C := C)) (X : C) :
    (X ⟶ X) →ₗ[k] End (𝟙_ C) where
  toFun := p.leftTrace
  map_add' := p.leftTrace_add
  map_smul' := p.leftTrace_smul

/-- If diagonal blocks are scalar, the left trace is their dimension-weighted sum. -/
theorem leftTrace_biproduct_scalar_blocks {ι : Type*} [Fintype ι]
    {F : ι → C} [HasBiproduct F] (p : PivotalStructure (C := C))
    (f : (⨁ F) ⟶ (⨁ F)) {c : ι → k}
    (hc : HasScalarDiagonal F f c) : p.leftTrace f = ∑ i, c i • p.leftTrace (𝟙 (F i)) :=
  cyclicTrace_biproduct_scalar_blocks (leftTraceLinear p)
    (fun f g => leftTrace_cyclic p f g) f hc

end MTC.Dimensions

namespace MTC.Dimensions
universe v u

variable (C : BraidedFusionCategory.{v,u})
attribute [local instance] Abelian.hasFiniteBiproducts

/-- In a fusion category it suffices to compare left and right dimensions on
simple representatives to verify sphericality on all endomorphisms. -/
theorem isSpherical_iff_simple_dimensions
    (p : PivotalStructure (C := C.Obj)) :
    p.IsSpherical ↔ ∀ i : Fin (rank C),
      p.leftTrace (𝟙 (simples C i)) = p.rightTrace (𝟙 (simples C i)) :=
  ⟨fun h i ↦ h _ _, fun hs X f ↦ by
    let V : (Σ i, Fin (simpleMultiplicity C i X)) → C.Obj := fun a ↦ simples C a.1
    let e : X ≅ ⨁ V := Classical.choice (exists_canonical_decomposition C X)
    let g : (⨁ V) ⟶ (⨁ V) := e.inv ≫ f ≫ e.hom
    obtain ⟨c, hc, htrace⟩ := rightTrace_biproduct_simple (k := ℂ)
      (fun (a : Σ i, Fin (simpleMultiplicity C i X)) ↦ simples_simple C a.1)
      (fun _ ↦ IsFusionCategory.hom_finite _ _) p g
    simp only [show p.leftTrace f = p.leftTrace g from by
          simpa [g, Category.assoc] using (leftTrace_cyclic p e.hom (e.inv ≫ f)),
      show p.rightTrace f = p.rightTrace g from by
        simpa [g, Category.assoc] using (p.rightTrace_cyclic e.hom (e.inv ≫ f)),
      htrace, leftTrace_biproduct_scalar_blocks p g hc, V, hs]⟩

end MTC.Dimensions
