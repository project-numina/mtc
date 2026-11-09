module
public import MTC.PropertyF.Pivotal.NondegeneracyHaar

open MTC.Fusion MTC.Modular MTC.CategoryTheory.Dimensions MTC.Center.Induction MTC.Center.Trace
open scoped BigOperators

/-! Fusion-basis expansion for the categorical Haar sliding argument. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
namespace MTC.PropertyF.Pivotal
universe v u
variable (C : BraidedFusionCategory.{v,u})
attribute [local instance] Abelian.hasFiniteBiproducts

/-- Restrict a sum of finite dependent fibers to labels whose fibers can be nonempty. -/
theorem sum_fin_fibers_eq_sum_support {ι A : Type*} [Fintype ι] [DecidableEq ι] [AddCommMonoid A]
    (S : Finset ι) (n : ι → ℕ) (f : ∀ i, Fin (n i) → A)
    (hs : ∀ i, i ∉ S → n i = 0) :
    (∑ i ∈ S, ∑ a, f i a) = ∑ i, ∑ a, f i a := by
  apply Finset.sum_subset (Finset.subset_univ S)
  intro i _ hi
  simp only [hs i hi, Fin.isEmpty_iff, Finset.univ_eq_empty, Finset.sum_empty]

/-- A natural endomorphism of the tensor-right functor is the contraction
of its simple components with the actual fusion inclusions and projections. -/
theorem natural_tensor_family_simple_expansion {V : C.Obj} (T : C.Obj)
    (β : ∀ X : C.Obj, End (X ⊗ V))
    (hβ : ∀ {X Y : C.Obj} (f : X ⟶ Y),
      (f ▷ V) ≫ (β Y).asHom = (β X).asHom ≫ (f ▷ V)) :
    (β T).asHom = ∑ q : simplePieces C T,
      (simpleProjection T q.1 q.2 ▷ V) ≫ (β (simples C q.1)).asHom ≫
        (simpleInclusion C T q.1 q.2 ▷ V) := by
  classical
  calc
    _ = (𝟙 T ▷ V) ≫ (β T).asHom := by simp
    _ = (∑ q : simplePieces C T,
        (simpleProjection T q.1 q.2 ≫ simpleInclusion C T q.1 q.2) ▷ V) ≫ (β T).asHom := by
          rw [← sum_whiskerRight, simple_completeness]
    _ = _ := by
      simp only [Preadditive.sum_comp, comp_whiskerRight, Category.assoc, hβ]

/-- Monodromy supplies the natural family used in the Haar calculation. -/
theorem monodromy_simple_expansion (V T : C.Obj) :
    doubleBraiding T V = ∑ q : simplePieces C T,
      (simpleProjection T q.1 q.2 ▷ V) ≫ doubleBraiding (simples C q.1) V ≫
        (simpleInclusion C T q.1 q.2 ▷ V) := by
  exact natural_tensor_family_simple_expansion C T
    (fun X ↦ End.of (doubleBraiding X V))
    (fun f ↦ (doubleBraiding_natural_left f V).symm)

/-- The left partial trace is additive on actual endomorphisms. -/
theorem leftPartialTrace_sum (p : PivotalStructure (C := C.Obj))
    {I : Type*} [Fintype I] (X Y : C.Obj) (f : I → End (X ⊗ Y)) :
    leftPartialTrace p (∑ i, f i) = ∑ i, leftPartialTrace p (f i) := by
  classical
  apply End.ext
  simpa only [End.sum_asHom, ← leftPartialTraceHom_end] using
    leftPartialTraceHom_sum C p X Y Y (fun i ↦ (f i).asHom)

/-- DGNO's Haar operator for any actual family of endomorphisms of `(-) ⊗ V`.
Naturality is an independent property of the supplied family. -/
def categoricalHaar (p : PivotalStructure (C := C.Obj)) (V U : C.Obj)
    (β : ∀ X : C.Obj, End (X ⊗ V)) : End (U ⊗ V) :=
  ∑ i : Fin (rank C), simpleDimension C p i •
    leftPartialTrace p (End.of ((α_ (simples C i) U V).inv ≫
      (β (simples C i ⊗ U)).asHom ≫ (α_ (simples C i) U V).hom))

/-- The monodromy Haar loop is the specialization of the general operator
to the actual monodromy family. -/
theorem categoricalHaar_monodromy (p : PivotalStructure (C := C.Obj)) (U V : C.Obj) :
    categoricalHaar C p V U (fun X ↦ End.of (doubleBraiding X V)) =
      monodromyHaar C p U V := rfl

/-- Fusion expansion of a single actual pivotal loop summand. -/
theorem haarSummand_fusion_expansion (p : PivotalStructure (C := C.Obj))
    (U : C.Obj) {V : C.Obj} (j : Fin (rank C))
    (β : ∀ X : C.Obj, End (X ⊗ V))
    (hβ : ∀ {X Y : C.Obj} (f : X ⟶ Y),
      (f ▷ V) ≫ (β Y).asHom = (β X).asHom ≫ (f ▷ V)) :
    simpleDimension C p j • leftPartialTraceHom C p (simples C j) (U ⊗ V) (U ⊗ V)
      ((α_ (simples C j) U V).inv ≫ (β (simples C j ⊗ U)).asHom ≫ (α_ (simples C j) U V).hom) =
    ∑ i : Fin (rank C), ∑ a : Fin (Module.finrank ℂ (simples C i ⟶ simples C j ⊗ U)),
      simpleDimension C p j • leftPartialTraceHom C p (simples C j) (U ⊗ V) (U ⊗ V)
        ((α_ (simples C j) U V).inv ≫ (simpleProjection (simples C j ⊗ U) i a ▷ V) ≫
          (β (simples C i)).asHom ≫ (simpleInclusion C (simples C j ⊗ U) i a ▷ V) ≫
          (α_ (simples C j) U V).hom) := by
  classical
  rw [natural_tensor_family_simple_expansion C (simples C j ⊗ U) β hβ]
  simp only [Preadditive.comp_sum, Preadditive.sum_comp, leftPartialTraceHom_sum,
    Finset.smul_sum, Fintype.sum_sigma, Category.assoc]

/-- If a tensor product has no simple summands outside `S`, its Haar
summand expansion can be restricted to labels in `S`. -/
theorem haarSummand_fusion_expansion_restricted (p : PivotalStructure (C := C.Obj))
    (U : C.Obj) {V : C.Obj} (j : Fin (rank C))
    (β : ∀ X : C.Obj, End (X ⊗ V))
    (hβ : ∀ {X Y : C.Obj} (f : X ⟶ Y),
      (f ▷ V) ≫ (β Y).asHom = (β X).asHom ≫ (f ▷ V))
    (S : Finset (Fin (rank C)))
    (hs : ∀ i ∉ S, Module.finrank ℂ (simples C i ⟶ simples C j ⊗ U) = 0) :
    simpleDimension C p j • leftPartialTraceHom C p (simples C j) (U ⊗ V) (U ⊗ V)
      ((α_ (simples C j) U V).inv ≫ (β (simples C j ⊗ U)).asHom ≫ (α_ (simples C j) U V).hom) =
    ∑ i ∈ S, ∑ a : Fin (Module.finrank ℂ (simples C i ⟶ simples C j ⊗ U)),
      simpleDimension C p j • leftPartialTraceHom C p (simples C j) (U ⊗ V) (U ⊗ V)
        ((α_ (simples C j) U V).inv ≫ (simpleProjection (simples C j ⊗ U) i a ▷ V) ≫
          (β (simples C i)).asHom ≫ (simpleInclusion C (simples C j ⊗ U) i a ▷ V) ≫
          (α_ (simples C j) U V).hom) := by
  classical
  rw [haarSummand_fusion_expansion C p U j β hβ]
  exact (sum_fin_fibers_eq_sum_support S _ _ hs).symm

/-- The first fusion-basis expansion in DGNO's Haar identity applies to any
natural tensor family, not just monodromy. -/
theorem categoricalHaar_fusion_expansion (p : PivotalStructure (C := C.Obj))
    (U : C.Obj) {V : C.Obj} (β : ∀ X : C.Obj, End (X ⊗ V))
    (hβ : ∀ {X Y : C.Obj} (f : X ⟶ Y),
      (f ▷ V) ≫ (β Y).asHom = (β X).asHom ≫ (f ▷ V)) :
    categoricalHaar C p V U β = ∑ i : Fin (rank C),
      ∑ q : simplePieces C (simples C i ⊗ U),
      simpleDimension C p i • leftPartialTrace p (End.of
        ((α_ (simples C i) U V).inv ≫
          (simpleProjection (simples C i ⊗ U) q.1 q.2 ▷ V) ≫
          (β (simples C q.1)).asHom ≫
          (simpleInclusion C (simples C i ⊗ U) q.1 q.2 ▷ V) ≫
          (α_ (simples C i) U V).hom)) := by
  classical
  unfold categoricalHaar
  apply Finset.sum_congr rfl
  intro i _
  apply End.ext
  simpa only [End.sum_asHom, End.smul_asHom, Fintype.sum_sigma,
    leftPartialTraceHom, leftPartialTrace] using
    haarSummand_fusion_expansion C p U i β hβ

/-- Expanding monodromy through simple tensor-product summands gives the
first double sum in the DGNO Haar sliding calculation. -/
theorem monodromyHaar_fusion_expansion (p : PivotalStructure (C := C.Obj))
    (U V : C.Obj) :
    monodromyHaar C p U V = ∑ i : Fin (rank C), ∑ q : simplePieces C (simples C i ⊗ U),
      simpleDimension C p i • leftPartialTrace p (End.of
        ((α_ (simples C i) U V).inv ≫
          (simpleProjection (simples C i ⊗ U) q.1 q.2 ▷ V) ≫
          doubleBraiding (simples C q.1) V ≫
          (simpleInclusion C (simples C i ⊗ U) q.1 q.2 ▷ V) ≫
          (α_ (simples C i) U V).hom)) := by
  simpa only [categoricalHaar_monodromy] using
    categoricalHaar_fusion_expansion C p U
      (fun X ↦ End.of (doubleBraiding X V))
      (fun f ↦ (doubleBraiding_natural_left f V).symm)

end MTC.PropertyF.Pivotal
end
