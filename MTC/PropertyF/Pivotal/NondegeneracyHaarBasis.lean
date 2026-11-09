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

/-- A natural endomorphism of the tensor-right functor is the contraction
of its simple components with the actual fusion inclusions and projections. -/
theorem natural_tensor_family_simple_expansion (V T : C.Obj)
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
      simp only [Preadditive.sum_comp, comp_whiskerRight, Category.assoc]
      apply Finset.sum_congr rfl
      intro q _
      rw [hβ]

/-- Monodromy supplies the natural family used in the Haar calculation. -/
theorem monodromy_simple_expansion (V T : C.Obj) :
    doubleBraiding T V = ∑ q : simplePieces C T,
      (simpleProjection T q.1 q.2 ▷ V) ≫ doubleBraiding (simples C q.1) V ≫
        (simpleInclusion C T q.1 q.2 ▷ V) := by
  exact natural_tensor_family_simple_expansion C V T
    (fun X ↦ End.of (doubleBraiding X V))
    (fun f ↦ (doubleBraiding_natural_left f V).symm)

/-- The left partial trace is additive on actual endomorphisms. -/
theorem leftPartialTrace_sum (p : PivotalStructure (C := C.Obj))
    {I : Type*} [Fintype I] (X Y : C.Obj) (f : I → End (X ⊗ Y)) :
    leftPartialTrace p (∑ i, f i) = ∑ i, leftPartialTrace p (f i) := by
  classical
  apply End.ext
  simp [leftPartialTrace, whiskerLeft_sum, Preadditive.sum_comp, Preadditive.comp_sum]

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

/-- The first fusion-basis expansion in DGNO's Haar identity applies to any
natural tensor family, not just monodromy. -/
theorem categoricalHaar_fusion_expansion (p : PivotalStructure (C := C.Obj))
    (U V : C.Obj) (β : ∀ X : C.Obj, End (X ⊗ V))
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
  rw [natural_tensor_family_simple_expansion C V (simples C i ⊗ U) β hβ]
  simp only [Preadditive.comp_sum, Preadditive.sum_comp]
  let F (q : simplePieces C (simples C i ⊗ U)) :
      (simples C i ⊗ (U ⊗ V)) ⟶ (simples C i ⊗ (U ⊗ V)) :=
    (α_ (simples C i) U V).inv ≫
      ((simpleProjection (simples C i ⊗ U) q.1 q.2 ▷ V) ≫
        (β (simples C q.1)).asHom ≫
          (simpleInclusion C (simples C i ⊗ U) q.1 q.2 ▷ V)) ≫
        (α_ (simples C i) U V).hom
  have he : End.of (∑ q, F q) = ∑ q, End.of (F q) := by
    apply End.ext
    simp
  change simpleDimension C p i • leftPartialTrace p (End.of (∑ q, F q)) = _
  rw [he, leftPartialTrace_sum, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro q _
  simp only [F, Category.assoc]

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
    categoricalHaar_fusion_expansion C p U V
      (fun X ↦ End.of (doubleBraiding X V))
      (fun f ↦ (doubleBraiding_natural_left f V).symm)

end MTC.PropertyF.Pivotal
end
