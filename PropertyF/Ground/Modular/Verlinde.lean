module
public import PropertyF.Ground.Modular.HopfPartialTrace
public import PropertyF.Ground.Modular.PseudoGalois

/-!
# Verlinde characters from categorical trace

The hexagon identity factors double braiding around a tensor product. Naturality
and associator coherence of the partial trace, together with Schur's lemma,
give the Hopf-link product identity on a simple strand. Additivity on the
semisimple tensor-product decomposition then proves the Verlinde equations.
-/
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.BraidedCategory
open PropertyF.Ground.Dimensions PropertyF.Ground.Calculus
open scoped BigOperators
@[expose] public noncomputable section
namespace PropertyF.Ground.Modular
universe v u
section Braiding
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
/-- The two braiding hexagons factor monodromy around a tensor product. -/
theorem doubleBraiding_tensor_factorization (Z X Y : C) :
    (α_ Z X Y).hom ≫ doubleBraiding Z (X ⊗ Y) ≫ (α_ Z X Y).inv =
      ((β_ Z X).hom ▷ Y) ≫ (α_ X Z Y).hom ≫ (X ◁ doubleBraiding Z Y) ≫
        (α_ X Z Y).inv ≫ ((β_ X Z).hom ▷ Y) := by
  simp only [doubleBraiding, braiding_tensor_right_hom, braiding_tensor_left_hom,
    whiskerLeft_comp, Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id_assoc,
    Iso.hom_inv_id, Category.comp_id]

end Braiding
section Trace
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
  [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
/-- Partial trace is natural for morphisms on the surviving strand. -/
theorem rightPartialTrace_natural (p : PivotalStructure (C := C)) {A B : C} (Y : C)
    (f : A ⟶ B) (g : B ⟶ A) (t : End (B ⊗ Y)) :
    rightPartialTrace p A Y (End.of ((f ▷ Y) ≫ t.asHom ≫ (g ▷ Y))) =
      End.of (f ≫ (rightPartialTrace p B Y t).asHom ≫ g) := by
  apply End.ext
  simp only [rightPartialTrace, LinearMap.coe_mk, AddHom.coe_mk,
    comp_whiskerRight, Category.assoc]
  rw [← associator_inv_naturality_left_assoc, whisker_exchange_assoc,
    ← rightUnitor_inv_naturality_assoc]
  rw [associator_naturality_left_assoc, ← whisker_exchange_assoc,
    ← whisker_exchange_assoc, rightUnitor_naturality]

/-- Partial trace commutes with adding an untouched strand on the left. -/
theorem rightPartialTrace_whiskerLeft (p : PivotalStructure (C := C))
    (X Z Y : C) (t : End (Z ⊗ Y)) :
    rightPartialTrace p (X ⊗ Z) Y
      (End.of ((α_ X Z Y).hom ≫ (X ◁ t.asHom) ≫ (α_ X Z Y).inv)) =
      End.of (X ◁ (rightPartialTrace p Z Y t).asHom) := by
  apply End.ext
  simp only [rightPartialTrace, LinearMap.coe_mk, AddHom.coe_mk,
    comp_whiskerRight, Category.assoc]
  simp only [whiskerLeft_comp]
  monoidal

end Trace
section Nested
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
  [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [CategoryTheory.Limits.HasKernels C]
/-- When the surviving object is simple with nonzero dimension, successive
partial traces agree with tracing the combined tensor factor. -/
theorem rightPartialTrace_nested_simple (p : PivotalStructure (C := C))
    (scalar : End (𝟙_ C) ≃ₐ[ℂ] ℂ) (Z X Y : C)
    [Simple Z] [FiniteDimensional ℂ (Z ⟶ Z)]
    (hd : scalar (p.rightTrace (𝟙 Z)) ≠ 0) (f : End (Z ⊗ (X ⊗ Y))) :
    rightPartialTrace p Z (X ⊗ Y) f =
      rightPartialTrace p Z X (rightPartialTrace p (Z ⊗ X) Y
        (End.of ((α_ Z X Y).hom ≫ f.asHom ≫ (α_ Z X Y).inv))) := by
  let g : End ((Z ⊗ X) ⊗ Y) := End.of ((α_ Z X Y).hom ≫ f.asHom ≫ (α_ Z X Y).inv)
  have hc : p.rightTrace g.asHom = p.rightTrace f.asHom := by
    have h := p.rightTrace_cyclic ((α_ Z X Y).hom ≫ f.asHom) (α_ Z X Y).inv
    simpa [g, Category.assoc] using h
  have ht1 := rightTrace_partialTrace p Z (X ⊗ Y) f
  have ht2 := rightTrace_partialTrace p Z X (rightPartialTrace p (Z ⊗ X) Y g)
  have ht3 := rightTrace_partialTrace p (Z ⊗ X) Y g
  rw [rightPartialTrace_simple_of_trace_compatibility Z (X ⊗ Y) p scalar f hd ht1,
    rightPartialTrace_simple_of_trace_compatibility Z X p scalar _ hd ht2, ht3, hc]


end Nested

/-- Double-braiding partial traces multiply on a simple surviving strand. -/
theorem partialTrace_doubleBraiding_tensor (D : Ground.BraidedFusionCategory.{v,u})
    (p : PivotalStructure (C := D.Obj)) (i j k : Fin (rank D)) :
    rightPartialTrace p (simples D k) (simples D i ⊗ simples D j)
      (End.of (doubleBraiding (simples D k) (simples D i ⊗ simples D j))) =
    rightPartialTrace p (simples D k) (simples D i)
      (End.of (doubleBraiding (simples D k) (simples D i))) *
    rightPartialTrace p (simples D k) (simples D j)
      (End.of (doubleBraiding (simples D k) (simples D j))) := by
  let Z : D.Obj := simples D k
  let X : D.Obj := simples D i
  let Y : D.Obj := simples D j
  let _ : Simple Z := simples_simple D k
  let _ : FiniteDimensional ℂ (Z ⟶ Z) := Ground.IsFusionCategory.hom_finite _ _
  let s : ℂ := Ground.unitScalarEquiv D (SEntry p Z Y) / simpleDimension D p k
  let f : End (Z ⊗ (X ⊗ Y)) := End.of (doubleBraiding Z (X ⊗ Y))
  let t : End ((X ⊗ Z) ⊗ Y) := End.of ((α_ X Z Y).hom ≫
    (X ◁ doubleBraiding Z Y) ≫ (α_ X Z Y).inv)
  have hs : rightPartialTrace p Z Y (End.of (doubleBraiding Z Y)) = s • 1 :=
    partialTrace_doubleBraiding_simple D p k Y
  change rightPartialTrace p Z (X ⊗ Y) f =
    rightPartialTrace p Z X (End.of (doubleBraiding Z X)) *
      rightPartialTrace p Z Y (End.of (doubleBraiding Z Y))
  rw [rightPartialTrace_nested_simple p (Ground.unitScalarEquiv D) Z X Y
    (simpleDimension_ne_zero D p k) f]
  have hfactor : End.of ((α_ Z X Y).hom ≫ f.asHom ≫ (α_ Z X Y).inv) =
      End.of (((β_ Z X).hom ▷ Y) ≫ t.asHom ≫ ((β_ X Z).hom ▷ Y)) := by
    apply End.ext
    simpa [f, t, Category.assoc] using doubleBraiding_tensor_factorization Z X Y
  rw [hfactor, rightPartialTrace_natural, rightPartialTrace_whiskerLeft, hs]
  have he : End.of ((β_ Z X).hom ≫ (X ◁ (s • (1 : End Z)).asHom) ≫ (β_ X Z).hom) =
      s • End.of (doubleBraiding Z X) := by
    apply End.ext
    simp [doubleBraiding]
  rw [he, map_smul]
  simp


/-- The normalized S columns satisfy the Verlinde fusion-character equations. -/
theorem categoricalS_verlinde (D : Ground.BraidedFusionCategory.{v,u})
    (p : PivotalStructure (C := D.Obj)) : ∀ i j k,
    (categoricalS D p i k / simpleDimension D p k) *
      (categoricalS D p j k / simpleDimension D p k) =
    ∑ l, (fusionCoeff D i j l : ℂ) * (categoricalS D p l k / simpleDimension D p k) :=
  categoricalS_verlinde_of_hopf_product D p
    (hopf_product_of_partialTrace_composition D p (partialTrace_doubleBraiding_tensor D p))

/-- In the pseudo-unitary case, S-square alone now gives the Galois action. -/
theorem categoricalS_galois_action_of_S_square (D : Ground.BraidedFusionCategory.{v,u})
    (h : Ground.PseudoUnitary D) (p : PivotalStructure (C := D.Obj))
    (hsq : ∀ x y, ∑ z, categoricalS D p x z * categoricalS D p z y =
      if x = Ground.dualIndex D y then globalDimension D else 0) :
    ∃ act : (ℂ ≃+* ℂ) →* Equiv.Perm (Fin (rank D)), ∀ (σ : ℂ ≃+* ℂ) i j,
      σ (categoricalS D p i j / simpleDimension D p j) =
        categoricalS D p i (act σ j) / simpleDimension D p (act σ j) :=
  categoricalS_galois_action_pseudoUnitary D h p hsq (categoricalS_verlinde D p)

end PropertyF.Ground.Modular
