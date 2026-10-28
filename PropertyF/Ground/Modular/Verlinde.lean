module
public import PropertyF.Ground.Dimensions.DualCoherence
public import PropertyF.Ground.Dimensions.TensorMultiplicativity
public import PropertyF.Ground.Fusion.SpectralIntegral
public import PropertyF.Ground.Modular.Classification
public import PropertyF.Ground.Modular.SMatrix
public import PropertyF.Ground.Modular.SAdditivity

/-!
# Categorical partial traces, Verlinde identities, and Galois symmetry.
-/

@[expose] public noncomputable section

section
/-!
# Galois action from Verlinde's equations

The classification and complex-automorphism action require no old modular-data
bundle. The remaining hypotheses of the categorical theorem are stated as the
specific S-square, global nonvanishing and Verlinde equations that must be
proved from a nondegenerate spherical fusion category.
-/
open scoped BigOperators
open PropertyF.Ground.Dimensions

namespace PropertyF.Ground.Modular

/-- Complex automorphisms act on normalized S-matrix columns. -/
abbrev IsGaloisColumnAction {ι : Type*} (S : Matrix ι ι ℂ) (d : ι → ℂ)
    (act : (ℂ ≃+* ℂ) →* Equiv.Perm ι) : Prop :=
  ∀ (σ : ℂ ≃+* ℂ) i j, σ (S i j / d j) = S i (act σ j) / d (act σ j)

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {N : FusionRules ι} {u : ι}
variable {S : Matrix ι ι ℂ} {dual : ι → ι} {d : ι → ℂ} {D : ℂ}
variable (hd : ∀ y, d y ≠ 0) (hD : D ≠ 0)
include hd hD

/-- The full action on normalized columns follows from S-square and the
Verlinde character equations, without an assumed character classification. -/
theorem exists_galoisLabel_of_verlinde
    (hsym : ∀ x y, S x y = S y x) (hunit : ∀ x, S x N.unit = d x)
    (hsq : HasSSquare S dual D)
    (hVerlinde : HasVerlindeFormula N S d) :
    ∃ act : (ℂ ≃+* ℂ) →* Equiv.Perm ι, IsGaloisColumnAction S d act := by
  let columns : ι → Character N := fun j => {
    value := fun i => S i j / d j
    unit_eq := by rw [hsym, hunit]; exact div_self (hd j)
    mul_eq := fun i k => hVerlinde i k j }
  let e : ι ≃ Character N := Equiv.ofBijective columns
    (characters_bijective N columns (normalized_columns_linearIndependent hd hD hsym hsq))
  exact ⟨Character.galoisLabel e, fun σ i j ↦ (Character.galoisLabel_character e σ j i).symm⟩

omit hd hD in
/-- A Galois image of the dimension column determines a diagonal entry of S squared. -/
theorem galois_unit_column_square
    (hglobal : D = ∑ x, d x ^ 2) (hsym : ∀ x y, S x y = S y x)
    (hsq : HasSSquare S dual D) (σ : ℂ ≃+* ℂ) (y : ι)
    (hcol : ∀ x, S x y = d y * σ (d x)) :
    d y ^ 2 * σ D = if y = dual y then D else 0 := by
  calc
    d y ^ 2 * σ D = ∑ x, (d y * σ (d x)) ^ 2 := by
      simp only [hglobal, map_sum, Finset.mul_sum, map_pow, mul_pow]
    _ = ∑ x, S x y ^ 2 :=
      (congrArg (fun f : ι → ℂ => ∑ x, f x ^ 2) (funext hcol)).symm
    _ = ∑ x, S y x * S x y :=
      Finset.sum_congr rfl fun x _ ↦ by rw [hsym y x, pow_two]
    _ = _ := hsq y y

/-- Proposition 2.1 from the numerical S identities and the character equation,
with no modular-data hypothesis bundle. -/
theorem galois_unit_properties (hu : d u = 1)
    (hglobal : D = ∑ x, d x ^ 2) (hsym : ∀ x y, S x y = S y x)
    (hunit : ∀ x, S x u = d x) (hsq : HasSSquare S dual D)
    (σ : ℂ ≃+* ℂ) (y : ι) (hchar : ∀ x, σ (S x u / d u) = S x y / d y) :
    (∀ x, S x y = d y * σ (d x)) ∧ y = dual y ∧ σ D = D / d y ^ 2 := by
  have hcol (x : ι) : S x y = d y * σ (d x) :=
    ((div_eq_iff (hd y)).mp (by simpa only [hunit, hu, div_one] using (hchar x).symm)).trans
      (mul_comm _ _)
  have hsquare := galois_unit_column_square hglobal hsym hsq σ y hcol
  have hself : y = dual y := by
    by_contra hn
    rw [ite_eq_right hn] at hsquare
    exact mul_ne_zero (pow_ne_zero 2 (hd y))
      (by simpa using σ.injective.ne hD) hsquare
  refine ⟨hcol, hself, ?_⟩
  apply (eq_div_iff (pow_ne_zero 2 (hd y))).mpr
  rw [mul_comm, hsquare, ite_eq_left hself]

end




end PropertyF.Ground.Modular
end

section
/-!
# Partial traces of double braidings

Iterated pivotal trace and Schur's lemma give the normalized S entry as the
scalar partial trace on a simple surviving strand. The Hopf-link product reduces
to the displayed composition law for these partial traces, which remains open.
-/
open CategoryTheory CategoryTheory.MonoidalCategory
open PropertyF.Ground.Dimensions PropertyF.Ground.Calculus

namespace PropertyF.Ground.Modular
universe v u

/-- The partial trace of monodromy, leaving the first strand open. -/
abbrev partialMonodromy {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
    [RightRigidCategory C] [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C]
    [MonoidalLinear ℂ C] (p : PivotalStructure (C := C)) (X Y : C) : End X :=
  rightPartialTrace p X Y (End.of (doubleBraiding X Y))

/-- Closing one strand of a double braiding gives the normalized S scalar. -/
theorem partialTrace_doubleBraiding_simple (D : Ground.BraidedFusionCategory.{v,u})
    (p : PivotalStructure (C := D.Obj)) (k : Fin (rank D)) (X : D.Obj) :
    partialMonodromy p (simples D k) X =
      (Ground.unitScalarEquiv D (SEntry p (simples D k) X) / simpleDimension D p k) • 1 :=
  letI : Simple (simples D k) := simples_simple D k
  letI : FiniteDimensional ℂ (simples D k ⟶ simples D k) := Ground.IsFusionCategory.hom_finite _ _
  rightPartialTrace_simple_of_trace_compatibility (X := simples D k) (Y := X) p
    (Ground.unitScalarEquiv D) (End.of (doubleBraiding (simples D k) X))
    (simpleDimension_ne_zero D p k)
    (rightTrace_partialTrace p (End.of (doubleBraiding (simples D k) X)))

/-- Partial traces of double braiding multiply on a simple strand. -/
abbrev HasMultiplicativePartialTrace (D : Ground.BraidedFusionCategory.{v,u})
    (p : PivotalStructure (C := D.Obj)) : Prop :=
  ∀ i j k : Fin (rank D),
    partialMonodromy p (simples D k) (simples D i ⊗ simples D j) =
      partialMonodromy p (simples D k) (simples D i) *
        partialMonodromy p (simples D k) (simples D j)

/-- Multiplicative partial traces imply the Hopf-link product rule. -/
theorem hopf_product_of_partialTrace_composition (D : Ground.BraidedFusionCategory.{v,u})
    (p : PivotalStructure (C := D.Obj)) (hcomp : HasMultiplicativePartialTrace D p) :
    HasHopfProduct D p := by
  intro i j k
  let _ : Simple (simples D k) := simples_simple D k
  have hv := smul_left_injective ℂ (one_ne_zero : (1 : End (simples D k)) ≠ 0) (by
    simpa only [partialTrace_doubleBraiding_simple, smul_mul_smul, one_mul] using hcomp i j k)
  field_simp [simpleDimension_ne_zero D p k] at hv
  simpa only [SEntry_symmetric p (simples D k) (simples D i ⊗ simples D j),
    SEntry_symmetric p (simples D k) (simples D i),
    SEntry_symmetric p (simples D k) (simples D j), categoricalS] using hv

end PropertyF.Ground.Modular
end

section
/-! The unit axiom of a pivotal structure normalizes the tensor-unit trace. -/
open CategoryTheory CategoryTheory.MonoidalCategory
open PropertyF.Ground.Dimensions

namespace PropertyF.Ground.Modular
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]

/-- The dimension of the simple representative of the tensor unit is one. -/
theorem simpleDimension_unit (C : Ground.BraidedFusionCategory.{v,u})
    (p : PivotalStructure (C := C.Obj)) : simpleDimension C p (unitIndex C) = 1 :=
  (unitIndex_iso C).elim fun e ↦ by
    simp only [simpleDimension, p.rightTrace_id_iso e, Dimensions.rightTrace_unit, map_one]

end PropertyF.Ground.Modular
end

section
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
variable (p : PivotalStructure (C := C))

/-- Partial trace is natural for morphisms on the surviving strand. -/
theorem rightPartialTrace_natural {A B : C} (Y : C)
    (f : A ⟶ B) (g : B ⟶ A) (t : End (B ⊗ Y)) :
    rightPartialTrace p A Y (End.of ((f ▷ Y) ≫ t.asHom ≫ (g ▷ Y))) =
      End.of (f ≫ (rightPartialTrace p B Y t).asHom ≫ g) :=
  End.ext (by
    simp only [rightPartialTrace, LinearMap.coe_mk, AddHom.coe_mk,
      comp_whiskerRight, Category.assoc]
    rw [← associator_inv_naturality_left_assoc, whisker_exchange_assoc,
      ← rightUnitor_inv_naturality_assoc]
    rw [associator_naturality_left_assoc, ← whisker_exchange_assoc,
      ← whisker_exchange_assoc, rightUnitor_naturality])

variable [CategoryTheory.Limits.HasKernels C]
/-- When the surviving object is simple with nonzero dimension, successive
partial traces agree with tracing the combined tensor factor. -/
theorem rightPartialTrace_nested_simple (scalar : End (𝟙_ C) ≃ₐ[ℂ] ℂ) (Z X Y : C)
    [Simple Z] [FiniteDimensional ℂ (Z ⟶ Z)]
    (hd : scalar (p.rightTrace (𝟙 Z)) ≠ 0) (f : End (Z ⊗ (X ⊗ Y))) :
    rightPartialTrace p Z (X ⊗ Y) f =
      rightPartialTrace p Z X (rightPartialTrace p (Z ⊗ X) Y
        (End.of ((α_ Z X Y).hom ≫ f.asHom ≫ (α_ Z X Y).inv))) := by
  let g : End ((Z ⊗ X) ⊗ Y) := End.of ((α_ Z X Y).hom ≫ f.asHom ≫ (α_ Z X Y).inv)
  have hc : p.rightTrace g.asHom = p.rightTrace f.asHom := by
    simpa [g, Category.assoc] using
      p.rightTrace_cyclic ((α_ Z X Y).hom ≫ f.asHom) (α_ Z X Y).inv
  rw [rightPartialTrace_simple_of_trace_compatibility (X := Z) (Y := X ⊗ Y) p scalar f hd
      (rightTrace_partialTrace p f),
    rightPartialTrace_simple_of_trace_compatibility (X := Z) (Y := X) p scalar _ hd
      (rightTrace_partialTrace p (rightPartialTrace p (Z ⊗ X) Y g))]
  simp only [Calculus.scalarTrace, rightTrace_partialTrace p g, hc]


end Trace

section MonodromyTrace
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [RightRigidCategory C] [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]

/-- Partial tracing a tensor-product monodromy leaves a conjugated partial monodromy. -/
theorem partialTrace_doubleBraiding_factor (p : PivotalStructure (C := C)) (Z X Y : C) :
    rightPartialTrace p (Z ⊗ X) Y
      (End.of ((α_ Z X Y).hom ≫ doubleBraiding Z (X ⊗ Y) ≫ (α_ Z X Y).inv)) =
    End.of ((β_ Z X).hom ≫ (X ◁ (partialMonodromy p Z Y).asHom) ≫ (β_ X Z).hom) := by
  let t : End ((X ⊗ Z) ⊗ Y) := End.of ((α_ X Z Y).hom ≫
    (X ◁ doubleBraiding Z Y) ≫ (α_ X Z Y).inv)
  have hfactor : End.of ((α_ Z X Y).hom ≫ doubleBraiding Z (X ⊗ Y) ≫ (α_ Z X Y).inv) =
      End.of (((β_ Z X).hom ▷ Y) ≫ t.asHom ≫ ((β_ X Z).hom ▷ Y)) := by
    apply End.ext
    simpa [t, Category.assoc] using doubleBraiding_tensor_factorization Z X Y
  rw [hfactor, rightPartialTrace_natural, Calculus.rightPartialTrace_whiskerLeft]

end MonodromyTrace

/-- Double-braiding partial traces multiply on a simple surviving strand. -/
theorem partialTrace_doubleBraiding_tensor (D : Ground.BraidedFusionCategory.{v,u})
    (p : PivotalStructure (C := D.Obj)) : HasMultiplicativePartialTrace D p := by
  intro i j k
  let Z : D.Obj := simples D k
  let X : D.Obj := simples D i
  let Y : D.Obj := simples D j
  let _ : Simple Z := simples_simple D k
  let _ : FiniteDimensional ℂ (Z ⟶ Z) := Ground.IsFusionCategory.hom_finite _ _
  let s : ℂ := Ground.unitScalarEquiv D (SEntry p Z Y) / simpleDimension D p k
  let f : End (Z ⊗ (X ⊗ Y)) := End.of (doubleBraiding Z (X ⊗ Y))
  have hs : partialMonodromy p Z Y = s • 1 :=
    partialTrace_doubleBraiding_simple D p k Y
  change rightPartialTrace p Z (X ⊗ Y) f =
    rightPartialTrace p Z X (End.of (doubleBraiding Z X)) *
      rightPartialTrace p Z Y (End.of (doubleBraiding Z Y))
  rw [rightPartialTrace_nested_simple p (Ground.unitScalarEquiv D) Z X Y
    (simpleDimension_ne_zero D p k) f]
  rw [partialTrace_doubleBraiding_factor]
  change rightPartialTrace p Z Y (End.of (doubleBraiding Z Y)) = s • 1 at hs
  dsimp only [partialMonodromy]
  rw [hs]
  have he : End.of ((β_ Z X).hom ≫ (X ◁ (s • (1 : End Z)).asHom) ≫ (β_ X Z).hom) =
      s • End.of (doubleBraiding Z X) := by
    apply End.ext
    simp [doubleBraiding]
  rw [he, map_smul]
  simp


/-- The normalized S columns satisfy the Verlinde fusion-character equations. -/
theorem categoricalS_verlinde (D : Ground.BraidedFusionCategory.{v,u})
    (p : PivotalStructure (C := D.Obj)) :
    HasVerlindeFormula ⟨unitIndex D, fusionCoeff D⟩ (categoricalS D p) (simpleDimension D p) :=
  categoricalS_verlinde_of_hopf_product D p
    (hopf_product_of_partialTrace_composition D p (partialTrace_doubleBraiding_tensor D p))

end PropertyF.Ground.Modular
end
