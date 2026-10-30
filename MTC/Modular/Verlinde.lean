module
public import MTC.CategoryTheory.Dimensions.DimensionCharacter
public import MTC.CategoryTheory.Dimensions.DualCoherence
public import MTC.CategoryTheory.Dimensions.TensorMultiplicativity
public import MTC.Fusion.SpectralIntegral
public import MTC.Modular.Classification
public import MTC.Modular.SMatrix
public import MTC.Modular.SAdditivity

/-!
# Categorical partial traces, Verlinde identities, and Galois symmetry.
-/

@[expose] public noncomputable section

section
/-!
# Galois action from Verlinde's equations

The classification and complex-automorphism action follow from the S-square,
global nonvanishing, and Verlinde equations.
-/
open scoped BigOperators
open PropertyF.Ground.Dimensions

namespace PropertyF.Ground.Modular

/-- Verlinde's character equations give a fusion expansion for S-entry products. -/
theorem fusion_character_product {ι K : Type*} [Fintype ι] [Field K]
    {N : FusionRules ι} {S : Matrix ι ι K} {d : ι → K}
    (hsym : ∀ x y, S x y = S y x) (hd : ∀ z, d z ≠ 0)
    (hVerlinde : HasVerlindeFormula N S d) (x y z : ι) :
    S x z * S z y = ∑ k, (N.coeff x y k : K) * (d z * S k z) := by
  have h := hVerlinde x y z
  simp_rw [← mul_div_assoc, ← Finset.sum_div] at h
  field_simp [hd z] at h
  simpa only [hsym z y, Finset.sum_mul, Finset.mul_sum, mul_left_comm, mul_comm, mul_assoc] using h

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
    (hsq : HasSSquare S dual D) (hVerlinde : HasVerlindeFormula N S d) :
    ∃ act : (ℂ ≃+* ℂ) →* Equiv.Perm ι, IsGaloisColumnAction S d act :=
  let columns : ι → Character N := fun j => {
    value := fun i => S i j / d j
    unit_eq := by rw [hsym, hunit, div_self (hd j)]
    mul_eq := fun i k => hVerlinde i k j }
  let e : ι ≃ Character N := Equiv.ofBijective columns
    (characters_bijective N columns (normalized_columns_linearIndependent hd hD hsym hsq))
  ⟨Character.galoisLabel e, fun σ i j ↦ (Character.galoisLabel_character e σ j i).symm⟩

end

section
variable {ι K : Type*} [Fintype ι] [DecidableEq ι] [CommSemiring K]
variable {S : Matrix ι ι K} {dual : ι → ι} {d : ι → K} {D : K}

/-- A Galois image of the dimension column determines a diagonal entry of S squared. -/
theorem galois_unit_column_square
    (hglobal : D = ∑ x, d x ^ 2) (hsym : ∀ x y, S x y = S y x)
    (hsq : HasSSquare S dual D) (σ : K ≃+* K) (y : ι)
    (hcol : ∀ x, S x y = d y * σ (d x)) : d y ^ 2 * σ D = if y = dual y then D else 0 := by
  calc
    d y ^ 2 * σ D = ∑ x, (d y * σ (d x)) ^ 2 := by
      simp only [hglobal, map_sum, Finset.mul_sum, map_pow, mul_pow]
    _ = ∑ x, S y x * S x y := by
      simp only [hsym y, hcol, pow_two]
    _ = _ := hsq y y

end

section
variable {ι K : Type*} [Fintype ι] [DecidableEq ι] [Field K] {u : ι}
variable {S : Matrix ι ι K} {dual : ι → ι} {d : ι → K} {D : K}
variable (hd : ∀ y, d y ≠ 0) (hD : D ≠ 0)
include hd hD

/-- Proposition 2.1 from the numerical S identities and the character equation,
with no modular-data hypothesis bundle. -/
theorem galois_unit_properties (hu : d u = 1) (hglobal : D = ∑ x, d x ^ 2)
    (hsym : ∀ x y, S x y = S y x) (hunit : ∀ x, S x u = d x) (hsq : HasSSquare S dual D)
    (σ : K ≃+* K) (y : ι) (hchar : ∀ x, σ (S x u / d u) = S x y / d y) :
    (∀ x, S x y = d y * σ (d x)) ∧ y = dual y ∧ σ D = D / d y ^ 2 := by
  have hcol (x : ι) : S x y = d y * σ (d x) :=
    ((div_eq_iff (hd y)).mp (by simpa only [hunit, hu, div_one] using (hchar x).symm)).trans
      (mul_comm _ _)
  have hsquare := galois_unit_column_square hglobal hsym hsq σ y hcol
  have hself : y = dual y := Classical.byContradiction fun hn ↦
    mul_ne_zero (pow_ne_zero 2 (hd y)) (show σ D ≠ 0 from by simpa using σ.injective.ne hD)
      (by simpa only [ite_eq_right hn] using hsquare)
  exact ⟨hcol, hself, (eq_div_iff (pow_ne_zero 2 (hd y))).mpr (by
    simpa only [mul_comm, ite_eq_left hself] using hsquare)⟩

end

end PropertyF.Ground.Modular
end

section
/-!
# Partial traces of double braidings

Iterated pivotal trace and Schur's lemma give the normalized S entry as the
scalar partial trace on a simple surviving strand. The Hopf-link product follows
from the composition law for these partial traces.
-/
open CategoryTheory CategoryTheory.MonoidalCategory
open PropertyF.Ground.Dimensions PropertyF.Ground.Calculus

namespace PropertyF.Ground.Modular
universe v u

/-- The partial trace of monodromy, leaving the first strand open. -/
abbrev partialMonodromy {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
    [RightRigidCategory C]
    (p : PivotalStructure (C := C)) (X Y : C) : End X :=
  rightPartialTrace p (End.of (doubleBraiding X Y))

/-- Closing one strand of a double braiding gives the normalized S scalar. -/
theorem partialTrace_doubleBraiding_simple (D : Ground.BraidedFusionCategory.{v,u})
    (p : PivotalStructure (C := D.Obj)) (k : Fin (rank D)) (X : D.Obj) :
    partialMonodromy p (simples D k) X =
      (Ground.unitScalar D (SEntry p (simples D k) X) / simpleDimension D p k) • 1 :=
  letI : Simple (simples D k) := simples_simple D k
  letI : FiniteDimensional ℂ (simples D k ⟶ simples D k) := Ground.IsFusionCategory.hom_finite _ _
  by
    rw [Ground.unitScalar_eq_equiv]
    exact rightPartialTrace_simple p (Ground.unitScalarEquiv D) _ (simpleDimension_ne_zero D p k)

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
    SEntry_symmetric p (simples D k) (simples D j), categoricalS,
    ← Ground.unitScalar_eq_equiv] using hv

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
  by simpa only [simpleDimension, ← Ground.unitScalar_eq_equiv, Dimensions.pivotalDimension] using
    Dimensions.pivotalDimension_unitIndex C p

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
  simp [doubleBraiding, braiding_tensor_right_hom, braiding_tensor_left_hom,
    whiskerLeft_comp, Category.assoc]

end Braiding
section Trace
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
variable (p : PivotalStructure (C := C))

/-- Partial trace is natural for morphisms on the surviving strand. -/
theorem rightPartialTrace_natural {A B Y : C}
    (f : A ⟶ B) (g : B ⟶ A) (t : End (B ⊗ Y)) :
    rightPartialTrace p (End.of ((f ▷ Y) ≫ t.asHom ≫ (g ▷ Y))) =
      End.of (f ≫ (rightPartialTrace p t).asHom ≫ g) :=
  End.ext (by
    simp only [rightPartialTrace,
      comp_whiskerRight, Category.assoc]
    rw [← associator_inv_naturality_left_assoc, whisker_exchange_assoc,
      ← rightUnitor_inv_naturality_assoc]
    rw [associator_naturality_left_assoc, ← whisker_exchange_assoc,
      ← whisker_exchange_assoc, rightUnitor_naturality])

variable {k : Type*} [Field k] [IsAlgClosed k] [Preadditive C] [Linear k C]
  [MonoidalPreadditive C] [MonoidalLinear k C] [CategoryTheory.Limits.HasKernels C]

/-- When the surviving object is simple with nonzero dimension, successive
partial traces agree with tracing the combined tensor factor. -/
theorem rightPartialTrace_nested_simple {scalar : End (𝟙_ C) ≃ₐ[k] k} {Z X Y : C}
    [Simple Z] [FiniteDimensional k (Z ⟶ Z)]
    (hd : scalar (p.rightTrace (𝟙 Z)) ≠ 0) (f : End (Z ⊗ (X ⊗ Y))) :
    rightPartialTrace p f = rightPartialTrace p (rightPartialTrace p ((α_ Z X Y).symm.conj f)) :=
  let g := (α_ Z X Y).symm.conj f
  have hc : p.rightTrace g.asHom = p.rightTrace f.asHom := by
    simpa [g, Iso.conj_apply_asHom, Category.assoc] using
      p.rightTrace_cyclic ((α_ Z X Y).hom ≫ f.asHom) (α_ Z X Y).inv
  (rightPartialTrace_simple p scalar f hd).trans (by
    simpa only [Calculus.scalarTrace, rightTrace_partialTrace p g, hc] using
      (rightPartialTrace_simple p scalar (rightPartialTrace p g) hd).symm)


end Trace

section MonodromyTrace
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [RightRigidCategory C]

/-- Partial tracing a tensor-product monodromy leaves a conjugated partial monodromy. -/
theorem partialTrace_doubleBraiding_factor (p : PivotalStructure (C := C)) (Z X Y : C) :
    rightPartialTrace p ((α_ Z X Y).symm.conj (End.of (doubleBraiding Z (X ⊗ Y)))) =
    End.of ((β_ Z X).hom ≫ (X ◁ (partialMonodromy p Z Y).asHom) ≫ (β_ X Z).hom) :=
  let t : End ((X ⊗ Z) ⊗ Y) := End.of ((α_ X Z Y).hom ≫
    (X ◁ doubleBraiding Z Y) ≫ (α_ X Z Y).inv)
  have hfactor : (α_ Z X Y).symm.conj (End.of (doubleBraiding Z (X ⊗ Y))) =
      End.of (((β_ Z X).hom ▷ Y) ≫ t.asHom ≫ ((β_ X Z).hom ▷ Y)) := End.ext (by
    simpa [t, Iso.conj_apply_asHom, Category.assoc] using doubleBraiding_tensor_factorization Z X Y)
  by rw [hfactor, rightPartialTrace_natural, Calculus.rightPartialTrace_whiskerLeft]

variable {k : Type*} [CommSemiring k] [Preadditive C] [Linear k C]
  [MonoidalPreadditive C] [MonoidalLinear k C]

/-- A scalar partial monodromy factors out of the tensor-product partial trace. -/
theorem partialTrace_doubleBraiding_scalar (p : PivotalStructure (C := C)) {Z Y : C} (X : C) {s : k}
    (hs : partialMonodromy p Z Y = s • 1) :
    rightPartialTrace p ((α_ Z X Y).symm.conj (End.of (doubleBraiding Z (X ⊗ Y)))) =
    s • End.of (doubleBraiding Z X) := by
  rw [partialTrace_doubleBraiding_factor, hs]
  exact End.ext (by simp [doubleBraiding])

end MonodromyTrace

/-- Double-braiding partial traces multiply on a simple surviving strand. -/
theorem partialTrace_doubleBraiding_tensor (D : BraidedFusionCategory.{v,u})
    (p : PivotalStructure (C := D.Obj)) : HasMultiplicativePartialTrace D p := by
  intro i j k
  let : Simple (simples D k) := simples_simple D k
  let : FiniteDimensional ℂ (simples D k ⟶ simples D k) := Ground.IsFusionCategory.hom_finite _ _
  let f := End.of (doubleBraiding (simples D k) (simples D i ⊗ simples D j))
  have hs := partialTrace_doubleBraiding_simple D p k (simples D j)
  change rightPartialTrace p f = _
  rw [rightPartialTrace_nested_simple p (simpleDimension_ne_zero D p k) f,
    partialTrace_doubleBraiding_scalar p (simples D i) hs, rightPartialTrace_smul, hs]
  simp [partialMonodromy]


/-- The normalized S columns satisfy the Verlinde fusion-character equations. -/
theorem categoricalS_verlinde (D : Ground.BraidedFusionCategory.{v,u})
    (p : PivotalStructure (C := D.Obj)) :
    HasVerlindeFormula ⟨unitIndex D, fusionCoeff D⟩ (categoricalS D p) (simpleDimension D p) :=
  categoricalS_verlinde_of_hopf_product D p
    (hopf_product_of_partialTrace_composition D p (partialTrace_doubleBraiding_tensor D p))

end PropertyF.Ground.Modular
end
