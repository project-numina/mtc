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

/-- The full action on normalized columns follows from S-square and the
Verlinde character equations, without an assumed character classification. -/
theorem exists_galoisLabel_of_verlinde {ι : Type*} [Fintype ι] [DecidableEq ι]
    (N : FusionRules ι) (S : Matrix ι ι ℂ) (dual : ι → ι)
    (d : ι → ℂ) (D : ℂ) (hd : ∀ y, d y ≠ 0) (hD : D ≠ 0)
    (hsym : ∀ x y, S x y = S y x) (hunit : ∀ x, S x N.unit = d x)
    (hsq : ∀ x y, ∑ z, S x z * S z y = if x = dual y then D else 0)
    (hVerlinde : ∀ i j y, (S i y / d y) * (S j y / d y) =
      ∑ k, (N.coeff i j k : ℂ) * (S k y / d y)) :
    ∃ act : (ℂ ≃+* ℂ) →* Equiv.Perm ι, ∀ (σ : ℂ ≃+* ℂ) i j,
      σ (S i j / d j) = S i (act σ j) / d (act σ j) := by
  let columns : ι → Character N := fun j => {
    value := fun i => S i j / d j
    unit_eq := by rw [hsym, hunit]; exact div_self (hd j)
    mul_eq := fun i k => hVerlinde i k j }
  have hlin : LinearIndependent ℂ (fun j => (columns j).value) :=
    normalized_columns_linearIndependent S dual d D hd hD hsym hsq
  let e : ι ≃ Character N := Equiv.ofBijective columns (characters_bijective N columns hlin)
  refine ⟨Character.galoisLabel e, ?_⟩
  intro σ i j
  exact (Character.galoisLabel_character e σ j i).symm

/-- Once S-square and Verlinde are proved categorically, the corresponding
normalized S-columns carry the genuine action of all complex automorphisms. -/
theorem categoricalS_galois_action (C : Ground.BraidedFusionCategory)
    (p : PivotalStructure (C := C.Obj)) (dual : Fin (rank C) → Fin (rank C))
    (hD : globalDimension C ≠ 0)
    (hsq : ∀ x y, ∑ z, categoricalS C p x z * categoricalS C p z y =
      if x = dual y then globalDimension C else 0)
    (hVerlinde : ∀ i j y,
      (categoricalS C p i y / simpleDimension C p y) *
        (categoricalS C p j y / simpleDimension C p y) =
      ∑ k, (fusionCoeff C i j k : ℂ) * (categoricalS C p k y / simpleDimension C p y)) :
    ∃ act : (ℂ ≃+* ℂ) →* Equiv.Perm (Fin (rank C)), ∀ (σ : ℂ ≃+* ℂ) i j,
      σ (categoricalS C p i j / simpleDimension C p j) =
        categoricalS C p i (act σ j) / simpleDimension C p (act σ j) := by
  let N : FusionRules (Fin (rank C)) := ⟨unitIndex C, fusionCoeff C⟩
  exact exists_galoisLabel_of_verlinde N (categoricalS C p) dual (simpleDimension C p)
    (globalDimension C) (simpleDimension_ne_zero C p) hD (categoricalS_symmetric C p) (categoricalS_unit C p) hsq hVerlinde


/-- Proposition 2.1 from the numerical S identities and the character equation,
with no modular-data hypothesis bundle. -/
theorem galois_unit_properties {ι : Type*} [Fintype ι] [DecidableEq ι]
    (u : ι) (S : Matrix ι ι ℂ) (dual : ι → ι) (d : ι → ℂ) (D : ℂ)
    (hd : ∀ y, d y ≠ 0) (hD : D ≠ 0) (hu : d u = 1)
    (hglobal : D = ∑ x, d x ^ 2) (hsym : ∀ x y, S x y = S y x)
    (hunit : ∀ x, S x u = d x)
    (hsq : ∀ x y, ∑ z, S x z * S z y = if x = dual y then D else 0)
    (σ : ℂ ≃+* ℂ) (y : ι)
    (hchar : ∀ x, σ (S x u / d u) = S x y / d y) :
    (∀ x, S x y = d y * σ (d x)) ∧ y = dual y ∧ σ D = D / d y ^ 2 := by
  have hcol (x : ι) : S x y = d y * σ (d x) := by
    have hh := hchar x
    rw [hunit, hu, div_one] at hh
    exact (div_eq_iff (hd y)).mp hh.symm |>.trans (mul_comm _ _)
  have hsquare : d y ^ 2 * σ D = if y = dual y then D else 0 := by
    calc
      d y ^ 2 * σ D = ∑ x, (d y * σ (d x)) ^ 2 := by
        rw [hglobal, map_sum, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x _
        rw [map_pow, mul_pow]
      _ = ∑ x, S x y ^ 2 := by
        apply Finset.sum_congr rfl
        intro x _
        rw [hcol]
      _ = ∑ x, S y x * S x y := by
        apply Finset.sum_congr rfl
        intro x _
        rw [hsym y x, pow_two]
      _ = _ := hsq y y
  have hself : y = dual y := by
    by_contra hn
    rw [ite_eq_right hn] at hsquare
    exact mul_ne_zero (pow_ne_zero 2 (hd y))
      (by simpa using σ.injective.ne hD) hsquare
  refine ⟨hcol, hself, ?_⟩
  apply (eq_div_iff (pow_ne_zero 2 (hd y))).mpr
  rw [mul_comm, hsquare, ite_eq_left hself]

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

/-- Closing one strand of a double braiding gives the normalized S scalar. -/
theorem partialTrace_doubleBraiding_simple (D : Ground.BraidedFusionCategory.{v,u})
    (p : PivotalStructure (C := D.Obj)) (k : Fin (rank D)) (X : D.Obj) :
    rightPartialTrace p (simples D k) X (End.of (doubleBraiding (simples D k) X)) =
      (Ground.unitScalarEquiv D (SEntry p (simples D k) X) / simpleDimension D p k) • 1 := by
  let _ : Simple (simples D k) := simples_simple D k
  let _ : FiniteDimensional ℂ (simples D k ⟶ simples D k) := Ground.IsFusionCategory.hom_finite _ _
  exact rightPartialTrace_simple_of_trace_compatibility (simples D k) X p
    (Ground.unitScalarEquiv D) (End.of (doubleBraiding (simples D k) X))
    (simpleDimension_ne_zero D p k)
    (rightTrace_partialTrace p (simples D k) X (End.of (doubleBraiding (simples D k) X)))

/-- The product formula follows from the precise residual partial-trace
composition law for double braidings. -/
theorem hopf_product_of_partialTrace_composition (D : Ground.BraidedFusionCategory.{v,u})
    (p : PivotalStructure (C := D.Obj))
    (hcomp : ∀ i j k : Fin (rank D),
      rightPartialTrace p (simples D k) (simples D i ⊗ simples D j)
          (End.of (doubleBraiding (simples D k) (simples D i ⊗ simples D j))) =
      rightPartialTrace p (simples D k) (simples D i)
          (End.of (doubleBraiding (simples D k) (simples D i))) *
      rightPartialTrace p (simples D k) (simples D j)
          (End.of (doubleBraiding (simples D k) (simples D j)))) :
    ∀ i j k : Fin (rank D),
      Ground.unitScalarEquiv D (SEntry p (simples D i ⊗ simples D j) (simples D k)) *
        simpleDimension D p k = categoricalS D p i k * categoricalS D p j k := by
  intro i j k
  let _ : Simple (simples D k) := simples_simple D k
  have honene : (1 : End (simples D k)) ≠ 0 := by
    intro h
    have hh := congrArg End.asHom h
    exact id_nonzero (simples D k) (by simpa using hh)
  have h := hcomp i j k
  rw [partialTrace_doubleBraiding_simple, partialTrace_doubleBraiding_simple,
    partialTrace_doubleBraiding_simple, smul_mul_smul, one_mul] at h
  have hv := smul_left_injective ℂ honene h
  have hd := simpleDimension_ne_zero D p k
  have hval : Ground.unitScalarEquiv D (SEntry p (simples D k) (simples D i ⊗ simples D j)) *
      simpleDimension D p k =
      Ground.unitScalarEquiv D (SEntry p (simples D k) (simples D i)) *
        Ground.unitScalarEquiv D (SEntry p (simples D k) (simples D j)) := by
    calc
      _ = (Ground.unitScalarEquiv D (SEntry p (simples D k) (simples D i ⊗ simples D j)) /
          simpleDimension D p k) * simpleDimension D p k ^ 2 := by field_simp
      _ = ((Ground.unitScalarEquiv D (SEntry p (simples D k) (simples D i)) /
          simpleDimension D p k) * (Ground.unitScalarEquiv D (SEntry p (simples D k) (simples D j)) /
          simpleDimension D p k)) * simpleDimension D p k ^ 2 := by rw [hv]
      _ = _ := by field_simp
  simpa only [SEntry_symmetric p (simples D k) (simples D i ⊗ simples D j),
    SEntry_symmetric p (simples D k) (simples D i),
    SEntry_symmetric p (simples D k) (simples D j), categoricalS] using hval

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
    (p : PivotalStructure (C := C.Obj)) : simpleDimension C p (unitIndex C) = 1 := by
  obtain ⟨e⟩ := unitIndex_iso C
  unfold simpleDimension
  rw [p.rightTrace_id_iso e, Dimensions.rightTrace_unit, map_one]

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
  rw [hfactor, rightPartialTrace_natural, Calculus.rightPartialTrace_whiskerLeft, hs]
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

end PropertyF.Ground.Modular
end
