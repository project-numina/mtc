module
public import PropertyF.Ground.Fusion.Simples
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.CategoryTheory.Monoidal.Preadditive

/-! Hom-space multiplicities of finite direct sums. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open scoped BigOperators

namespace PropertyF.Ground
universe v u
attribute [local instance] Abelian.hasFiniteBiproducts IsFusionCategory.hom_finite
section
variable {k : Type*} [Field k] [IsAlgClosed k]
  {C : Type u} [Category.{v} C] [Preadditive C] [Linear k C]

/-- Schur's lemma identifies the scalar algebra with the endomorphism algebra
of a finite-dimensional simple object. -/
theorem simple_algebraMap_bijective [HasKernels C] (X : C) [Simple X]
    [FiniteDimensional k (X ⟶ X)] : Function.Bijective (algebraMap k (End X)) :=
  ⟨RingHom.injective _, fun a ↦ (endomorphism_simple_eq_smul_id k a.asHom).imp
    fun _ hz ↦ End.ext (by simpa [Algebra.algebraMap_eq_smul_one] using hz)⟩

/-- The endomorphism algebra of a finite-dimensional simple object is the scalar field. -/
def simpleEndScalar [HasKernels C] (X : C) [Simple X]
    [FiniteDimensional k (X ⟶ X)] : End X ≃ₐ[k] k :=
  (AlgEquiv.ofBijective (Algebra.ofId k (End X)) (simple_algebraMap_bijective X)).symm

end

section
variable {k : Type*} [CommSemiring k] {C : Type u} [Category.{v} C] [Preadditive C] [Linear k C]
  {ι : Type*}

/-- The Hom space into a finite biproduct is the product of the Hom spaces. -/
def homBiproductLinearEquiv
    (X : C) (V : ι → C) [HasBiproduct V] : (X ⟶ ⨁ V) ≃ₗ[k] (∀ i, X ⟶ V i) where
  toFun f i := f ≫ biproduct.π V i
  invFun f := biproduct.lift f
  left_inv f := biproduct.hom_ext _ _ fun i ↦ by simp
  right_inv f := funext fun i ↦ by simp
  map_add' f g := funext fun i ↦ by simp
  map_smul' z f := funext fun i ↦ by simp

/-- The Hom space out of a finite biproduct is the product of the Hom spaces. -/
def biproductHomLinearEquiv
    (V : ι → C) [HasBiproduct V] (X : C) : (⨁ V ⟶ X) ≃ₗ[k] (∀ i, V i ⟶ X) where
  toFun f i := biproduct.ι V i ≫ f
  invFun f := biproduct.desc f
  left_inv f := biproduct.hom_ext' _ _ fun i ↦ by simp
  right_inv f := funext fun i ↦ by simp
  map_add' f g := funext fun i ↦ by simp
  map_smul' z f := funext fun i ↦ by simp

end

section
variable {k : Type*} [Field k] {C : Type u} [Category.{v} C] [Preadditive C] [Linear k C]
  {ι : Type*} [Fintype ι]
  {X : C} {V : ι → C} [HasBiproduct V]

theorem finrank_hom_biproduct [∀ i, FiniteDimensional k (X ⟶ V i)] :
    Module.finrank k (X ⟶ ⨁ V) = ∑ i, Module.finrank k (X ⟶ V i) :=
  by rw [(homBiproductLinearEquiv (k := k) X V).finrank_eq, Module.finrank_pi_fintype]

theorem finrank_biproduct_hom [∀ i, FiniteDimensional k (V i ⟶ X)] :
    Module.finrank k (⨁ V ⟶ X) = ∑ i, Module.finrank k (V i ⟶ X) :=
  by rw [(biproductHomLinearEquiv (k := k) V X).finrank_eq, Module.finrank_pi_fintype]

end

variable (D : BraidedFusionCategory.{v,u})

/-- The multiplicity of a chosen simple object in an object. -/
abbrev simpleMultiplicity (i : Fin (rank D)) (X : D.Obj) : ℕ :=
  Module.finrank ℂ (simples D i ⟶ X)

variable {D} in
/-- A chosen simple's Hom dimension counts its copies in a decomposition. -/
theorem finrank_simple_of_decomposition
    {X : D.Obj} (m : Fin (rank D) → ℕ)
    (e : X ≅ ⨁ (fun p : Σ i, Fin (m i) => simples D p.1)) (i : Fin (rank D)) :
    simpleMultiplicity D i X = m i := by
  dsimp only [simpleMultiplicity]
  rw [(CategoryTheory.Linear.homCongr ℂ (Iso.refl _) e).finrank_eq,
    finrank_hom_biproduct, Fintype.sum_sigma]
  simp [finrank_simples_hom]

/-- Every object decomposes with the canonical Hom-space multiplicities. -/
theorem exists_canonical_decomposition (X : D.Obj) :
    Nonempty (X ≅ ⨁ (fun p : Σ i : Fin (rank D),
      Fin (simpleMultiplicity D i X) => simples D p.1)) := by
  obtain ⟨m, ⟨e⟩⟩ := simples_decompose D X
  cases (funext (finrank_simple_of_decomposition m e)).symm
  exact ⟨e⟩

/-- Hom dimensions to and from a simple coincide in a semisimple category. -/
theorem finrank_to_simple_eq_from_simple {E : Type u} [Category.{v} E]
    [MonoidalCategory E] [BraidedCategory E] [Abelian E] [Linear ℂ E]
    [RigidCategory E] [MonoidalPreadditive E] [MonoidalLinear ℂ E] [IsFusionCategory E]
    (X S : E) [Simple S] : Module.finrank ℂ (X ⟶ S) = Module.finrank ℂ (S ⟶ X) := by
  classical
  obtain ⟨n, T, hsimple, _, hdecomp⟩ := IsFusionCategory.finite_semisimple (C := E)
  obtain ⟨m, ⟨e⟩⟩ := hdecomp X
  let V : (Σ i, Fin (m i)) → E := fun p ↦ T p.1
  let : ∀ p, Simple (V p) := fun p ↦ hsimple p.1
  simp only [(CategoryTheory.Linear.homCongr ℂ e (Iso.refl S)).finrank_eq,
    (CategoryTheory.Linear.homCongr ℂ (Iso.refl S) e).finrank_eq,
    finrank_biproduct_hom, finrank_hom_biproduct,
    CategoryTheory.finrank_hom_simple_simple ℂ, Iso.nonempty_iso_symm]

/-- A nonzero object decomposed over a finite family has a nonzero multiplicity. -/
theorem exists_positive_multiplicity {k : Type*} [Field k]
    {E : Type u} [Category.{v} E] [Preadditive E] [Linear k E] [HasFiniteBiproducts E]
    {ι : Type} [Fintype ι] {T : ι → E} {X : E}
    (hdecomp : HasBiproductDecomposition T X)
    (hfinite : ∀ i, FiniteDimensional k (T i ⟶ X)) (hX : ¬ IsZero X) :
    ∃ i, 0 < Module.finrank k (T i ⟶ X) := by
  obtain ⟨i, s, t, hs, ht⟩ := exists_retract_of_biproduct_decomposition hdecomp (by
    simpa [IsZero.iff_id_eq_zero] using hX)
  let : FiniteDimensional k (T i ⟶ X) := hfinite i
  exact ⟨i, Module.finrank_pos_iff_exists_ne_zero.mpr
    ⟨t, fun ht0 ↦ hs (by rw [← Category.comp_id s, ← ht, ht0, zero_comp, comp_zero])⟩⟩

variable {D} in
/-- Tensoring an object on the left acts on simple multiplicities by its
integer fusion matrix. -/
theorem tensor_multiplicity (X Y : D.Obj) (k : Fin (rank D)) :
    simpleMultiplicity D k (X ⊗ Y) =
      ∑ j, simpleMultiplicity D j Y *
        simpleMultiplicity D k (X ⊗ simples D j) := by
  obtain ⟨e⟩ := exists_canonical_decomposition D Y
  dsimp only [simpleMultiplicity]
  rw [(CategoryTheory.Linear.homCongr ℂ (Iso.refl _)
      ((Iso.refl X ⊗ᵢ e) ≪≫ CategoryTheory.leftDistributor X _)).finrank_eq,
    finrank_hom_biproduct, Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  change (∑ _ : Fin (simpleMultiplicity D j Y), simpleMultiplicity D k (X ⊗ simples D j)) = _
  simp

/-- Fusion coefficients are the actual Hom-space dimensions. -/
def fusionCoeff (i j k : Fin (rank D)) : ℕ :=
  Module.finrank ℂ (simples D k ⟶ simples D i ⊗ simples D j)

/-- The representative of the tensor unit. -/
def unitIndex : Fin (rank D) :=
  Classical.choose (exists_unit_iso D)

theorem unitIndex_iso :
    Nonempty (simples D (unitIndex D) ≅ 𝟙_ D.Obj) :=
  Classical.choose_spec (exists_unit_iso D)

theorem fusionCoeff_unit (j k : Fin (rank D)) :
    fusionCoeff D (unitIndex D) j k = if k = j then 1 else 0 :=
  (unitIndex_iso D).elim fun e ↦
    ((Linear.homCongr ℂ (Iso.refl _) ((e ⊗ᵢ Iso.refl _) ≪≫ λ_ _)).finrank_eq).trans
      (finrank_simples_hom D k j)

theorem fusionCoeff_comm (i j k : Fin (rank D)) :
    fusionCoeff D i j k = fusionCoeff D j i k :=
  (CategoryTheory.Linear.homCongr ℂ (Iso.refl _) (β_ (simples D i) (simples D j))).finrank_eq

local notation "N" => fusionCoeff D

variable {D} in
/-- Associativity of fusion coefficients, derived from associativity of
tensor products and finite semisimplicity. -/
theorem fusionCoeff_assoc (i j k l : Fin (rank D)) :
    ∑ r, N j k r * N i r l = ∑ r, N i j r * N r k l := by
  have h := (CategoryTheory.Linear.homCongr ℂ (Iso.refl (simples D l))
    ((α_ (simples D i) (simples D j) (simples D k)).symm ≪≫
      β_ (simples D i ⊗ simples D j) (simples D k))).finrank_eq
  change simpleMultiplicity D l (simples D i ⊗ (simples D j ⊗ simples D k)) =
    simpleMultiplicity D l (simples D k ⊗ (simples D i ⊗ simples D j)) at h
  rw [tensor_multiplicity (simples D i) (simples D j ⊗ simples D k) l,
    tensor_multiplicity (simples D k) (simples D i ⊗ simples D j) l] at h
  change (∑ r, fusionCoeff D j k r * fusionCoeff D i r l) =
    ∑ r, fusionCoeff D i j r * fusionCoeff D k r l at h
  simpa only [fusionCoeff_comm D k] using h

end PropertyF.Ground
