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
attribute [local instance] Abelian.hasFiniteBiproducts
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]

/-- Schur's lemma identifies the scalar algebra with the endomorphism algebra
of a finite-dimensional simple object. -/
theorem simple_algebraMap_bijective [HasKernels C] (X : C) [Simple X]
    [FiniteDimensional ℂ (X ⟶ X)] : Function.Bijective (algebraMap ℂ (End X)) := by
  refine ⟨RingHom.injective _, fun a ↦ ?_⟩
  obtain ⟨z, hz⟩ := endomorphism_simple_eq_smul_id ℂ a.asHom
  exact ⟨z, End.ext (by simpa [Algebra.algebraMap_eq_smul_one] using hz)⟩

/-- The endomorphism algebra of a finite-dimensional simple object is the scalar field. -/
def simpleEndScalar [HasKernels C] (X : C) [Simple X]
    [FiniteDimensional ℂ (X ⟶ X)] : End X ≃ₐ[ℂ] ℂ :=
  (AlgEquiv.ofBijective (Algebra.ofId ℂ (End X)) (simple_algebraMap_bijective X)).symm

/-- The Hom space into a finite biproduct is the product of the Hom spaces. -/
def homBiproductLinearEquiv {ι : Type*} [Fintype ι] [HasFiniteBiproducts C]
    (X : C) (V : ι → C) : (X ⟶ ⨁ V) ≃ₗ[ℂ] (∀ i, X ⟶ V i) where
  toFun f i := f ≫ biproduct.π V i
  invFun f := biproduct.lift f
  left_inv f := by
    apply biproduct.hom_ext
    intro i
    simp
  right_inv f := by
    funext i
    simp
  map_add' f g := by
    funext i
    simp
  map_smul' z f := by
    funext i
    simp

/-- The Hom space out of a finite biproduct is the product of the Hom spaces. -/
def biproductHomLinearEquiv {ι : Type*} [Fintype ι] [HasFiniteBiproducts C]
    (V : ι → C) (X : C) : (⨁ V ⟶ X) ≃ₗ[ℂ] (∀ i, V i ⟶ X) where
  toFun f i := biproduct.ι V i ≫ f
  invFun f := biproduct.desc f
  left_inv f := by
    apply biproduct.hom_ext'
    intro i
    simp
  right_inv f := by
    funext i
    simp
  map_add' f g := by
    funext i
    simp
  map_smul' z f := by
    funext i
    simp

theorem finrank_hom_biproduct {ι : Type*} [Fintype ι] [HasFiniteBiproducts C]
    (X : C) (V : ι → C) [∀ i, FiniteDimensional ℂ (X ⟶ V i)] :
    Module.finrank ℂ (X ⟶ ⨁ V) = ∑ i, Module.finrank ℂ (X ⟶ V i) :=
  by rw [(homBiproductLinearEquiv X V).finrank_eq, Module.finrank_pi_fintype]

theorem finrank_biproduct_hom {ι : Type*} [Fintype ι] [HasFiniteBiproducts C]
    (V : ι → C) (X : C) [∀ i, FiniteDimensional ℂ (V i ⟶ X)] :
    Module.finrank ℂ (⨁ V ⟶ X) = ∑ i, Module.finrank ℂ (V i ⟶ X) :=
  by rw [(biproductHomLinearEquiv V X).finrank_eq, Module.finrank_pi_fintype]

/-- A chosen simple's Hom dimension counts its copies in a decomposition. -/
theorem finrank_simple_of_decomposition (D : BraidedFusionCategory.{v,u})
    {X : D.Obj} (m : Fin (rank D) → ℕ)
    (e : X ≅ ⨁ (fun p : Σ i, Fin (m i) => simples D p.1)) (i : Fin (rank D)) :
    Module.finrank ℂ (simples D i ⟶ X) = m i := by
  classical
  let : ∀ Y Z : D.Obj, FiniteDimensional ℂ (Y ⟶ Z) := IsFusionCategory.hom_finite
  calc
    Module.finrank ℂ (simples D i ⟶ X) =
        Module.finrank ℂ (simples D i ⟶ ⨁ (fun p : Σ j, Fin (m j) => simples D p.1)) :=
      (CategoryTheory.Linear.homCongr ℂ (Iso.refl _) e).finrank_eq
    _ = ∑ p : Σ j, Fin (m j), Module.finrank ℂ (simples D i ⟶ simples D p.1) :=
      finrank_hom_biproduct _ _
    _ = m i := by
      rw [Fintype.sum_sigma]
      simp [finrank_simples_hom]

/-- Every object decomposes with the canonical Hom-space multiplicities. -/
theorem exists_canonical_decomposition (D : BraidedFusionCategory.{v,u}) (X : D.Obj) :
    Nonempty (X ≅ ⨁ (fun p : Σ i : Fin (rank D),
      Fin (Module.finrank ℂ (simples D i ⟶ X)) => simples D p.1)) := by
  obtain ⟨m, ⟨e⟩⟩ := simples_decompose D X
  cases (funext (finrank_simple_of_decomposition D m e)).symm
  exact ⟨e⟩

/-- Hom dimensions to and from a simple coincide in a semisimple category. -/
theorem finrank_to_simple_eq_from_simple (D : BraidedFusionCategory.{v,u})
    (X : D.Obj) (i : Fin (rank D)) :
    Module.finrank ℂ (X ⟶ simples D i) = Module.finrank ℂ (simples D i ⟶ X) := by
  classical
  let m : Fin (rank D) → ℕ := fun j => Module.finrank ℂ (simples D j ⟶ X)
  obtain ⟨e⟩ := exists_canonical_decomposition D X
  let : ∀ A B : D.Obj, FiniteDimensional ℂ (A ⟶ B) := IsFusionCategory.hom_finite
  calc
    _ = Module.finrank ℂ (⨁ (fun p : Σ j, Fin (m j) => simples D p.1) ⟶ simples D i) :=
      (CategoryTheory.Linear.homCongr ℂ e (Iso.refl _)).finrank_eq
    _ = ∑ p : Σ j, Fin (m j), Module.finrank ℂ (simples D p.1 ⟶ simples D i) :=
      finrank_biproduct_hom _ _
    _ = _ := by
      rw [Fintype.sum_sigma]
      simp [finrank_simples_hom, m]

/-- Tensoring an object on the left acts on simple multiplicities by its
integer fusion matrix. -/
theorem tensor_multiplicity (D : BraidedFusionCategory.{v,u}) (X Y : D.Obj)
    (k : Fin (rank D)) :
    Module.finrank ℂ (simples D k ⟶ X ⊗ Y) =
      ∑ j, Module.finrank ℂ (simples D j ⟶ Y) *
        Module.finrank ℂ (simples D k ⟶ X ⊗ simples D j) := by
  classical
  let m : Fin (rank D) → ℕ := fun j => Module.finrank ℂ (simples D j ⟶ Y)
  let V : (Σ j, Fin (m j)) → D.Obj := fun p => simples D p.1
  obtain ⟨e⟩ := exists_canonical_decomposition D Y
  let e' : X ⊗ Y ≅ ⨁ (fun p => X ⊗ V p) :=
    (Iso.refl X ⊗ᵢ e) ≪≫ CategoryTheory.leftDistributor X V
  let : ∀ A B : D.Obj, FiniteDimensional ℂ (A ⟶ B) := IsFusionCategory.hom_finite
  calc
    Module.finrank ℂ (simples D k ⟶ X ⊗ Y) =
        Module.finrank ℂ (simples D k ⟶ ⨁ (fun p => X ⊗ V p)) :=
      (CategoryTheory.Linear.homCongr ℂ (Iso.refl _) e').finrank_eq
    _ = ∑ p : Σ j, Fin (m j), Module.finrank ℂ (simples D k ⟶ X ⊗ V p) :=
      finrank_hom_biproduct _ _
    _ = _ := by
      rw [Fintype.sum_sigma]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      change (∑ _ : Fin (m j), Module.finrank ℂ (simples D k ⟶ X ⊗ simples D j)) = _
      simp [m]

/-- Fusion coefficients are the actual Hom-space dimensions. -/
def fusionCoeff (D : BraidedFusionCategory.{v,u}) (i j k : Fin (rank D)) : ℕ :=
  Module.finrank ℂ (simples D k ⟶ simples D i ⊗ simples D j)

/-- The representative of the tensor unit. -/
def unitIndex (D : BraidedFusionCategory.{v,u}) : Fin (rank D) :=
  Classical.choose (exists_unit_iso D)

theorem unitIndex_iso (D : BraidedFusionCategory.{v,u}) :
    Nonempty (simples D (unitIndex D) ≅ 𝟙_ D.Obj) :=
  Classical.choose_spec (exists_unit_iso D)

theorem fusionCoeff_unit (D : BraidedFusionCategory.{v,u}) (j k : Fin (rank D)) :
    fusionCoeff D (unitIndex D) j k = if k = j then 1 else 0 :=
  (unitIndex_iso D).elim fun e ↦
    ((CategoryTheory.Linear.homCongr ℂ (Iso.refl _)
      ((e ⊗ᵢ Iso.refl (simples D j)) ≪≫ λ_ (simples D j))).finrank_eq).trans
      (finrank_simples_hom D k j)

theorem fusionCoeff_comm (D : BraidedFusionCategory.{v,u}) (i j k : Fin (rank D)) :
    fusionCoeff D i j k = fusionCoeff D j i k :=
  (CategoryTheory.Linear.homCongr ℂ (Iso.refl _) (β_ (simples D i) (simples D j))).finrank_eq

/-- Associativity of fusion coefficients, derived from associativity of
tensor products and finite semisimplicity. -/
theorem fusionCoeff_assoc (D : BraidedFusionCategory.{v,u})
    (i j k l : Fin (rank D)) :
    ∑ r, fusionCoeff D j k r * fusionCoeff D i r l =
      ∑ r, fusionCoeff D i j r * fusionCoeff D r k l := by
  classical
  calc
    _ = Module.finrank ℂ (simples D l ⟶ simples D i ⊗ (simples D j ⊗ simples D k)) := by
      simpa [fusionCoeff] using (tensor_multiplicity D (simples D i)
        (simples D j ⊗ simples D k) l).symm
    _ = Module.finrank ℂ (simples D l ⟶ simples D k ⊗ (simples D i ⊗ simples D j)) :=
      (CategoryTheory.Linear.homCongr ℂ (Iso.refl _)
        ((α_ (simples D i) (simples D j) (simples D k)).symm ≪≫
          β_ (simples D i ⊗ simples D j) (simples D k))).finrank_eq
    _ = ∑ r, fusionCoeff D i j r * fusionCoeff D k r l := by
      simpa [fusionCoeff] using tensor_multiplicity D (simples D k)
        (simples D i ⊗ simples D j) l
    _ = _ := by
      apply Finset.sum_congr rfl
      intro r _
      rw [fusionCoeff_comm D k r l]

end PropertyF.Ground
