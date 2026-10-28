module
public import PropertyF.Ground.Integrate.Arithmetic
public import PropertyF.Ground.Integrate.CharacterReality
public import PropertyF.Ground.Dimensions.DimensionCharacter
public import PropertyF.Ground.Dimensions.GlobalInequality
public import PropertyF.Ground.Modular.FusionTransport
public import PropertyF.Ground.Dimensions.IntrinsicNonzero
public import PropertyF.Ground.Fusion.Agreement
public import PropertyF.Ground.Modular.SSquare
public import PropertyF.Ground.Modular.SMatrix
public import PropertyF.Ground.Integrate.TwistedRigidity
public import PropertyF.Ground.Dimensions.PivotalTwist
public import PropertyF.Ground.Dimensions.PositiveCanonical
public import PropertyF.Ground.Calculus.TensorPowerCoherence
public import PropertyF.Ground.Centre.ProductClosure
public import PropertyF.Ground.CentreCabling.RegularSupport
public import PropertyF.Ground.Integrate.CenterBundle

section
/-! Bundle-free reduction of the target to FP invariance under conjugacy and the
paper's Galois-fixedness argument for pseudo-unitary categories. -/

@[expose] public noncomputable section
namespace PropertyF.Ground
universe v u

/-- The unit simple proves positivity, leaving only the bounded-conjugate and
centre/rigidity witness obligations. -/
theorem target_of_bounded_conjugates_and_witness
    (hConjugates : ∀ (C : BraidedFusionCategory.{v,u}), PseudoUnitary C →
      HasPropertyF C.Obj → ∀ σ : ℂ ≃+* ℂ, ∃ a : ℝ,
        0 < a ∧ a ≤ globalFPDimension C ∧
          σ (globalFPDimension C : ℂ) = (a : ℂ))
    (hWitness : ∀ (C : BraidedFusionCategory.{v,u}), PseudoUnitary C →
      HasPropertyF C.Obj → ∀ (σ : ℂ ≃+* ℂ) (a b : ℝ),
        0 < a → a < globalFPDimension C →
        σ (globalFPDimension C : ℂ) = (a : ℂ) →
        σ.symm (globalFPDimension C : ℂ) = (b : ℂ) →
        ∃ f d : ℝ, σ (f : ℂ) = (d : ℂ) ∧
          f * b = globalFPDimension C ∧ 1 ≤ f ∧ f = |d|) :
    TargetStatement.{v,u} :=
by
  intro C hPU hF
  obtain ⟨D, σ, ⟨E⟩, hD⟩ := hPU
  have hDF := Modular.conjugate_propertyF E hF
  have hfixed := galois_fixed_of_smaller_conjugate_witness (globalFPDimension D)
    (lt_of_lt_of_le zero_lt_one (one_le_globalFPDimension D))
    (hConjugates D hD hDF) (hWitness D hD hDF)
  have hInt := weaklyIntegral_of_globalFPDimension_fixed D hfixed
  rwa [Modular.conjugate_globalFPDimension E]

end PropertyF.Ground
end
end

section
/-! Extract the numerical ingredients of the paper's witness from an actual
spherical category with positive FP dimensions and invertible S matrix. -/

@[expose] public noncomputable section
open CategoryTheory
open scoped BigOperators
namespace PropertyF.Ground
universe v u

/-- The actual Galois-unit label supplies the modular dimension identity, its
self-column, a dimension at least one, and a real conjugate. This is independent
of the centre-specific realization and finite-braid rigidity. -/
theorem exists_modular_witness (Z : BraidedFusionCategory.{v,u})
    (p : Dimensions.PivotalStructure (C := Z.Obj)) (hp : p.IsSpherical)
    (hdim : Modular.HasFPSimpleDimensions Z p)
    (hdet : (Modular.categoricalS Z p).det ≠ 0)
    (δ : ℝ) (hglobal : globalDimension Z = (δ : ℂ) ^ 2)
    (σ : ℂ ≃+* ℂ) :
    ∃ (y : Fin (rank Z)) (d : ℝ), 1 ≤ fpSimple Z y ∧
      σ (fpSimple Z y : ℂ) = (d : ℂ) ∧
      (∀ x, Modular.categoricalS Z p x y =
        (fpSimple Z y : ℂ) * σ.symm (Modular.simpleDimension Z p x)) ∧
      σ.symm ((δ : ℂ) ^ 2) = (δ : ℂ) ^ 2 / (fpSimple Z y : ℂ) ^ 2 ∧
      Modular.categoricalS Z p y y = (fpSimple Z y : ℂ) * σ.symm (fpSimple Z y : ℂ) := by
  have hreal := CentreCabling.realSimpleDimensions_of_fp hdim
  obtain ⟨act, hact⟩ := Modular.categoricalS_galois_action_of_invertibleS Z p hp hdet hreal
  let y := act σ.symm (unitIndex Z)
  have hprop := Modular.galois_unit_properties (Modular.simpleDimension_ne_zero Z p)
    (Modular.globalDimension_ne_zero_of_invertibleS Z p hp hdet hreal)
    (Modular.simpleDimension_unit Z p) (Modular.categorical_global_eq_sum_squares Z p hp)
    (Modular.categoricalS_symmetric Z p) (Modular.categoricalS_unit Z p)
    (Modular.categoricalS_square Z p hp hdet hreal) σ.symm y
    (fun x => hact σ.symm x (unitIndex Z))
  refine ⟨y, (σ (fpSimple Z y : ℂ)).re, one_le_fpSimple Z y,
    (fp_simple_galois_real Z σ y).symm, ?_, ?_, ?_⟩
  · intro x
    have h := hprop.1 x
    rw [hdim] at h
    exact h
  · have h := hprop.2.2
    rw [hglobal, hdim] at h
    exact h
  · have h := hprop.1 y
    rw [hdim] at h
    exact h

/-- Once the Galois-unit column is known to have finite braid image and the
actual three-strand rigidity theorem applies, the required numerical witness
follows from categorical modular data. -/
theorem center_witness_of_categorical_modular_data (Z : BraidedFusionCategory.{v,u})
    (p : Dimensions.PivotalStructure (C := Z.Obj)) (hp : p.IsSpherical)
    (hdim : Modular.HasFPSimpleDimensions Z p)
    (hdet : (Modular.categoricalS Z p).det ≠ 0)
    (δ b : ℝ) (hδ : 0 < δ) (hb : 0 < b)
    (hglobal : globalDimension Z = (δ : ℂ) ^ 2)
    (σ : ℂ ≃+* ℂ) (hτ : σ.symm (δ : ℂ) = (b : ℂ))
    (hF : ∀ y, (∀ x, Modular.categoricalS Z p x y =
      (fpSimple Z y : ℂ) * σ.symm (Modular.simpleDimension Z p x)) →
      ObjectPropertyF (simples Z y)) :
    ∃ f d : ℝ, σ (f : ℂ) = (d : ℂ) ∧ f * b = δ ∧ 1 ≤ f ∧ f = |d| := by
  obtain ⟨y, d, hf, hσf, hcolumn, hG, hS⟩ :=
    exists_modular_witness Z p hp hdim hdet δ hglobal σ
  exact ⟨_, d, center_witness_of_modular_and_rigidity σ hδ hb hf hτ hσf hG hS
    (galois_rigidity_of_propertyF Z p hdim σ y (hF y hcolumn) d hσf)⟩

end PropertyF.Ground
end
end

section
/-! The FP fusion character is self-dual, so all its conjugates are real
and bounded. This gives global FP conjugate bounds without any spherical or
pseudo-unitary assumptions. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
open scoped BigOperators
namespace PropertyF.Ground
universe v u

/-- Global FP dimension has positive, FP-bounded real conjugates. -/
theorem positive_bounded_conjugates_of_fp (C : BraidedFusionCategory.{v,u})
    (σ : ℂ ≃+* ℂ) : ∃ a : ℝ, 0 < a ∧ a ≤ globalFPDimension C ∧
      σ (globalFPDimension C : ℂ) = (a : ℂ) := by
  let χ : Fin (rank C) → ℂ := fun i => (fpSimple C i : ℂ)
  have hχ : χ (unitIndex C) ≠ 0 := by simp [χ, fpSimple_unit]
  have hchar : ∀ i j, χ i * χ j = ∑ k, (fusionCoeff C i j k : ℂ) * χ k := by
    intro i j
    dsimp [χ]
    exact_mod_cast fpSimple_mul C i j
  let d : Fin (rank C) → ℝ := fun i => (σ (χ i)).re
  have hbound (i : Fin (rank C)) : |d i| ≤ fpSimple C i := by
    have h := Dimensions.galois_character_norm_le_fpSimple C χ (unitIndex C) hχ hchar σ i
    rw [← fp_simple_galois_real C σ i] at h
    simpa [d, χ, Complex.norm_real, Real.norm_eq_abs] using h
  have hone : d (unitIndex C) = 1 := by simp [d, χ, fpSimple_unit]
  refine ⟨∑ i, (d i) ^ 2, ?_, ?_, ?_⟩
  · exact lt_of_lt_of_le zero_lt_one
      (Dimensions.global_sum_squares_one_le d ⟨unitIndex C, hone⟩)
  · exact Dimensions.target_globalDimension_le_of_simple_bounds C d hbound
  · have hglobal : (globalFPDimension C : ℂ) = ∑ i, (χ i) ^ 2 := by
      simp [globalFPDimension, χ, Complex.ofReal_sum, Complex.ofReal_pow]
    rw [hglobal, map_sum, Complex.ofReal_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [map_pow, ← fp_simple_galois_real C σ i]
    norm_cast

end PropertyF.Ground
end
end

section
/-! The Galois-unit finite-image argument without `CenterInputs`. -/

@[expose] public noncomputable section
namespace PropertyF.Ground
universe v u

/-- If the common centralizer has integral dimensions, its double centralizer
contains a simple with the Galois-unit column. Any such simple has property F
when property F holds throughout the generated subcategory. The two label
sets and the categorical double-centralizer and finite-image results are
explicit interim premises, not assumptions in the target. -/
theorem propertyF_of_galois_column
    (Z : BraidedFusionCategory.{v,u}) (p : Dimensions.PivotalStructure (C := Z.Obj))
    (τ : ℂ ≃+* ℂ) (core generated : Set (Fin (rank Z)))
    (hIntegral : ∀ x ∈ core, ∃ z : ℤ, Modular.simpleDimension Z p x = z)
    (hDouble : ∀ y, (∀ x ∈ core, Modular.categoricalS Z p x y =
      Modular.simpleDimension Z p x * Modular.simpleDimension Z p y) → y ∈ generated)
    (hFinite : ∀ y ∈ generated, ObjectPropertyF (simples Z y))
    (y : Fin (rank Z))
    (hColumn : ∀ x, Modular.categoricalS Z p x y =
      Modular.simpleDimension Z p y * τ (Modular.simpleDimension Z p x)) :
    ObjectPropertyF (simples Z y) := by
  apply hFinite y
  apply hDouble y
  intro x hx
  obtain ⟨z, hz⟩ := hIntegral x hx
  rw [hColumn, hz, map_intCast, mul_comm]

end PropertyF.Ground
end
end

/-! # Reduction to the actual Drinfeld centre

The overlap, modularity and product-retract reductions assemble the categorical
inputs required by the final integrality argument. -/

section
/-! Discharge overlap coherence and reduce the target to its modular centre. -/

@[expose] public noncomputable section
open CategoryTheory
namespace PropertyF.Ground
universe v u

set_option backward.isDefEq.respectTransparency false in
/-- The target follows from an actual positive spherical modular centre with
the global dimension and selected finite-braid-image properties. All of
these centre facts remain explicit premises. -/
theorem target_of_modular_center
    (hCenter : ∀ (C : BraidedFusionCategory.{v,u}), PseudoUnitary C →
      HasPropertyF C.Obj → ∀ σ : ℂ ≃+* ℂ,
      ∃ (Z : BraidedFusionCategory.{v,max u v}) (p : Dimensions.PivotalStructure (C := Z.Obj)),
        p.IsSpherical ∧
        (Modular.HasFPSimpleDimensions Z p) ∧
        (Modular.categoricalS Z p).det ≠ 0 ∧
        globalDimension Z = (globalFPDimension C : ℂ) ^ 2 ∧
        (∀ y, (∀ x, Modular.categoricalS Z p x y =
          (fpSimple Z y : ℂ) * σ.symm (Modular.simpleDimension Z p x)) →
          ObjectPropertyF (simples Z y))) : TargetStatement.{v,u} := by
  apply target_of_bounded_conjugates_and_witness
  · intro C _ _ σ
    exact positive_bounded_conjugates_of_fp C σ
  · intro C hPU hF σ a b _ _ _ hτ
    obtain ⟨b', hb', _, hb'eq⟩ := positive_bounded_conjugates_of_fp C σ.symm
    have hb : 0 < b := (Complex.ofReal_injective (hb'eq.symm.trans hτ)) ▸ hb'
    obtain ⟨Z, p, hp, hdim, hdet, hglobal, hfinite⟩ := hCenter C hPU hF σ
    apply center_witness_of_categorical_modular_data Z p hp hdim hdet
      (globalFPDimension C) b (lt_of_lt_of_le (by norm_num) (one_le_globalFPDimension C))
      hb hglobal σ hτ hfinite


end PropertyF.Ground
end
end

section
/-! Expose the remaining centre inputs in the final reduction. -/

@[expose] public noncomputable section
namespace PropertyF.Ground
universe v u

/-- The target follows from the actual centre and the three categorical
centralizer facts in the paper. These facts are explicit interim premises;
no old hypothesis structure appears in the dependency cone. -/
theorem target_of_center_centralizers
    (hCenter : ∀ (C : BraidedFusionCategory.{v,u}), PseudoUnitary C →
      HasPropertyF C.Obj → ∀ σ : ℂ ≃+* ℂ,
      ∃ (Z : BraidedFusionCategory.{v,max u v}) (p : Dimensions.PivotalStructure (C := Z.Obj))
        (core generated : Set (Fin (rank Z))),
        p.IsSpherical ∧
        (Modular.HasFPSimpleDimensions Z p) ∧
        (Modular.categoricalS Z p).det ≠ 0 ∧
        globalDimension Z = (globalFPDimension C : ℂ) ^ 2 ∧
        (∀ x ∈ core, ∃ z : ℤ, Modular.simpleDimension Z p x = z) ∧
        (∀ y, (∀ x ∈ core, Modular.categoricalS Z p x y =
          Modular.simpleDimension Z p x * Modular.simpleDimension Z p y) → y ∈ generated) ∧
        (∀ y ∈ generated, ObjectPropertyF (simples Z y))) : TargetStatement.{v,u} := by
  apply target_of_modular_center
  intro C hPU hF σ
  obtain ⟨Z, p, core, generated, hp, hdim, hdet, hglobal, hIntegral, hDouble, hFinite⟩ :=
    hCenter C hPU hF σ
  refine ⟨Z, p, hp, hdim, hdet, hglobal, ?_⟩
  intro y hColumn
  apply propertyF_of_galois_column Z p σ.symm core generated hIntegral hDouble hFinite y
  intro x
  rw [hdim y]
  exact hColumn x

end PropertyF.Ground
end
end

section
/-! Transfer finite braid images from actual centre product retracts. -/

@[expose] public noncomputable section
set_option linter.style.haveILetI false
open CategoryTheory
namespace PropertyF.Ground
universe v u v' u'

/-- A faithful braided functor reflects the finite image of a product retract. -/
theorem propertyF_of_center_productRetract (C : BraidedFusionCategory.{v,u})
    (Z : BraidedFusionCategory.{v',u'}) (F : Z.Obj ⥤ CategoryTheory.Center C.Obj)
    [F.Braided] [F.Faithful] (hF : HasPropertyF C.Obj)
    (X : Z.Obj) (hX : Centre.ProductRetract (F.obj X)) : ObjectPropertyF X := fun n ↦
  letI : Finite (braidImage (F.obj X) n) := Centre.productRetract_propertyF hX hF n
  Finite.of_injective (Modular.braidImageFunctorIso F X n)
    (Modular.braidImageFunctorIso F X n).injective

/-- Replace the generated-label finite-image premise by actual product
retracts in Mathlib’s centre. The centre and centralizer facts remain explicit
unproved premises of this reduction. -/
theorem target_of_center_product_retracts
    (hCenter : ∀ (C : BraidedFusionCategory.{v,u}), PseudoUnitary C →
      HasPropertyF C.Obj → ∀ σ : ℂ ≃+* ℂ,
      ∃ (Z : BraidedFusionCategory.{v,max u v}) (p : Dimensions.PivotalStructure (C := Z.Obj))
        (F : Z.Obj ⥤ CategoryTheory.Center C.Obj),
        Nonempty F.Braided ∧ F.Faithful ∧
      ∃ (core generated : Set (Fin (rank Z))),
        p.IsSpherical ∧
        (Modular.HasFPSimpleDimensions Z p) ∧
        (Modular.categoricalS Z p).det ≠ 0 ∧
        globalDimension Z = (globalFPDimension C : ℂ) ^ 2 ∧
        (∀ x ∈ core, ∃ z : ℤ, Modular.simpleDimension Z p x = z) ∧
        (∀ y, (∀ x ∈ core, Modular.categoricalS Z p x y =
          Modular.simpleDimension Z p x * Modular.simpleDimension Z p y) → y ∈ generated) ∧
        (∀ y ∈ generated, Centre.ProductRetract (F.obj (simples Z y)))) :
    TargetStatement.{v,u} := by
  apply target_of_center_centralizers
  intro C hPU hF σ
  obtain ⟨Z, p, F, hB, hfaithful, core, generated, hp, hdim, hdet, hglobal,
    hIntegral, hDouble, hProduct⟩ := hCenter C hPU hF σ
  letI : F.Braided := hB.some
  letI : F.Faithful := hfaithful
  refine ⟨Z, p, core, generated, hp, hdim, hdet, hglobal, hIntegral, hDouble, ?_⟩
  intro y hy
  exact propertyF_of_center_productRetract C Z F hF (simples Z y) (hProduct y hy)

end PropertyF.Ground
end
end

section
/-! State the remaining inputs on Mathlib’s actual Drinfeld centre. -/

@[expose] public noncomputable section
set_option linter.style.haveILetI false
open CategoryTheory
namespace PropertyF.Ground
universe v u

/-- The target follows from explicit rigidity, fusion, modularity, dimension
and centralizer assertions about the actual centre. Those assertions remain
unproved premises of this reduction. -/
theorem target_of_actual_center
    (hCenter : ∀ (C : BraidedFusionCategory.{v,u}), PseudoUnitary C →
      HasPropertyF C.Obj →
      ∃ (hR : RigidCategory (CategoryTheory.Center C.Obj)),
        letI := hR
        ∃ (hFusion : IsFusionCategory (CategoryTheory.Center C.Obj)),
          letI := hFusion
          let Z := Integrate.bundledCenter C
          ∃ (p : Dimensions.PivotalStructure (C := Z.Obj))
            (core generated : Set (Fin (rank Z))),
            p.IsSpherical ∧
            (Modular.HasFPSimpleDimensions Z p) ∧
            (Modular.categoricalS Z p).det ≠ 0 ∧
            globalDimension Z = (globalFPDimension C : ℂ) ^ 2 ∧
            (∀ x ∈ core, ∃ z : ℤ, Modular.simpleDimension Z p x = z) ∧
            (∀ y, (∀ x ∈ core, Modular.categoricalS Z p x y =
              Modular.simpleDimension Z p x * Modular.simpleDimension Z p y) → y ∈ generated) ∧
            (∀ y ∈ generated, Centre.ProductRetract (simples Z y))) : TargetStatement.{v,u} := by
  apply target_of_center_product_retracts
  intro C hPU hF σ
  obtain ⟨hR, hFusion, p, core, generated, hp, hdim, hdet, hglobal, hIntegral, hDouble, hProduct⟩ :=
    hCenter C hPU hF
  letI := hR
  letI := hFusion
  have hB : (𝟭 (CategoryTheory.Center C.Obj)).Braided := inferInstance
  have hfaithful : (𝟭 (CategoryTheory.Center C.Obj)).Faithful := inferInstance
  exact ⟨Integrate.bundledCenter C, p, 𝟭 (CategoryTheory.Center C.Obj), ⟨hB⟩, hfaithful,
    core, generated, hp, hdim, hdet, hglobal, hIntegral, hDouble, hProduct⟩

end PropertyF.Ground
end
end
