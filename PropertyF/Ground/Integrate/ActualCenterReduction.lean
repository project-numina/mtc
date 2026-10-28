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
    {p : Dimensions.PivotalStructure (C := Z.Obj)} (hp : p.IsSpherical)
    (hdim : Modular.HasFPSimpleDimensions Z p)
    (hdet : (Modular.categoricalS Z p).det ≠ 0)
    {δ : ℝ} (hglobal : globalDimension Z = (δ : ℂ) ^ 2)
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
    simpa only [hdim] using hprop.1 x
  · simpa only [hglobal, hdim] using hprop.2.2
  · simpa only [hdim] using hprop.1 y

/-- Once the Galois-unit column is known to have finite braid image and the
actual three-strand rigidity theorem applies, the required numerical witness
follows from categorical modular data. -/
theorem center_witness_of_categorical_modular_data (Z : BraidedFusionCategory.{v,u})
    {p : Dimensions.PivotalStructure (C := Z.Obj)} (hp : p.IsSpherical)
    (hdim : Modular.HasFPSimpleDimensions Z p)
    (hdet : (Modular.categoricalS Z p).det ≠ 0)
    {δ b : ℝ} (hδ : 0 < δ) (hb : 0 < b)
    (hglobal : globalDimension Z = (δ : ℂ) ^ 2)
    (σ : ℂ ≃+* ℂ) (hτ : σ.symm (δ : ℂ) = (b : ℂ))
    (hF : ∀ y, (∀ x, Modular.categoricalS Z p x y =
      (fpSimple Z y : ℂ) * σ.symm (Modular.simpleDimension Z p x)) →
      ObjectPropertyF (simples Z y)) :
    ∃ f d : ℝ, σ (f : ℂ) = (d : ℂ) ∧ f * b = δ ∧ 1 ≤ f ∧ f = |d| := by
  obtain ⟨y, d, hf, hσf, hcolumn, hG, hS⟩ :=
    exists_modular_witness Z hp hdim hdet hglobal σ
  exact ⟨_, d, center_witness_of_modular_and_rigidity (σ := σ) hδ hb hf hτ hσf hG hS
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
  have hchar : IsFusionMultiplicative C χ := fpSimple_isFusionMultiplicative C
  let d : Fin (rank C) → ℝ := fun i => (σ (χ i)).re
  have hbound (i : Fin (rank C)) : |d i| ≤ fpSimple C i := by
    have h := Dimensions.galois_character_norm_le_fpSimple C hχ hchar σ i
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

/-- The simple dimensions indexed by a set are integers. -/
abbrev HasIntegralSimpleDimensionsOn (Z : BraidedFusionCategory.{v,u})
    (p : Dimensions.PivotalStructure (C := Z.Obj)) (core : Set (Fin (rank Z))) : Prop :=
  ∀ x ∈ core, ∃ z : ℤ, Modular.simpleDimension Z p x = z

/-- If the common centralizer has integral dimensions, its double centralizer
contains a simple with the Galois-unit column. Any such simple has property F
when property F holds throughout the generated subcategory. The two label
sets and the categorical double-centralizer and finite-image results are
explicit interim premises, not assumptions in the target. -/
theorem propertyF_of_galois_column
    (Z : BraidedFusionCategory.{v,u}) (p : Dimensions.PivotalStructure (C := Z.Obj))
    (τ : ℂ ≃+* ℂ) (core generated : Set (Fin (rank Z)))
    (hIntegral : HasIntegralSimpleDimensionsOn Z p core)
    (hDouble : CentreCabling.sCentralizer Z p core ⊆ generated)
    (hFinite : ∀ y ∈ generated, ObjectPropertyF (simples Z y))
    (y : Fin (rank Z))
    (hColumn : ∀ x, Modular.categoricalS Z p x y =
      Modular.simpleDimension Z p y * τ (Modular.simpleDimension Z p x)) :
    ObjectPropertyF (simples Z y) :=
  hFinite y <| hDouble fun x hx ↦ by
    obtain ⟨z, hz⟩ := hIntegral x hx
    change Modular.categoricalS Z p x y = Modular.simpleDimension Z p x * Modular.simpleDimension Z p y
    rw [hColumn, hz, map_intCast, mul_comm]

end PropertyF.Ground
end
end

/-! # Reduction to the actual Drinfeld centre

The overlap, modularity and product-retract reductions assemble the categorical
inputs required by the final integrality argument. -/

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
            (HasIntegralSimpleDimensionsOn Z p core) ∧
            (CentreCabling.sCentralizer Z p core ⊆ generated) ∧
            (∀ y ∈ generated, Centre.ProductRetract (simples Z y))) : TargetStatement.{v,u} := by
  intro C hPU hF
  obtain ⟨D, σ, ⟨E⟩, hD⟩ := hPU
  have hDF := Modular.conjugate_propertyF E hF
  have hfixed := galois_fixed_of_smaller_conjugate_witness (globalFPDimension D)
    (lt_of_lt_of_le zero_lt_one (one_le_globalFPDimension D))
    (positive_bounded_conjugates_of_fp D) (by
      intro τ a b _ _ _ hτ
      obtain ⟨b', hb', _, hb'eq⟩ := positive_bounded_conjugates_of_fp D τ.symm
      have hb : 0 < b := (Complex.ofReal_injective (hb'eq.symm.trans hτ)) ▸ hb'
      obtain ⟨hR, hFusion, p, core, generated, hp, hdim, hdet, hglobal,
        hIntegral, hDouble, hProduct⟩ := hCenter D hD hDF
      letI := hR
      letI := hFusion
      let Z := Integrate.bundledCenter D
      apply center_witness_of_categorical_modular_data Z hp hdim hdet
        (lt_of_lt_of_le zero_lt_one (one_le_globalFPDimension D)) hb hglobal τ hτ
      intro y hColumn
      apply propertyF_of_galois_column Z p τ.symm core generated hIntegral hDouble ?_ y
      · intro x
        rw [hdim y]
        exact hColumn x
      · intro i hi
        exact Centre.productRetract_propertyF (hProduct i hi) hDF)
  have hInt := weaklyIntegral_of_globalFPDimension_fixed D hfixed
  rwa [Modular.conjugate_globalFPDimension E]

end PropertyF.Ground
end
end
