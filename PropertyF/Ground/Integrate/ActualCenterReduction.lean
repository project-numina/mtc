module
public import PropertyF.Ground.Integrate.Arithmetic
public import PropertyF.Ground.Integrate.CharacterReality
public import PropertyF.Ground.Dimensions.DimensionCharacter
public import PropertyF.Ground.Dimensions.GroundNorm
public import PropertyF.Ground.Modular.FusionTransport
public import PropertyF.Ground.Dimensions.IntrinsicNonzero
public import PropertyF.Ground.Fusion.Agreement
public import PropertyF.Ground.Modular.SSquare
public import PropertyF.Ground.Modular.SMatrix
public import PropertyF.Ground.Integrate.TwistedRigidity
public import PropertyF.Ground.Dimensions.PivotalTwist
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

variable (Z : BraidedFusionCategory.{v,u}) {p : Dimensions.PivotalStructure (C := Z.Obj)}
local notation "𝒮" => Modular.categoricalS Z p
local notation "𝒅" => Modular.simpleDimension Z p
local notation "𝒇" => fpSimple Z

/-- The actual Galois-unit label supplies the modular dimension identity, its
self-column, a dimension at least one, and a real conjugate. This is independent
of the centre-specific realization and finite-braid rigidity. -/
theorem exists_modular_witness (hp : p.IsSpherical)
    (hdim : Modular.HasFPSimpleDimensions Z p)
    (hdet : (𝒮).det ≠ 0)
    {δ : ℝ} (hglobal : globalDimension Z = (δ : ℂ) ^ 2)
    (σ : ℂ ≃+* ℂ) :
    ∃ (y : Fin (rank Z)) (d : ℝ), 1 ≤ 𝒇 y ∧
      σ (𝒇 y : ℂ) = (d : ℂ) ∧
      (∀ x, 𝒮 x y =
        (𝒇 y : ℂ) * σ.symm (𝒅 x)) ∧
      σ.symm ((δ : ℂ) ^ 2) = (δ : ℂ) ^ 2 / (𝒇 y : ℂ) ^ 2 ∧
      𝒮 y y = (𝒇 y : ℂ) * σ.symm (𝒇 y : ℂ) := by
  have hreal := CentreCabling.realSimpleDimensions_of_fp hdim
  obtain ⟨act, hact⟩ := Modular.categoricalS_galois_action_of_invertibleS Z p hp hdet hreal
  let y := act σ.symm (unitIndex Z)
  have hprop := Modular.galois_unit_properties (Modular.simpleDimension_ne_zero Z p)
    (Modular.globalDimension_ne_zero_of_invertibleS Z p hp hdet hreal)
    (Modular.simpleDimension_unit Z p) (Modular.categorical_global_eq_sum_squares Z p hp)
    (Modular.categoricalS_symmetric Z p) (Modular.categoricalS_unit Z p)
    (Modular.categoricalS_square Z p hp hdet hreal) σ.symm y
    (fun x => hact σ.symm x (unitIndex Z))
  refine ⟨y, (σ (𝒇 y : ℂ)).re, one_le_fpSimple Z y,
    (fp_simple_galois_real Z σ y).symm, ?_, ?_, ?_⟩
  · simpa only [hdim] using hprop.1
  · simpa only [hglobal, hdim] using hprop.2.2
  · simpa only [hdim] using hprop.1 y

/-- Once the Galois-unit column is known to have finite braid image and the
actual three-strand rigidity theorem applies, the required numerical witness
follows from categorical modular data. -/
theorem center_witness_of_categorical_modular_data (hp : p.IsSpherical)
    (hdim : Modular.HasFPSimpleDimensions Z p)
    (hdet : (𝒮).det ≠ 0)
    {δ b : ℝ} (hδ : 0 < δ) (hb : 0 < b)
    (hglobal : globalDimension Z = (δ : ℂ) ^ 2)
    (σ : ℂ ≃+* ℂ) (hτ : σ.symm (δ : ℂ) = (b : ℂ))
    (hF : ∀ y, (∀ x, 𝒮 x y =
      (𝒇 y : ℂ) * σ.symm (𝒅 x)) →
      ObjectPropertyF (simples Z y)) :
    ∃ f d : ℝ, σ (f : ℂ) = (d : ℂ) ∧ f * b = δ ∧ 1 ≤ f ∧ f = |d| :=
  let ⟨y, d, hf, hσf, hcolumn, hG, hS⟩ := exists_modular_witness Z hp hdim hdet hglobal σ
  ⟨_, d, center_witness_of_modular_and_rigidity (σ := σ) hδ hb hf hτ hσf hG hS
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

/-- Every Galois conjugate of the global FP dimension is the sum of the
squares of the real conjugates of the simple FP dimensions. -/
theorem globalFPDimension_galois_sum_squares (C : BraidedFusionCategory.{v,u})
    (σ : ℂ ≃+* ℂ) : σ (globalFPDimension C : ℂ) =
      ((∑ i, (σ (fpSimple C i : ℂ)).re ^ 2 : ℝ) : ℂ) := by
  simp only [globalFPDimension, Complex.ofReal_sum, Complex.ofReal_pow, map_sum, map_pow]
  apply Finset.sum_congr rfl
  intro i _
  rw [← fp_simple_galois_real C σ i]
  norm_cast

/-- Global FP dimension has positive, FP-bounded real conjugates. -/
theorem positive_bounded_conjugates_of_fp (C : BraidedFusionCategory.{v,u})
    (σ : ℂ ≃+* ℂ) : ∃ a : ℝ, 0 < a ∧ a ≤ globalFPDimension C ∧
      σ (globalFPDimension C : ℂ) = (a : ℂ) := by
  let χ : Fin (rank C) → ℂ := fun i => (fpSimple C i : ℂ)
  let d : Fin (rank C) → ℝ := fun i => (σ (χ i)).re
  have hbound (i : Fin (rank C)) : |d i| ≤ fpSimple C i := by
    have h := Dimensions.galois_character_norm_le_fpSimple C (χ := χ) (i₀ := unitIndex C)
      (by simp [χ, fpSimple_unit]) (fpSimple_isFusionMultiplicative C) σ i
    rw [← fp_simple_galois_real C σ i] at h
    simpa [d, χ, Complex.norm_real, Real.norm_eq_abs] using h
  exact ⟨∑ i, (d i) ^ 2, lt_of_lt_of_le zero_lt_one
      (Dimensions.global_sum_squares_one_le d ⟨unitIndex C, by simp [d, χ, fpSimple_unit]⟩),
    Dimensions.target_globalDimension_le_of_simple_bounds C d hbound,
    globalFPDimension_galois_sum_squares C σ⟩

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

variable {Z : BraidedFusionCategory.{v,u}} {p : Dimensions.PivotalStructure (C := Z.Obj)}
variable {τ : ℂ ≃+* ℂ} {core generated : Set (Fin (rank Z))}
local notation "𝒮" => Modular.categoricalS Z p
local notation "𝒅" => Modular.simpleDimension Z p

/-- If the common centralizer has integral dimensions, its double centralizer
contains a simple with the Galois-unit column. Any such simple has property F
when property F holds throughout the generated subcategory. The two label
sets and the categorical double-centralizer and finite-image results are
explicit interim premises, not assumptions in the target. -/
theorem propertyF_of_galois_column (hIntegral : HasIntegralSimpleDimensionsOn Z p core)
    (hDouble : CentreCabling.sCentralizer Z p core ⊆ generated)
    (hFinite : ∀ y ∈ generated, ObjectPropertyF (simples Z y))
    (y : Fin (rank Z))
    (hColumn : ∀ x, 𝒮 x y =
      𝒅 y * τ (𝒅 x)) :
    ObjectPropertyF (simples Z y) :=
  hFinite y <| hDouble fun x hx ↦ by
    obtain ⟨z, hz⟩ := hIntegral x hx
    simpa only [CentreCabling.sCentralizes, hz, map_intCast, mul_comm] using hColumn x

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

variable (C : BraidedFusionCategory.{v,u})
variable [RigidCategory (CategoryTheory.Center C.Obj)] [IsFusionCategory (CategoryTheory.Center C.Obj)]
local notation "𝒵ᶠ" => Integrate.bundledCenter C

/-- A modular actual centre with integral centralizer and finite braid-image
retracts forces the global Frobenius–Perron dimension to be integral. -/
theorem weaklyIntegral_of_actual_center (hF : HasPropertyF C.Obj)
    {p : Dimensions.PivotalStructure (C := 𝒵ᶠ.Obj)}
    {core generated : Set (Fin (rank 𝒵ᶠ))}
    (hp : p.IsSpherical) (hdim : Modular.HasFPSimpleDimensions 𝒵ᶠ p)
    (hdet : (Modular.categoricalS 𝒵ᶠ p).det ≠ 0)
    (hglobal : globalDimension 𝒵ᶠ = (globalFPDimension C : ℂ) ^ 2)
    (hIntegral : HasIntegralSimpleDimensionsOn 𝒵ᶠ p core)
    (hDouble : CentreCabling.sCentralizer 𝒵ᶠ p core ⊆ generated)
    (hProduct : ∀ y ∈ generated, Centre.ProductRetract (simples 𝒵ᶠ y)) :
    WeaklyIntegral (globalFPDimension C) := by
  apply weaklyIntegral_of_galois_fixed (globalFPDimension_isIntegral C)
  apply galois_fixed_of_smaller_conjugate_witness (globalFPDimension C)
    (lt_of_lt_of_le zero_lt_one (one_le_globalFPDimension C))
    (positive_bounded_conjugates_of_fp C)
  intro τ a b _ _ _ hτ
  obtain ⟨b', hb', _, hb'eq⟩ := positive_bounded_conjugates_of_fp C τ.symm
  have hb : 0 < b := (Complex.ofReal_injective (hb'eq.symm.trans hτ)) ▸ hb'
  apply center_witness_of_categorical_modular_data 𝒵ᶠ hp hdim hdet
    (lt_of_lt_of_le zero_lt_one (one_le_globalFPDimension C)) hb hglobal τ hτ
  intro y hColumn
  apply propertyF_of_galois_column hIntegral hDouble ?_ y
  · intro x
    rw [hdim y]
    exact hColumn x
  · intro i hi
    exact Centre.productRetract_propertyF (hProduct i hi) hF

end PropertyF.Ground
end
end
