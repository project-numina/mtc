module
public import PropertyF.Ground.Integrate.Arithmetic
public import PropertyF.Ground.Integrate.CharacterReality
public import PropertyF.Ground.Dimensions.DimensionCharacter
public import PropertyF.Ground.Dimensions.GroundNorm
public import PropertyF.Ground.Modular.FusionTransport

public import PropertyF.Ground.Fusion.Agreement
public import PropertyF.Ground.Modular.SSquare
public import PropertyF.Ground.Modular.SMatrix
public import PropertyF.Ground.Integrate.TwistedRigidity
public import PropertyF.Ground.Dimensions.SimpleScalars
public import PropertyF.Ground.Calculus.TensorPowerCoherence
public import PropertyF.Ground.Centre.ProductClosure
public import PropertyF.Ground.CentreCabling.RegularSupport
public import PropertyF.Ground.Integrate.CenterBundle

section
/-! Extract the numerical ingredients of the paper's witness from an actual
spherical category with positive FP dimensions and invertible S matrix. -/

@[expose] public noncomputable section
open CategoryTheory
open PropertyF.Ground.Modular (IsFPSpherical)
open scoped BigOperators
namespace PropertyF.Ground
universe v u

/-- A column satisfying the Galois-unit identity. -/
abbrev IsGaloisUnitColumn (Z : BraidedFusionCategory.{v,u})
    (p : Dimensions.PivotalStructure (C := Z.Obj)) (τ : ℂ ≃+* ℂ) (y : Fin (rank Z)) : Prop :=
  ∀ x, Modular.categoricalS Z p x y =
    Modular.simpleDimension Z p y * τ (Modular.simpleDimension Z p x)

variable (Z : BraidedFusionCategory.{v,u}) {p : Dimensions.PivotalStructure (C := Z.Obj)}
local notation "𝒮" => Modular.categoricalS Z p
local notation "𝒇" => fpSimple Z

/-- The Galois-unit label has dimension at least one, the Galois-unit column,
and the modular global-dimension identity. -/
theorem exists_modular_witness (hfp : IsFPSpherical Z p) (hdet : (𝒮).det ≠ 0)
    {δ : ℝ} (hglobal : globalDimension Z = (δ : ℂ) ^ 2) (σ : ℂ ≃+* ℂ) :
    ∃ y : Fin (rank Z), 1 ≤ 𝒇 y ∧ IsGaloisUnitColumn Z p σ.symm y ∧
      σ.symm ((δ : ℂ) ^ 2) = (δ : ℂ) ^ 2 / (𝒇 y : ℂ) ^ 2 := by
  have hreal := CentreCabling.realSimpleDimensions_of_fp hfp.2
  obtain ⟨act, hact⟩ := Modular.categoricalS_galois_action_of_invertibleS Z p hfp.1 hdet hreal
  let y := act σ.symm (unitIndex Z)
  obtain ⟨hcolumn, _, hG⟩ := Modular.galois_unit_properties (Modular.simpleDimension_ne_zero Z p)
    (Modular.globalDimension_ne_zero_of_invertibleS Z p hfp.1 hdet hreal)
    (Modular.simpleDimension_unit Z p) (Modular.categorical_global_eq_sum_squares Z p hfp.1)
    (Modular.categoricalS_symmetric Z p) (Modular.categoricalS_unit Z p)
    (Modular.categoricalS_square Z p hfp.1 hdet hreal) σ.symm y
    (fun x => hact σ.symm x (unitIndex Z))
  exact ⟨y, one_le_fpSimple Z y, by simpa only [IsGaloisUnitColumn, hfp.2] using hcolumn,
    by simpa only [hglobal, hfp.2] using hG⟩

/-- Once the Galois-unit column is known to have finite braid image and the
actual three-strand rigidity theorem applies, the required numerical witness
follows from categorical modular data. -/
theorem center_witness_of_categorical_modular_data (hfp : IsFPSpherical Z p)
    (hdet : (𝒮).det ≠ 0) {δ b : ℝ} (hδ : 0 < δ) (hb : 0 < b)
    (hglobal : globalDimension Z = (δ : ℂ) ^ 2)
    (σ : ℂ ≃+* ℂ) (hτ : σ.symm (δ : ℂ) = (b : ℂ))
    (hF : ∀ y, IsGaloisUnitColumn Z p σ.symm y → ObjectPropertyF (simples Z y)) :
    HasGaloisDimensionWitness (algebraMap ℝ ℂ) σ δ b :=
  let ⟨y, hf, hcolumn, hG⟩ := exists_modular_witness Z hfp hdet hglobal σ
  let d := (σ (𝒇 y : ℂ)).re
  let hσf : σ (𝒇 y : ℂ) = (d : ℂ) := (fp_simple_galois_real Z σ y).symm
  ⟨𝒇 y, d, hσf,
    (by
      refine (sq_eq_sq₀ (mul_pos (lt_of_lt_of_le zero_lt_one hf) hb).le hδ.le).mp ?_
      apply Complex.ofReal_injective
      simpa only [Complex.ofReal_mul, Complex.ofReal_pow, mul_pow, mul_comm] using
        (eq_div_iff (pow_ne_zero 2 (by exact_mod_cast (ne_of_gt (lt_of_lt_of_le zero_lt_one hf))))).mp
          (by simpa only [map_pow, hτ] using hG)), hf,
    galois_rigidity_of_propertyF Z p hfp.2 (hF y hcolumn) hσf (by
      rw [hcolumn y, hfp.2 y, map_mul, hσf, σ.apply_symm_apply])⟩

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

variable (C : BraidedFusionCategory.{v,u}) (σ : ℂ ≃+* ℂ)

/-- Every Galois conjugate of the global FP dimension is the sum of the
squares of the real conjugates of the simple FP dimensions. -/
theorem globalFPDimension_galois_sum_squares : σ (globalFPDimension C : ℂ) =
      ((∑ i, (σ (fpSimple C i : ℂ)).re ^ 2 : ℝ) : ℂ) := by
  simp only [globalFPDimension, Complex.ofReal_sum, Complex.ofReal_pow, map_sum, map_pow,
    fp_simple_galois_real]

/-- A Galois conjugate of a simple FP dimension is bounded by that dimension. -/
theorem fp_simple_galois_norm_le (i : Fin (rank C)) :
    ‖σ (fpSimple C i : ℂ)‖ ≤ fpSimple C i :=
  Dimensions.galois_character_norm_le_fpSimple C (χ := fun i ↦ (fpSimple C i : ℂ))
    (i₀ := unitIndex C) (by simp [fpSimple_unit]) (fpSimple_isFusionMultiplicative C) σ i

/-- Global FP dimension has positive, FP-bounded real conjugates. -/
theorem positive_bounded_conjugates_of_fp : ∃ a : ℝ, 0 < a ∧ a ≤ globalFPDimension C ∧
      σ (globalFPDimension C : ℂ) = (a : ℂ) :=
  let d : Fin (rank C) → ℝ := fun i ↦ (σ (fpSimple C i : ℂ)).re
  have hbound (i : Fin (rank C)) : |d i| ≤ fpSimple C i := by
    simp only [d, ← Real.norm_eq_abs, ← Complex.norm_real, fp_simple_galois_real]
    exact fp_simple_galois_norm_le C σ i
  ⟨∑ i, (d i) ^ 2, lt_of_lt_of_le zero_lt_one
      (Dimensions.global_sum_squares_one_le d ⟨unitIndex C, by simp [d, fpSimple_unit]⟩),
    Dimensions.target_globalDimension_le_of_simple_bounds C hbound,
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
variable {τ : ℂ ≃+* ℂ} {core generated : Set (Fin (rank Z))} {y : Fin (rank Z)}

/-- If the common centralizer has integral dimensions, its double centralizer
contains a simple with the Galois-unit column. Any such simple has property F
when property F holds throughout the generated subcategory. The two label
sets and the categorical double-centralizer and finite-image results are
explicit interim premises, not assumptions in the target. -/
theorem propertyF_of_galois_column (hIntegral : HasIntegralSimpleDimensionsOn Z p core)
    (hDouble : Modular.sCentralizer Z p core ⊆ generated)
    (hFinite : ∀ y ∈ generated, ObjectPropertyF (simples Z y))
    (hColumn : IsGaloisUnitColumn Z p τ y) : ObjectPropertyF (simples Z y) :=
  hFinite y <| hDouble fun x hx ↦ by
    obtain ⟨z, hz⟩ := hIntegral x hx
    simpa only [Modular.sCentralizes, hz, map_intCast, mul_comm] using hColumn x

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
    (hfp : Modular.IsFPSpherical 𝒵ᶠ p) (hdet : (Modular.categoricalS 𝒵ᶠ p).det ≠ 0)
    (hglobal : globalDimension 𝒵ᶠ = (globalFPDimension C : ℂ) ^ 2)
    (hIntegral : HasIntegralSimpleDimensionsOn 𝒵ᶠ p core)
    (hDouble : Modular.sCentralizer 𝒵ᶠ p core ⊆ generated)
    (hProduct : ∀ y ∈ generated, Centre.ProductRetract (simples 𝒵ᶠ y)) :
    WeaklyIntegral (globalFPDimension C) := by
  apply weaklyIntegral_of_galois_fixed (globalFPDimension_isIntegral C)
  apply galois_fixed_of_smaller_conjugate_witness (j := algebraMap ℝ ℂ) (globalFPDimension C)
    (lt_of_lt_of_le zero_lt_one (one_le_globalFPDimension C))
    (positive_bounded_conjugates_of_fp C)
  intro τ a b _ _ _ hτ
  change τ.symm (globalFPDimension C : ℂ) = (b : ℂ) at hτ
  obtain ⟨b', hb', _, hb'eq⟩ := positive_bounded_conjugates_of_fp C τ.symm
  have hb : 0 < b := (Complex.ofReal_injective (hb'eq.symm.trans hτ)) ▸ hb'
  apply center_witness_of_categorical_modular_data 𝒵ᶠ hfp hdet
    (lt_of_lt_of_le zero_lt_one (one_le_globalFPDimension C)) hb hglobal τ hτ
  intro y hColumn
  exact propertyF_of_galois_column hIntegral hDouble
    (fun i hi ↦ Centre.productRetract_propertyF (hProduct i hi) hF) hColumn

end PropertyF.Ground
end
end
