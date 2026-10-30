module
public import MTC.PropertyF.Reduction.CharacterReality
public import MTC.CategoryTheory.Dimensions.DimensionCharacter
public import MTC.CategoryTheory.Dimensions.SquaredNorm
public import MTC.Modular.FusionTransport
public import MTC.Fusion.Agreement
public import MTC.Modular.SSquare
public import MTC.Modular.SMatrix
public import MTC.PropertyF.Reduction.TwistedRigidity
public import MTC.CategoryTheory.Dimensions.SimpleScalars
public import MTC.Braided.Trace.TensorPowerCoherence
public import MTC.Center.ProductClosure
public import MTC.Center.Braid.RegularSupport
public import MTC.Center.Fusion.Bundled
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Tactic
public import Mathlib.FieldTheory.IsSepClosed
public import MTC.Fusion.SpectralIntegral
public import Mathlib.FieldTheory.IsAlgClosed.Classification
public import Mathlib.Algebra.MvPolynomial.Equiv
public import MTC.Algebra.Arithmetic

open MTC.Fusion

open MTC.Braided

/-! # Galois arithmetic and the centre reduction

The numerical descent and categorical centre witnesses combine to prove
weak integrality from the actual centre and its finite braid images.

## Main results

* `integral_eq_int_of_complex_galois_fixed` gives the arithmetic descent.
* `center_witness_of_categorical_modular_data` constructs the numerical witness.
* `weaklyIntegral_of_actual_center` assembles the centre reduction. -/

/-! # Galois fixedness and integrality

A positive ratio and the centre's rigidity witness rule out smaller Galois
conjugates. A real algebraic integer fixed by every complex automorphism is an
integer, yielding the arithmetic descent used in the final theorem. -/

@[expose] public noncomputable section
namespace MTC

/-- Every automorphism of a subfield extends to the ambient algebraically closed field.
Choose a transcendence basis, apply the automorphism to coefficients while
fixing the basis, and extend across the algebraic closure. -/
private theorem extend_subfield_automorphism {L : Type*} [Field L] [IsAlgClosed L]
    (K : Subfield L) (σ : K ≃+* K) :
    ∃ τ : L ≃+* L, ∀ x : K, τ (x : L) = (σ x : L) := by
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis K L
  let v : s → L := fun x => x
  let A := Algebra.adjoin K (Set.range v)
  let e : MvPolynomial s K ≃ₐ[K] A := hs.1.aevalEquiv
  let α : A ≃+* A := e.toRingEquiv.symm.trans
    ((MvPolynomial.mapEquiv s σ).trans e.toRingEquiv)
  let : IsAlgClosure A L := IsAlgClosed.isAlgClosure_of_transcendence_basis v hs
  let τ : L ≃+* L := IsAlgClosure.equivOfEquiv L L α
  refine ⟨τ, fun x => ?_⟩
  have he : α (algebraMap K A x) = algebraMap K A (σ x) := by
    apply e.symm.injective
    simp [α, e]
  simpa [he, Subfield.algebraMap_ofSubfield] using
    IsAlgClosure.equivOfEquiv_algebraMap L L α (algebraMap K A x)

end MTC

end

section

@[expose] public noncomputable section

variable {R K : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [Field K]

namespace MTC

/-- The final strict-inequality contradiction, including the inverse Galois
transport of the positive dimension ratio. Lemma 3.2 supplies `hrigidity`.
No assertion about all conjugates is assumed here. -/
theorem galois_dimension_contradiction {j : R →+* K} {δ δσ δτ f d : R}
    {σ : K ≃+* K} (hδ : 0 < δ) (hδσ : 0 < δσ) (hlt : δσ < δ)
    (hδτ : σ (j δτ) = j δ) (hσδ : σ (j δ) = j δσ) (hσf : σ (j f) = j d)
    (hratio : f * δτ = δ) (hf : 1 ≤ f) (hrigidity : f = |d|) : False := by
  have hreal : d * δ = δσ := j.injective <| by simpa [hδτ, hσδ, hσf] using congrArg (σ ∘ j) hratio
  nlinarith [abs_of_pos (show 0 < d by nlinarith)]

end MTC

namespace MTC

/-- The numerical witness supplied by a Galois-unit column. -/
abbrev HasGaloisDimensionWitness (j : R →+* K) (σ : K ≃+* K) (δ b : R) : Prop :=
  ∃ f d : R, σ (j f) = j d ∧ f * b = δ ∧ 1 ≤ f ∧ f = |d|

/-- If real conjugates are bounded above by δ and the centre/rigidity witness
exists for each strictly smaller conjugate, every conjugate equals δ. -/
theorem galois_fixed_of_smaller_conjugate_witness {j : R →+* K} (δ : R) (hδ : 0 < δ)
    (hConjugates : ∀ σ : K ≃+* K, ∃ a : R, 0 < a ∧ a ≤ δ ∧ σ (j δ) = j a)
    (hWitness : ∀ (σ : K ≃+* K) (a b : R), 0 < a → a < δ → 0 < b → σ (j δ) = j a →
      σ.symm (j δ) = j b → HasGaloisDimensionWitness j σ δ b) :
    ∀ σ : K ≃+* K, σ (j δ) = j δ := by
  intro σ
  obtain ⟨a, ha, hale, haeq⟩ := hConjugates σ
  obtain ⟨b, hb, _, hbeq⟩ := hConjugates σ.symm
  rcases lt_or_eq_of_le hale with halt | heq
  · obtain ⟨f, d, hσf, hratio, hf, hrigidity⟩ := hWitness σ a b ha halt hb haeq hbeq
    exact (galois_dimension_contradiction (j := j) (σ := σ) hδ ha halt
      (by rw [← hbeq, σ.apply_symm_apply])
      haeq hσf hratio hf hrigidity).elim
  · simpa [heq] using haeq

end MTC
end
end

/-! The final arithmetic descent for the frozen target, without a dimension
field or standard-input hypothesis. -/

@[expose] public noncomputable section
namespace MTC
universe v u
variable {R : Type*} [Field R] [Algebra R ℂ]
local notation "ι" => algebraMap R ℂ

/-- An algebraic integer in a complex subfield fixed by every complex automorphism is an integer. -/
theorem integral_eq_int_of_complex_galois_fixed {δ : R} (hδr : IsIntegral ℤ δ)
    (hfixed : ∀ τ : ℂ ≃+* ℂ, τ (ι δ) = ι δ) : ∃ z : ℤ, δ = z :=
  let hδ := (isIntegral_algebraMap_iff (R := ℤ) (A := R) (B := ℂ)).mpr hδr
  let K := separableClosure ℚ ℂ
  let x : K := ⟨ι δ, (minpoly.irreducible (hδ.tower_top (A := ℚ))).separable⟩
  let ⟨z, hz⟩ := MTC.Algebra.integer_of_galois_fixed (x := x)
    ((isIntegral_algebraMap_iff (R := ℤ) (A := K) (B := ℂ)).mp (by simpa [x] using hδ)) fun σ ↦ by
      obtain ⟨τ, hτ⟩ := extend_subfield_automorphism K.toSubfield σ.toRingEquiv
      exact Subtype.ext ((hτ x).symm.trans (hfixed τ))
  ⟨z, (algebraMap R ℂ).injective (by simpa [x] using congrArg (fun y : K ↦ (y : ℂ)) hz)⟩

end MTC
end

section
/-! Extract the numerical ingredients of the paper's witness from an actual
spherical category with positive FP dimensions and invertible S matrix. -/

@[expose] public noncomputable section
open CategoryTheory
open MTC.Modular (IsFPSpherical)
open scoped BigOperators
namespace MTC
universe v u

/-- A column satisfying the Galois-unit identity. -/
abbrev IsGaloisUnitColumn (Z : BraidedFusionCategory.{v,u})
    (p : MTC.CategoryTheory.Dimensions.PivotalStructure (C := Z.Obj)) (τ : ℂ ≃+* ℂ) (y : Fin (rank Z)) : Prop :=
  ∀ x, Modular.categoricalS Z p x y =
    Modular.simpleDimension Z p y * τ (Modular.simpleDimension Z p x)

variable (Z : BraidedFusionCategory.{v,u}) {p : MTC.CategoryTheory.Dimensions.PivotalStructure (C := Z.Obj)}
local notation "𝒮" => Modular.categoricalS Z p
local notation "𝒇" => fpSimple Z

/-- The Galois-unit label has dimension at least one, the Galois-unit column,
and the modular global-dimension identity. -/
theorem exists_modular_witness (hfp : IsFPSpherical Z p) (hdet : (𝒮).det ≠ 0)
    {δ : ℝ} (hglobal : globalDimension Z = (δ : ℂ) ^ 2) (σ : ℂ ≃+* ℂ) :
    ∃ y : Fin (rank Z), 1 ≤ 𝒇 y ∧ IsGaloisUnitColumn Z p σ.symm y ∧
      σ.symm ((δ : ℂ) ^ 2) = (δ : ℂ) ^ 2 / (𝒇 y : ℂ) ^ 2 :=
  let hreal := MTC.Center.Braid.realSimpleDimensions_of_fp hfp.2
  let ⟨act, hact⟩ := Modular.categoricalS_galois_action_of_invertibleS Z p hfp.1 hdet hreal
  let y := act σ.symm (unitIndex Z)
  let ⟨hcolumn, _, hG⟩ := Modular.galois_unit_properties (Modular.simpleDimension_ne_zero Z p)
    (Modular.globalDimension_ne_zero_of_invertibleS Z p hfp.1 hdet hreal)
    (Modular.simpleDimension_unit Z p) (Modular.categorical_global_eq_sum_squares Z p hfp.1)
    (Modular.categoricalS_symmetric Z p) (Modular.categoricalS_unit Z p)
    (Modular.categoricalS_square Z p hfp.1 hdet hreal) σ.symm y
    (fun x => hact σ.symm x (unitIndex Z))
  ⟨y, one_le_fpSimple y, by simpa only [IsGaloisUnitColumn, hfp.2] using hcolumn,
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

end MTC
end
end

section
/-! The FP fusion character is self-dual, so all its conjugates are real
and bounded. This gives global FP conjugate bounds without any spherical or
pseudo-unitary assumptions. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
open scoped BigOperators
namespace MTC
universe v u

section
variable {ι R K : Type*} [Fintype ι] [CommSemiring R] [CommSemiring K] [Algebra R K]
local notation "φ" => algebraMap R K

/-- A conjugate of a sum of squares is the sum of the squares of its conjugates. -/
theorem galois_sum_squares {d e : ι → R} (σ : K ≃+* K) (h : ∀ i, σ (φ (d i)) = φ (e i)) :
    σ (φ (∑ i, d i ^ 2)) = φ (∑ i, e i ^ 2) := by simp only [map_sum, map_pow, h]
end

variable {ι K : Type*} [Fintype ι] [CommSemiring K] [Algebra ℝ K]
local notation "φ" => algebraMap ℝ K

/-- A bounded conjugate sum of squares is positive when one conjugate is one. -/
theorem positive_galois_sum_squares {d e : ι → ℝ} (σ : K ≃+* K)
    (h : ∀ i, σ (φ (d i)) = φ (e i)) (hone : ∃ i, e i = 1)
    (hbound : ∑ i, e i ^ 2 ≤ ∑ i, d i ^ 2) :
    ∃ a : ℝ, 0 < a ∧ a ≤ ∑ i, d i ^ 2 ∧ σ (φ (∑ i, d i ^ 2)) = φ a :=
  ⟨∑ i, e i ^ 2, lt_of_lt_of_le zero_lt_one (MTC.CategoryTheory.Dimensions.global_sum_squares_one_le e hone),
    hbound, galois_sum_squares σ h⟩

variable (C : BraidedFusionCategory.{v,u}) (σ : ℂ ≃+* ℂ)

/-- Global FP dimension has positive, FP-bounded real conjugates. -/
theorem positive_bounded_conjugates_of_fp : ∃ a : ℝ, 0 < a ∧ a ≤ globalFPDimension C ∧
      σ (globalFPDimension C : ℂ) = (a : ℂ) :=
  let d : Fin (rank C) → ℝ := fun i ↦ (σ (fpSimple C i : ℂ)).re
  have hbound (i : Fin (rank C)) : |d i| ≤ fpSimple C i := by
    simp only [d, ← Real.norm_eq_abs, ← Complex.norm_real, fp_simple_galois_real]
    exact MTC.CategoryTheory.Dimensions.galois_character_norm_le_fpSimple (χ := fun i ↦ (fpSimple C i : ℂ))
      (i₀ := unitIndex C) (by simp [fpSimple_unit]) (fpSimple_isFusionMultiplicative C) σ i
  by
    change ∃ a : ℝ, 0 < a ∧ a ≤ ∑ i, fpSimple C i ^ 2 ∧
      σ ((algebraMap ℝ ℂ) (∑ i, fpSimple C i ^ 2)) = (algebraMap ℝ ℂ) a
    exact positive_galois_sum_squares σ (fun i ↦ (fp_simple_galois_real C σ i).symm)
      ⟨unitIndex C, by simp [fpSimple_unit]⟩
      (MTC.CategoryTheory.Dimensions.sum_sq_le_sum_sq_of_abs_le hbound)

end MTC
end
end

section
/-! The Galois-unit finite-image argument without `CenterInputs`. -/

@[expose] public noncomputable section
namespace MTC
universe v u

/-- The simple dimensions indexed by a set are integers. -/
abbrev HasIntegralSimpleDimensionsOn (Z : BraidedFusionCategory.{v,u})
    (p : MTC.CategoryTheory.Dimensions.PivotalStructure (C := Z.Obj)) (core : Set (Fin (rank Z))) : Prop :=
  ∀ x ∈ core, ∃ z : ℤ, Modular.simpleDimension Z p x = z

variable {Z : BraidedFusionCategory.{v,u}} {p : MTC.CategoryTheory.Dimensions.PivotalStructure (C := Z.Obj)}
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

end MTC
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
namespace MTC
universe v u

variable (C : BraidedFusionCategory.{v,u})
variable [RigidCategory (CategoryTheory.Center C.Obj)] [IsFusionCategory (CategoryTheory.Center C.Obj)]
local notation "𝒵ᶠ" => MTC.PropertyF.Reduction.bundledCenter C

/-- A modular actual centre with integral centralizer and finite braid-image
retracts forces the global Frobenius–Perron dimension to be integral. -/
theorem weaklyIntegral_of_actual_center (hF : HasPropertyF C.Obj)
    {p : MTC.CategoryTheory.Dimensions.PivotalStructure (C := 𝒵ᶠ.Obj)}
    {core generated : Set (Fin (rank 𝒵ᶠ))}
    (hfp : Modular.IsFPSpherical 𝒵ᶠ p) (hdet : (Modular.categoricalS 𝒵ᶠ p).det ≠ 0)
    (hglobal : globalDimension 𝒵ᶠ = (globalFPDimension C : ℂ) ^ 2)
    (hIntegral : HasIntegralSimpleDimensionsOn 𝒵ᶠ p core)
    (hDouble : Modular.sCentralizer 𝒵ᶠ p core ⊆ generated)
    (hProduct : ∀ y ∈ generated, MTC.Center.ProductRetract (simples 𝒵ᶠ y)) :
    WeaklyIntegral (globalFPDimension C) :=
  integral_eq_int_of_complex_galois_fixed
    (IsIntegral.sum _ fun i _ ↦ (fpSimple_isIntegral i).pow 2) <|
    galois_fixed_of_smaller_conjugate_witness (j := algebraMap ℝ ℂ) (globalFPDimension C)
      (lt_of_lt_of_le zero_lt_one (one_le_globalFPDimension C))
      (positive_bounded_conjugates_of_fp C) fun τ _ _ _ _ hb _ hτ ↦
        center_witness_of_categorical_modular_data 𝒵ᶠ hfp hdet
          (lt_of_lt_of_le zero_lt_one (one_le_globalFPDimension C)) hb hglobal τ hτ fun _ hColumn ↦
            propertyF_of_galois_column hIntegral hDouble
              (fun i hi ↦ MTC.Center.productRetract_propertyF (hProduct i hi) hF) hColumn

end MTC
end
end
