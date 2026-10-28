module
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.Data.Fintype.Lattice
public import Mathlib.Tactic
public import PropertyF.Ground.Fusion.SpectralIntegral
public import Mathlib.Analysis.Matrix.Spectrum
public import PropertyF.Ground.Fusion.Reciprocity
public import PropertyF.Ground.Cabling.Strands
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.LinearAlgebra.Eigenspace.Matrix

/-! Elementary uniqueness of a positive matrix eigenvector. -/

@[expose] public noncomputable section
open scoped BigOperators Matrix

namespace PropertyF.Ground

section
variable {k : Type*} [Field k] [LinearOrder k] [IsStrictOrderedRing k]
  {ι : Type*} [Fintype ι] {A : Matrix ι ι k} (hA : ∀ i j, 0 < A i j)
include hA

/-- For a strictly positive matrix, the eigenspace of any strictly positive
eigenvector is one-dimensional. No spectral theorem is assumed. -/
theorem positive_matrix_eigenspace_unique [Nonempty ι]
    {x y : ι → k} (hx : ∀ i, 0 < x i) {d : k}
    (hxe : A *ᵥ x = d • x) (hye : A *ᵥ y = d • y) :
    ∃ c : k, y = c • x := by
  obtain ⟨i, _, hmin⟩ := Finset.exists_min_image Finset.univ (fun j => y j / x j)
    Finset.univ_nonempty
  let c := y i / x i
  have hnonneg (j : ι) : 0 ≤ y j - c * x j :=
    sub_nonneg.mpr ((le_div_iff₀ (hx j)).mp (hmin j (Finset.mem_univ j)))
  have hsum : ∑ j, A i j * (y j - c * x j) = 0 := by
    have he : A *ᵥ (y - c • x) = d • (y - c • x) := by
      rw [Matrix.mulVec_sub, Matrix.mulVec_smul, hye, hxe, smul_sub]
      simp only [smul_smul, mul_comm]
    simpa only [Matrix.mulVec, dotProduct, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
      show y i - c * x i = 0 from sub_eq_zero.mpr (div_mul_cancel₀ _ (ne_of_gt (hx i))).symm,
      mul_zero] using congrFun he i
  refine ⟨c, funext fun j ↦ sub_eq_zero.mp ?_⟩
  exact (mul_eq_zero.mp ((Finset.sum_eq_zero_iff_of_nonneg
      (fun j _ => mul_nonneg (hA i j).le (hnonneg j))).mp hsum j
        (Finset.mem_univ j))).resolve_left (ne_of_gt (hA i j))

/-- Positive eigenvectors of a positive symmetric matrix agree when normalized
at the same coordinate, even when their eigenvalues are initially different. -/
theorem positive_symmetric_eigenvector_unique (hsym : Aᵀ = A)
    {f g : ι → k} (hfpos : ∀ i, 0 < f i) (hgpos : ∀ i, 0 < g i)
    {i₀ : ι} (hfunit : f i₀ = 1) (hgunit : g i₀ = 1)
    {a b : k} (hfe : A *ᵥ f = a • f) (hge : A *ᵥ g = b • g) : f = g := by
  let : Nonempty ι := ⟨i₀⟩
  have hdot : f ⬝ᵥ A *ᵥ g = g ⬝ᵥ A *ᵥ f := by
    simpa [hsym] using Matrix.dotProduct_transpose_mulVec A f g
  rw [hfe, hge, dotProduct_smul, dotProduct_smul, dotProduct_comm g f] at hdot
  obtain ⟨c, hc⟩ := positive_matrix_eigenspace_unique hA hfpos hfe (by
    rw [mul_right_cancel₀ (ne_of_gt (Finset.sum_pos
      (fun i _ ↦ mul_pos (hfpos i) (hgpos i)) Finset.univ_nonempty)) hdot.symm]
    exact hge)
  rw [hc, show c = 1 from by simpa [hfunit, hgunit] using (congrFun hc i₀).symm, one_smul]

end

/-- A function on simple labels is multiplicative for the fusion rules. -/
abbrev IsFusionMultiplicative {R : Type*} [Semiring R]
    (C : BraidedFusionCategory) (χ : Fin (rank C) → R) : Prop :=
  ∀ i j, χ i * χ j = ∑ k, (fusionCoeff C i j k : R) * χ k

end PropertyF.Ground

end

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
open scoped BigOperators Matrix Matrix.Norms.Operator ENNReal
namespace PropertyF.Ground.Dimensions

variable (C : BraidedFusionCategory)

variable {C} in
/-- Each value of any nonzero fusion-ring character is bounded in absolute value
by the spectral-radius FP dimension. No positivity of the character is needed. -/
theorem character_norm_le_fpSimple
    {χ : Fin (rank C) → ℂ} {i₀ : Fin (rank C)} (hχ : χ i₀ ≠ 0)
    (hchar : IsFusionMultiplicative C χ) (i : Fin (rank C)) :
    ‖χ i‖ ≤ fpSimple C i := by
  let A := (fusionMatrix C i)ᵀ
  have hz : χ i ∈ spectrum ℂ A := by
    rw [← Matrix.spectrum_toLin']
    exact (Module.End.hasEigenvalue_of_hasEigenvector
      ⟨Module.End.mem_eigenspace_iff.mpr (by
        ext j
        change (∑ k, (fusionCoeff C i j k : ℂ) * χ k) = χ i * χ j
        exact (hchar i j).symm), fun h ↦ hχ (congrFun h i₀)⟩).mem_spectrum
  simpa [fpSimple, A, Matrix.spectralRadius_transpose] using
    ENNReal.toReal_mono
      (ne_of_lt (lt_of_le_of_lt (spectralRadius_le_nnnorm (𝕜 := ℂ) A) (by simp)))
      (show (‖χ i‖₊ : ℝ≥0∞) ≤ spectralRadius ℂ A from by
        rw [spectralRadius_eq_of_unital]
        exact le_iSup_of_le (χ i) (le_iSup_of_le hz le_rfl))

variable {C} in
/-- Every complex field conjugate of a fusion character obeys the same FP
bound, because field automorphisms preserve the integer fusion coefficients. -/
theorem galois_character_norm_le_fpSimple
    {χ : Fin (rank C) → ℂ} {i₀ : Fin (rank C)} (hχ : χ i₀ ≠ 0)
    (hchar : IsFusionMultiplicative C χ) (σ : ℂ ≃+* ℂ) (i : Fin (rank C)) :
    ‖σ (χ i)‖ ≤ fpSimple C i :=
  character_norm_le_fpSimple (i₀ := i₀)
    ((map_ne_zero σ).2 hχ) (fun j k ↦ by simpa using congrArg σ (hchar j k)) i

end PropertyF.Ground.Dimensions

end

/-! Perron theory for positive symmetric real matrices. -/

@[expose] public noncomputable section
open scoped BigOperators Matrix InnerProductSpace
open WithLp

namespace PropertyF.Ground

variable {ι : Type*}

/-- The coordinatewise absolute value of a real Euclidean vector. -/
def euclideanAbs (x : EuclideanSpace ℝ ι) : EuclideanSpace ℝ ι :=
  toLp 2 (fun i => |x i|)

variable [Fintype ι]

theorem euclideanAbs_norm (x : EuclideanSpace ℝ ι) :
    ‖euclideanAbs x‖ = ‖x‖ :=
  (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (by
    simp [EuclideanSpace.real_norm_sq_eq, euclideanAbs])

/-- Replacing coordinates by absolute values cannot decrease the quadratic
form of a matrix with nonnegative entries. -/
theorem quadratic_le_abs
    {k : Type*} [CommRing k] [LinearOrder k] [IsStrictOrderedRing k]
    {A : Matrix ι ι k} (hA : ∀ i j, 0 ≤ A i j) (x : ι → k) :
    ∑ i, ∑ j, x i * A i j * x j ≤ ∑ i, ∑ j, |x i| * A i j * |x j| :=
  Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun j _ ↦ by
    simpa [abs_mul, mul_assoc, mul_comm, mul_left_comm] using
      (mul_le_mul_of_nonneg_left (le_abs_self (x i * x j)) (hA i j))

theorem matrix_quadratic_form [DecidableEq ι]
    (A : Matrix ι ι ℝ) (x : EuclideanSpace ℝ ι) :
    (Matrix.toEuclideanLin A).toContinuousLinearMap.reApplyInnerSelf x =
      ∑ i, ∑ j, x i * A i j * x j := by
  rw [Finset.sum_comm]
  simp [ContinuousLinearMap.reApplyInnerSelf, EuclideanSpace.inner_eq_star_dotProduct,
    Matrix.toLpLin_apply, Matrix.dot_mulVec_eq_sum_sum]

/-- A nonnegative eigenvector of a positive matrix is positive in every coordinate
if it has a positive coordinate. -/
theorem positive_matrix_eigenvector_pos {k : Type*} [Semiring k] [LinearOrder k]
    [IsStrictOrderedRing k] {A : Matrix ι ι k} (hpos : ∀ i j, 0 < A i j) {v : ι → k}
    (hnonneg : ∀ i, 0 ≤ v i) (hpositive : ∃ i, 0 < v i)
    {d : k} (heigen : A *ᵥ v = d • v) : ∀ i, 0 < v i :=
  hpositive.elim fun j hj i ↦ by
    have hv : 0 < d * v i := by
      change 0 < (d • v) i
      rw [← heigen]
      exact Finset.sum_pos' (fun k _ => mul_nonneg (hpos i k).le (hnonneg k))
        ⟨j, Finset.mem_univ _, mul_pos (hpos i j) hj⟩
    exact lt_of_le_of_ne (hnonneg i) (Ne.symm (right_ne_zero_of_mul (ne_of_gt hv)))

variable [DecidableEq ι] [Nonempty ι]

/-- A nonnegative symmetric real matrix has a nonnegative eigenvector with a
positive coordinate. -/
theorem nonneg_symmetric_matrix_has_nonneg_eigenvector {A : Matrix ι ι ℝ}
    (hsym : A.IsHermitian) (hA : ∀ i j, 0 ≤ A i j) :
    ∃ (d : ℝ) (v : ι → ℝ), (∀ i, 0 ≤ v i) ∧ (∃ i, 0 < v i) ∧ A *ᵥ v = d • v := by
  let T : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι :=
    (Matrix.toEuclideanLin A).toContinuousLinearMap
  have hself : IsSelfAdjoint T :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
      (Matrix.isSymmetric_toEuclideanLin_iff.mpr hsym)
  obtain ⟨z, hz⟩ : ∃ z : EuclideanSpace ℝ ι, z ≠ 0 := exists_ne 0
  obtain ⟨x, hxmem, hxmax⟩ := (isCompact_sphere (0 : EuclideanSpace ℝ ι) ‖z‖).exists_isMaxOn
    ⟨z, by simp⟩
    T.reApplyInnerSelf_continuous.continuousOn
  let y := euclideanAbs x
  have hynorm : ‖y‖ = ‖z‖ := by
    simpa [y, euclideanAbs_norm] using hxmem
  have hyne : y ≠ 0 := norm_ne_zero_iff.mp (by simpa [hynorm] using norm_ne_zero_iff.mpr hz)
  have hynonneg (i : ι) : 0 ≤ y i := abs_nonneg _
  have hyexists : ∃ i, 0 < y i := by
    obtain ⟨i, hi⟩ := Function.ne_iff.mp ((not_congr (WithLp.ext_iff 2)).mp hyne)
    exact ⟨i, lt_of_le_of_ne (hynonneg i) (Ne.symm hi)⟩
  have hyquad : T.reApplyInnerSelf x ≤ T.reApplyInnerSelf y := by
    simpa [T, matrix_quadratic_form, y, euclideanAbs] using quadratic_le_abs hA (fun i ↦ x i)
  have hymax : IsMaxOn T.reApplyInnerSelf (Metric.sphere 0 ‖y‖) y :=
    fun _ hw ↦ (hxmax (by simpa [hynorm] using hw)).trans hyquad
  have heigen := hself.eq_smul_self_of_isLocalExtrOn (Or.inr hymax.isLocalMaxOn)
  let d := T.rayleighQuotient y
  refine ⟨d, fun i => y i, hynonneg, hyexists, ?_⟩
  simpa [T, d, Matrix.toLpLin_apply] using (congrArg ofLp heigen)

/-- A strictly positive symmetric real matrix has a strictly positive eigenvector. -/
theorem positive_symmetric_matrix_has_positive_eigenvector {A : Matrix ι ι ℝ}
    (hsym : A.IsHermitian) (hpos : ∀ i j, 0 < A i j) :
    ∃ (d : ℝ) (v : ι → ℝ), (∀ i, 0 < v i) ∧ A *ᵥ v = d • v :=
  (nonneg_symmetric_matrix_has_nonneg_eigenvector hsym (fun i j => (hpos i j).le)).imp
    fun _ ⟨v, hv, hvpos, heigen⟩ ↦
      ⟨v, positive_matrix_eigenvector_pos hpos hv hvpos heigen, heigen⟩

end PropertyF.Ground

end

/-! The symmetric total fusion matrix. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open scoped BigOperators

namespace PropertyF.Ground

variable (D : BraidedFusionCategory)
attribute [local instance] Abelian.hasFiniteBiproducts
local instance (i : Fin (rank D)) : Simple (simples D i) := simples_simple D i

/-- Sum of all simple fusion matrices, over the real numbers. -/
def totalFusionMatrix (D : BraidedFusionCategory) :
    Matrix (Fin (rank D)) (Fin (rank D)) ℝ :=
  fun j k => ∑ i, (fusionCoeff D i k j : ℝ)

/-- Duality and Frobenius reciprocity make the total fusion matrix symmetric. -/
theorem totalFusionMatrix_symmetric (j k : Fin (rank D)) :
    totalFusionMatrix D j k = totalFusionMatrix D k j := by
  simpa only [totalFusionMatrix, ← fusionCoeff_dual_symmetry, show ⇑(dualEquiv D) = dualIndex D from rfl] using
    Equiv.sum_comp (dualEquiv D) (fun i ↦ (fusionCoeff D i j k : ℝ))

/-- The total fusion matrix is strictly positive in every entry. -/
theorem totalFusionMatrix_pos (j k : Fin (rank D)) :
    0 < totalFusionMatrix D j k := by
  let : Simple (ᘁ(simples D k)) := simple_leftDual (simples D k)
  obtain ⟨s, r, hsr⟩ := unit_retract_leftDual_tensor (simples D j)
  let : (tensorLeft (simples D j)).Faithful :=
    PropertyF.tensorLeft_faithful_of_unit_retract s r hsr
  let Y : D.Obj := simples D j ⊗ (ᘁ(simples D k))
  obtain ⟨i, hm⟩ := exists_positive_multiplicity (simples_decompose D Y)
    (fun _ ↦ IsFusionCategory.hom_finite _ _) (fun h ↦ id_nonzero (ᘁ(simples D k))
      ((tensorLeft (simples D j)).map_eq_zero_iff.mp
        (by simpa [Y] using (IsZero.iff_id_eq_zero Y).mp h)))
  exact Finset.sum_pos' (fun _ _ => Nat.cast_nonneg _)
    ⟨i, Finset.mem_univ _, Nat.cast_pos.mpr (by simpa only [fusionCoeff_reciprocity] using hm)⟩

end PropertyF.Ground

end

/-! Constructing the positive fusion character from the total matrix. -/

@[expose] public noncomputable section
open scoped BigOperators Matrix

namespace PropertyF.Ground

variable (D : BraidedFusionCategory)

/-- The transpose convention: its rows encode the fusion equations. -/
def characterMatrix (D : BraidedFusionCategory) (i : Fin (rank D)) :
    Matrix (Fin (rank D)) (Fin (rank D)) ℝ :=
  fun j k => fusionCoeff D i j k

theorem characterMatrix_commute (i j : Fin (rank D)) :
    Commute (characterMatrix D i) (characterMatrix D j) :=
  Matrix.ext fun a b ↦ by simp only [Matrix.mul_apply, characterMatrix]; exact_mod_cast
    (fusionCoeff_assoc j i a b).trans (by simpa only [fusionCoeff_comm D j i] using
      (fusionCoeff_assoc i j a b).symm)

theorem totalFusionMatrix_eq_sum_characterMatrix :
    totalFusionMatrix D = ∑ i, characterMatrix D i :=
  Matrix.ext fun j k ↦ by
    simpa [totalFusionMatrix, characterMatrix, Matrix.sum_apply] using totalFusionMatrix_symmetric D j k

/-- The total matrix has a strictly positive common eigenvector for all
fusion matrices. -/
theorem exists_positive_common_eigenvector :
    ∃ (v : Fin (rank D) → ℝ), (∀ j, 0 < v j) ∧
      ∀ i, ∃ d : ℝ, characterMatrix D i *ᵥ v = d • v :=
  let : Nonempty (Fin (rank D)) := ⟨unitIndex D⟩
  (positive_symmetric_matrix_has_positive_eigenvector
    (Matrix.isHermitian_iff_isSymm.mpr (Matrix.IsSymm.ext fun j k ↦
      totalFusionMatrix_symmetric D k j)) (totalFusionMatrix_pos D)).elim fun _ ⟨v, hvpos, hve⟩ ↦
    ⟨v, hvpos, fun i ↦ positive_matrix_eigenspace_unique (totalFusionMatrix_pos D) hvpos hve (by
      rw [Matrix.mulVec_mulVec,
        (show Commute (totalFusionMatrix D) (characterMatrix D i) from
          (totalFusionMatrix_eq_sum_characterMatrix D).symm ▸
            Commute.sum_left _ _ _ fun j _ ↦ characterMatrix_commute D j i).eq,
        ← Matrix.mulVec_mulVec, hve, Matrix.mulVec_smul])⟩

/-- A positive normalized character exists for the actual fusion rules. -/
theorem exists_positive_character :
    ∃ f : Fin (rank D) → ℝ,
      (∀ i, 0 < f i) ∧ f (unitIndex D) = 1 ∧
      IsFusionMultiplicative D f := by
  obtain ⟨v, hvpos, hve⟩ := exists_positive_common_eigenvector D
  let f : Fin (rank D) → ℝ := fun i => v i / v (unitIndex D)
  have hunit : v (unitIndex D) ≠ 0 := ne_of_gt (hvpos _)
  refine ⟨f, fun i => div_pos (hvpos i) (hvpos _), ?_, ?_⟩
  · exact div_self hunit
  · intro i j
    obtain ⟨d, hd⟩ := hve i
    have hscalar : d = f i := by
      apply (eq_div_iff hunit).mpr
      simpa [Matrix.mulVec, dotProduct, characterMatrix,
        fusionCoeff_comm D i (unitIndex D), fusionCoeff_unit] using
          (congrFun hd (unitIndex D)).symm
    have hrow := congrFun hd j
    simp only [Matrix.mulVec, dotProduct, characterMatrix, Pi.smul_apply, smul_eq_mul] at hrow
    rw [hscalar] at hrow
    calc
      f i * f j = (∑ k, (fusionCoeff D i j k : ℝ) * v k) / v (unitIndex D) := by
        rw [hrow]
        dsimp [f]
        ring
      _ = ∑ k, (fusionCoeff D i j k : ℝ) * f k := by
        simp [f, Finset.sum_div, mul_div_assoc]

variable {D} in
theorem character_total_eigenvector
    {f : Fin (rank D) → ℝ}
    (hf : IsFusionMultiplicative D f) :
    totalFusionMatrix D *ᵥ f = (∑ i, f i) • f := by
  rw [totalFusionMatrix_eq_sum_characterMatrix, Matrix.sum_mulVec]
  ext j
  simp only [Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul, Finset.sum_mul, Matrix.mulVec, dotProduct, characterMatrix,
    ← hf]

/-- The unique positive normalized character of the fusion rules. -/
def fpCharacter (D : BraidedFusionCategory) : Fin (rank D) → ℝ :=
  Classical.choose (exists_positive_character D)

variable {D} in
theorem fpCharacter_pos (i : Fin (rank D)) :
    0 < fpCharacter D i := (Classical.choose_spec (exists_positive_character D)).1 i

variable {D} in
theorem fpCharacter_mul (i j : Fin (rank D)) :
    fpCharacter D i * fpCharacter D j =
      ∑ k, (fusionCoeff D i j k : ℝ) * fpCharacter D k :=
  (Classical.choose_spec (exists_positive_character D)).2.2 i j

end PropertyF.Ground

end

/-! Weighted matrix bounds and spectral estimates. -/

@[expose] public noncomputable section
open scoped BigOperators
namespace PropertyF.Ground.Dimensions

/-- A matrix dominated entrywise by a nonnegative matrix cannot have an
eigenvalue larger than the latter's positive eigenvalue. -/
theorem weighted_eigenvalue_bound {K : Type*} [NormedRing K] [NormMulClass K]
    {ι : Type*} [Fintype ι] {N : ι → ι → ℝ}
    {T : ι → ι → K} {f : ι → ℝ} {F : ℝ} {v : ι → K} {z : K}
    {i₀ : ι} (hv : v i₀ ≠ 0) (hf : ∀ i, 0 < f i)
    (hN : ∀ i j, 0 ≤ N i j) (hdom : ∀ i j, ‖T i j‖ ≤ N i j)
    (hfp : ∀ i, ∑ j, N i j * f j = F * f i)
    (heig : ∀ i, ∑ j, T i j * v j = z * v i) :
    ‖z‖ ≤ F := by
  obtain ⟨i, _, hmax⟩ := Finset.exists_max_image Finset.univ
    (fun j => ‖v j‖ / f j) ⟨i₀, Finset.mem_univ _⟩
  let r := ‖v i‖ / f i
  have hvi : 0 < ‖v i‖ := (div_pos_iff_of_pos_right (hf i)).1 <|
    lt_of_lt_of_le (div_pos (norm_pos_iff.mpr hv) (hf i₀)) (hmax i₀ (Finset.mem_univ _))
  apply le_of_mul_le_mul_right _ hvi
  calc
    _ = ‖∑ j, T i j * v j‖ := by rw [heig i, norm_mul]
    _ ≤ ∑ j, ‖T i j * v j‖ := by simpa using norm_sum_le Finset.univ (fun j ↦ T i j * v j)
    _ ≤ ∑ j, N i j * (r * f j) := Finset.sum_le_sum fun j _ ↦ by
      rw [norm_mul]
      exact mul_le_mul (hdom i j) ((div_le_iff₀ (hf j)).1 (hmax j (Finset.mem_univ _)))
        (norm_nonneg _) (hN i j)
    _ = r * (∑ j, N i j * f j) := by simp only [Finset.mul_sum, mul_left_comm]
    _ = F * ‖v i‖ := by
      rw [hfp i, mul_left_comm, show r * f i = ‖v i‖ from
        div_mul_cancel₀ _ (ne_of_gt (hf i))]

end PropertyF.Ground.Dimensions

end

/-! Spectral bounds from a positive eigenvector. -/

@[expose] public noncomputable section
open scoped BigOperators Matrix

namespace PropertyF.Ground

/-- A positive real eigenvector bounds the modulus of every complex eigenvalue
of a nonnegative real matrix. -/
theorem complex_eigenvalue_le_positive_eigenvalue {ι : Type*} [Fintype ι]
    {A : Matrix ι ι ℝ} {w : ι → ℝ} {d : ℝ} {z : ℂ} {v : ι → ℂ}
    (hwe : A *ᵥ w = d • w) (hve : A.map Complex.ofRealHom *ᵥ v = z • v)
    (hA : ∀ i j, 0 ≤ A i j) (hw : ∀ i, 0 < w i) (hv : v ≠ 0) : ‖z‖ ≤ d :=
  (Function.ne_iff.mp hv).elim fun _ hi ↦
    Dimensions.weighted_eigenvalue_bound (T := fun i j ↦ (A i j : ℂ)) hi hw hA
      (fun i j ↦ by simp [Complex.norm_real, abs_of_nonneg (hA i j)])
      (fun i ↦ by simpa [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] using congrFun hwe i)
      (fun i ↦ by simpa [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] using congrFun hve i)

end PropertyF.Ground

end

/-! Agreement of the positive character with the target's spectral radius. -/

@[expose] public noncomputable section
open scoped BigOperators Matrix Matrix.Norms.Operator

namespace PropertyF.Ground

variable (D : BraidedFusionCategory)

theorem fpCharacter_le_fpSimple (i : Fin (rank D)) :
    fpCharacter D i ≤ fpSimple D i := by
  simpa [Complex.norm_real, abs_of_pos (fpCharacter_pos i)] using
    (Dimensions.character_norm_le_fpSimple (χ := fun j ↦ (fpCharacter D j : ℂ))
      (i₀ := unitIndex D) (Complex.ofReal_ne_zero.mpr (ne_of_gt (fpCharacter_pos (unitIndex D))))
      (fun j k ↦ by
        dsimp
        exact_mod_cast fpCharacter_mul j k) i)

theorem fpSimple_le_fpCharacter (i : Fin (rank D)) :
    fpSimple D i ≤ fpCharacter D i := by
  let : Nonempty (Fin (rank D)) := ⟨unitIndex D⟩
  let A := characterMatrix D i
  let B := A.map Complex.ofRealHom
  have hB : B = (fusionMatrix D i)ᵀ := Matrix.ext fun j k ↦ by
    change (((fusionCoeff D i j k : ℝ) : ℂ)) = _
    simp [fusionMatrix, fusionCoeff]
  obtain ⟨z, hz, hzmax⟩ := spectrum.exists_nnnorm_eq_spectralRadius B
  obtain ⟨v, hv⟩ := (Module.End.hasEigenvalue_iff_mem_spectrum.mpr
    (show z ∈ spectrum ℂ B.toLin' from by simpa using hz)).exists_hasEigenvector
  simpa only [fpSimple, ← Matrix.spectralRadius_transpose (fusionMatrix D i), ← hB,
    ← hzmax, ENNReal.coe_toReal, coe_nnnorm] using
      complex_eigenvalue_le_positive_eigenvalue
        (show A *ᵥ fpCharacter D = fpCharacter D i • fpCharacter D from by
          ext j
          change (∑ k, (fusionCoeff D i j k : ℝ) * fpCharacter D k) = _
          exact (fpCharacter_mul i j).symm)
        (show A.map Complex.ofRealHom *ᵥ v = z • v from by
          simpa [B, Matrix.toLin'_apply] using hv.apply_eq_smul)
        (fun j k => Nat.cast_nonneg _) (fpCharacter_pos) hv.2

/-- The target spectral-radius FP dimension is the unique positive character. -/
theorem fpSimple_eq_fpCharacter (i : Fin (rank D)) :
    fpSimple D i = fpCharacter D i :=
  le_antisymm (fpSimple_le_fpCharacter D i) (fpCharacter_le_fpSimple D i)

theorem fpSimple_pos (i : Fin (rank D)) :
    0 < fpSimple D i := (fpSimple_eq_fpCharacter D i).symm ▸ fpCharacter_pos i

theorem fpSimple_mul (i j : Fin (rank D)) :
    fpSimple D i * fpSimple D j =
      ∑ k, (fusionCoeff D i j k : ℝ) * fpSimple D k :=
  by simp only [fpSimple_eq_fpCharacter, fpCharacter_mul]

/-- FP dimensions form a complex-valued fusion character. -/
theorem fpSimple_isFusionMultiplicative :
    IsFusionMultiplicative D (fun i ↦ (fpSimple D i : ℂ)) :=
  fun i j ↦ by
    dsimp
    exact_mod_cast fpSimple_mul D i j

variable {D} in
/-- Dual simple objects have the same FP dimension. -/
theorem fpSimple_dual (i : Fin (rank D)) :
    fpSimple D (dualIndex D i) = fpSimple D i := by
  simp only [fpSimple, show fusionMatrix D (dualIndex D i) = (fusionMatrix D i)ᵀ from
    Matrix.ext fun j k ↦ congrArg (fun n : ℕ ↦ (n : ℂ)) (fusionCoeff_dual_symmetry D i k j).symm,
    Matrix.spectralRadius_transpose]

variable {D} in
/-- Every simple has FP dimension at least one. -/
theorem one_le_fpSimple (i : Fin (rank D)) :
    1 ≤ fpSimple D i := (one_le_sq_iff₀ (fpSimple_pos D i).le).mp <| by
  simpa only [fusionCoeff_dual_unit, Nat.cast_one, fpSimple_unit, one_mul,
    ← fpSimple_mul, fpSimple_dual, ← pow_two, one_pow] using
    (Finset.single_le_sum
      (f := fun k => (fusionCoeff D i (dualIndex D i) k : ℝ) * fpSimple D k)
      (fun k _ => mul_nonneg (Nat.cast_nonneg _) (fpSimple_pos D k).le)
      (Finset.mem_univ (unitIndex D)))

end PropertyF.Ground

end
