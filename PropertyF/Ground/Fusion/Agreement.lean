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

/-- For a strictly positive matrix, the eigenspace of any strictly positive
eigenvector is one-dimensional. No spectral theorem is assumed. -/
theorem positive_matrix_eigenspace_unique {ι : Type*} [Fintype ι] [Nonempty ι]
    {A : Matrix ι ι ℝ} (hA : ∀ i j, 0 < A i j)
    {x y : ι → ℝ} (hx : ∀ i, 0 < x i) {d : ℝ}
    (hxe : A *ᵥ x = d • x) (hye : A *ᵥ y = d • y) :
    ∃ c : ℝ, y = c • x := by
  classical
  obtain ⟨i, _, hmin⟩ := Finset.exists_min_image Finset.univ (fun j => y j / x j)
    Finset.univ_nonempty
  let c := y i / x i
  have hnonneg (j : ι) : 0 ≤ y j - c * x j :=
    sub_nonneg.mpr ((le_div_iff₀ (hx j)).mp (hmin j (Finset.mem_univ j)))
  have hzero : y i - c * x i = 0 := by
    simp [c, div_mul_cancel₀ _ (ne_of_gt (hx i))]
  have hsum : ∑ j, A i j * (y j - c * x j) = 0 := by
    have ex := congrFun hxe i
    have ey := congrFun hye i
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at ex ey
    calc
      _ = (∑ j, A i j * y j) - c * (∑ j, A i j * x j) := by
        simp only [mul_sub, Finset.sum_sub_distrib, Finset.mul_sum, mul_left_comm]
      _ = d * (y i - c * x i) := by rw [ex, ey]; ring
      _ = 0 := by rw [hzero, mul_zero]
  have hall (j : ι) : y j - c * x j = 0 :=
    (mul_eq_zero.mp ((Finset.sum_eq_zero_iff_of_nonneg
      (fun j _ => mul_nonneg (hA i j).le (hnonneg j))).mp hsum j
        (Finset.mem_univ j))).resolve_left (ne_of_gt (hA i j))
  refine ⟨c, ?_⟩
  funext j
  simp only [Pi.smul_apply, smul_eq_mul]
  linarith [hall j]

/-- A function on simple labels is multiplicative for the fusion rules. -/
abbrev IsFusionMultiplicative (C : BraidedFusionCategory) (χ : Fin (rank C) → ℂ) : Prop :=
  ∀ i j, χ i * χ j = ∑ k, (fusionCoeff C i j k : ℂ) * χ k

end PropertyF.Ground

end

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
open scoped BigOperators Matrix Matrix.Norms.Operator ENNReal
namespace PropertyF.Ground.Dimensions

/-- Each value of any nonzero fusion-ring character is bounded in absolute value
by the spectral-radius FP dimension. No positivity of the character is needed. -/
theorem character_norm_le_fpSimple (C : BraidedFusionCategory)
    {χ : Fin (rank C) → ℂ} {i₀ : Fin (rank C)} (hχ : χ i₀ ≠ 0)
    (hchar : IsFusionMultiplicative C χ) (i : Fin (rank C)) :
    ‖χ i‖ ≤ fpSimple C i := by
  classical
  let A := (fusionMatrix C i)ᵀ
  have heigen : A *ᵥ χ = χ i • χ := by
    ext j
    change (∑ k, (fusionCoeff C i j k : ℂ) * χ k) = χ i * χ j
    exact (hchar i j).symm
  have hzero : (Matrix.scalar (Fin (rank C)) (χ i) - A) *ᵥ χ = 0 := by
    rw [Matrix.sub_mulVec, heigen]
    ext j
    simp [Matrix.scalar_apply]
  have hdet : (Matrix.scalar (Fin (rank C)) (χ i) - A).det = 0 :=
    Matrix.det_eq_zero_of_mulVec_eq_zero_of_mem_nonZeroDivisors hzero
      (mem_nonZeroDivisors_of_ne_zero hχ)
  have hz : χ i ∈ spectrum ℂ A := by
    apply Matrix.mem_spectrum_iff_isRoot_charpoly.mpr
    change Polynomial.eval (χ i) A.charpoly = 0
    rw [Matrix.eval_charpoly]
    exact hdet
  have hle : (‖χ i‖₊ : ℝ≥0∞) ≤ spectralRadius ℂ A := by
    rw [spectralRadius_eq_of_unital]
    exact le_iSup_of_le (χ i) (le_iSup_of_le hz le_rfl)
  have htop : spectralRadius ℂ A ≠ ⊤ := by
    exact ne_of_lt (lt_of_le_of_lt (spectralRadius_le_nnnorm (𝕜 := ℂ) A) (by simp))
  simpa [fpSimple, A, Matrix.spectralRadius_transpose] using (ENNReal.toReal_mono htop hle)

/-- Every complex field conjugate of a fusion character obeys the same FP
bound, because field automorphisms preserve the integer fusion coefficients. -/
theorem galois_character_norm_le_fpSimple (C : BraidedFusionCategory)
    {χ : Fin (rank C) → ℂ} {i₀ : Fin (rank C)} (hχ : χ i₀ ≠ 0)
    (hchar : IsFusionMultiplicative C χ)
    (σ : ℂ ≃+* ℂ) (i : Fin (rank C)) :
    ‖σ (χ i)‖ ≤ fpSimple C i := by
  apply character_norm_le_fpSimple C (χ := fun j => σ (χ j)) (i₀ := i₀)
  · exact (map_ne_zero σ).2 hχ
  · intro j k
    simpa using congrArg σ (hchar j k)

end PropertyF.Ground.Dimensions

end

/-! Perron theory for positive symmetric real matrices. -/

@[expose] public noncomputable section
open scoped BigOperators Matrix InnerProductSpace
open WithLp

namespace PropertyF.Ground

/-- The coordinatewise absolute value of a real Euclidean vector. -/
def euclideanAbs {ι : Type*} (x : EuclideanSpace ℝ ι) : EuclideanSpace ℝ ι :=
  toLp 2 (fun i => |x i|)

theorem euclideanAbs_norm {ι : Type*} [Fintype ι] (x : EuclideanSpace ℝ ι) :
    ‖euclideanAbs x‖ = ‖x‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp [EuclideanSpace.real_norm_sq_eq, euclideanAbs]

/-- Replacing coordinates by absolute values cannot decrease the quadratic
form of a matrix with nonnegative entries. -/
theorem quadratic_le_abs {ι : Type*} [Fintype ι]
    {A : Matrix ι ι ℝ} (hA : ∀ i j, 0 ≤ A i j) (x : ι → ℝ) :
    ∑ i, ∑ j, x i * A i j * x j ≤
      ∑ i, ∑ j, |x i| * A i j * |x j| := by
  refine Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun j _ ↦ ?_
  simpa [abs_mul, mul_assoc, mul_comm, mul_left_comm] using
    (mul_le_mul_of_nonneg_left (le_abs_self (x i * x j)) (hA i j))

theorem matrix_quadratic_form {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (x : EuclideanSpace ℝ ι) :
    (Matrix.toEuclideanLin A).toContinuousLinearMap.reApplyInnerSelf x =
      ∑ i, ∑ j, x i * A i j * x j := by
  simp [ContinuousLinearMap.reApplyInnerSelf, EuclideanSpace.inner_eq_star_dotProduct,
    Matrix.toLpLin_apply, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc,
    mul_comm, mul_left_comm]

/-- A nonnegative eigenvector of a positive matrix is positive in every coordinate
if it has a positive coordinate. -/
theorem positive_matrix_eigenvector_pos {ι : Type*} [Fintype ι]
    {A : Matrix ι ι ℝ} (hpos : ∀ i j, 0 < A i j) {v : ι → ℝ}
    (hnonneg : ∀ i, 0 ≤ v i) (hpositive : ∃ i, 0 < v i)
    {d : ℝ} (heigen : A *ᵥ v = d • v) : ∀ i, 0 < v i := by
  classical
  obtain ⟨j, hj⟩ := hpositive
  intro i
  have hsum : 0 < ∑ k, A i k * v k :=
    Finset.sum_pos' (fun k _ => mul_nonneg (hpos i k).le (hnonneg k))
      ⟨j, Finset.mem_univ _, mul_pos (hpos i j) hj⟩
  have hi := congrFun heigen i
  simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at hi
  have hv : 0 < d * v i := hi ▸ hsum
  exact lt_of_le_of_ne (hnonneg i) (Ne.symm (right_ne_zero_of_mul (ne_of_gt hv)))

/-- A nonnegative symmetric real matrix has a nonnegative eigenvector with a
positive coordinate. -/
theorem nonneg_symmetric_matrix_has_nonneg_eigenvector {ι : Type*} [Fintype ι]
    [DecidableEq ι] [Nonempty ι] {A : Matrix ι ι ℝ}
    (hsym : A.IsHermitian) (hA : ∀ i j, 0 ≤ A i j) :
    ∃ (d : ℝ) (v : ι → ℝ), (∀ i, 0 ≤ v i) ∧ (∃ i, 0 < v i) ∧ A *ᵥ v = d • v := by
  classical
  let T : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι :=
    (Matrix.toEuclideanLin A).toContinuousLinearMap
  have hself : IsSelfAdjoint T :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
      (Matrix.isSymmetric_toEuclideanLin_iff.mpr hsym)
  obtain ⟨z, hz⟩ : ∃ z : EuclideanSpace ℝ ι, z ≠ 0 := exists_ne 0
  have hcompact : IsCompact (Metric.sphere (0 : EuclideanSpace ℝ ι) ‖z‖) :=
    isCompact_sphere _ _
  obtain ⟨x, hxmem, hxmax⟩ := hcompact.exists_isMaxOn ⟨z, by simp⟩
    T.reApplyInnerSelf_continuous.continuousOn
  let y := euclideanAbs x
  have hynorm : ‖y‖ = ‖z‖ := by
    rw [euclideanAbs_norm]
    simpa using hxmem
  have hyne : y ≠ 0 := by
    intro h
    apply hz
    apply norm_eq_zero.mp
    simpa [h] using hynorm.symm
  have hynonneg (i : ι) : 0 ≤ y i := abs_nonneg _
  have hyexists : ∃ i, 0 < y i := by
    by_contra! h
    apply hyne
    ext i
    exact le_antisymm (h i) (hynonneg i)
  have hyquad : T.reApplyInnerSelf x ≤ T.reApplyInnerSelf y := by
    change (Matrix.toEuclideanLin A).toContinuousLinearMap.reApplyInnerSelf x ≤
      (Matrix.toEuclideanLin A).toContinuousLinearMap.reApplyInnerSelf y
    rw [matrix_quadratic_form, matrix_quadratic_form]
    simpa [y, euclideanAbs] using quadratic_le_abs hA (fun i => x i)
  have hymax : IsMaxOn T.reApplyInnerSelf (Metric.sphere 0 ‖y‖) y :=
    fun _ hw ↦ (hxmax (by simpa [hynorm] using hw)).trans hyquad
  have heigen := hself.eq_smul_self_of_isLocalExtrOn (Or.inr hymax.isLocalMaxOn)
  let d := T.rayleighQuotient y
  refine ⟨d, fun i => y i, hynonneg, hyexists, ?_⟩
  simpa [T, d, Matrix.toLpLin_apply] using (congrArg ofLp heigen)

/-- A strictly positive symmetric real matrix has a strictly positive eigenvector. -/
theorem positive_symmetric_matrix_has_positive_eigenvector {ι : Type*} [Fintype ι]
    [DecidableEq ι] [Nonempty ι] {A : Matrix ι ι ℝ}
    (hsym : A.IsHermitian) (hpos : ∀ i j, 0 < A i j) :
    ∃ (d : ℝ) (v : ι → ℝ), (∀ i, 0 < v i) ∧ A *ᵥ v = d • v := by
  obtain ⟨d, v, hv, hvpos, heigen⟩ :=
    nonneg_symmetric_matrix_has_nonneg_eigenvector hsym (fun i j => (hpos i j).le)
  exact ⟨d, v, positive_matrix_eigenvector_pos hpos hv hvpos heigen, heigen⟩

end PropertyF.Ground

end

/-! The symmetric total fusion matrix. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open scoped BigOperators

namespace PropertyF.Ground

variable (D : BraidedFusionCategory)
attribute [local instance] Abelian.hasFiniteBiproducts

/-- Sum of all simple fusion matrices, over the real numbers. -/
def totalFusionMatrix (D : BraidedFusionCategory) :
    Matrix (Fin (rank D)) (Fin (rank D)) ℝ :=
  fun j k => ∑ i, (fusionCoeff D i k j : ℝ)

/-- Duality and Frobenius reciprocity make the total fusion matrix symmetric. -/
theorem totalFusionMatrix_symmetric (j k : Fin (rank D)) :
    totalFusionMatrix D j k = totalFusionMatrix D k j := by
  classical
  have h := Equiv.sum_comp (dualEquiv D) (fun i => (fusionCoeff D i j k : ℝ))
  change (∑ i, (fusionCoeff D (dualIndex D i) j k : ℝ)) = _ at h
  simpa only [totalFusionMatrix, ← fusionCoeff_dual_symmetry] using h

/-- The total fusion matrix is strictly positive in every entry. -/
theorem totalFusionMatrix_pos (j k : Fin (rank D)) :
    0 < totalFusionMatrix D j k := by
  classical
  let : Simple (simples D j) := simples_simple D j
  let : Simple (simples D k) := simples_simple D k
  let : Simple (ᘁ(simples D k)) := simple_leftDual D (simples D k)
  obtain ⟨s, r, hsr⟩ := unit_retract_leftDual_tensor (simples D j)
  let : (tensorLeft (simples D j)).Faithful :=
    PropertyF.tensorLeft_faithful_of_unit_retract s r hsr
  let Y : D.Obj := simples D j ⊗ (ᘁ(simples D k))
  have hid : (𝟙 Y : Y ⟶ Y) ≠ 0 := fun h ↦
    id_nonzero (ᘁ(simples D k))
      ((tensorLeft (simples D j)).map_eq_zero_iff.mp (by simpa [Y] using h))
  obtain ⟨i, f, _, hf, _⟩ := exists_simple_retract D hid
  let : ∀ A B : D.Obj, FiniteDimensional ℂ (A ⟶ B) := IsFusionCategory.hom_finite
  have hm : 0 < Module.finrank ℂ (simples D i ⟶ Y) := by
    rw [← finrank_to_simple_eq_from_simple D Y i]
    exact Module.finrank_pos_iff_exists_ne_zero.mpr ⟨f, hf⟩
  have hc : 0 < fusionCoeff D i k j := by
    rw [fusionCoeff_reciprocity_labels]
    obtain ⟨e'⟩ := dualIndex_iso D k
    change 0 < Module.finrank ℂ (simples D i ⟶ simples D j ⊗ simples D (dualIndex D k))
    rw [(CategoryTheory.Linear.homCongr ℂ (Iso.refl _)
      (Iso.refl (simples D j) ⊗ᵢ e'.symm)).finrank_eq]
    exact hm
  unfold totalFusionMatrix
  exact Finset.sum_pos' (fun _ _ => Nat.cast_nonneg _)
    ⟨i, Finset.mem_univ _, Nat.cast_pos.mpr hc⟩

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
    Commute (characterMatrix D i) (characterMatrix D j) := by
  classical
  apply Matrix.ext
  intro a b
  simp only [Matrix.mul_apply, characterMatrix]
  have hn : (∑ k, fusionCoeff D i a k * fusionCoeff D j k b) =
      ∑ k, fusionCoeff D j a k * fusionCoeff D i k b := by
    calc
      _ = ∑ k, fusionCoeff D j i k * fusionCoeff D k a b :=
        fusionCoeff_assoc D j i a b
      _ = ∑ k, fusionCoeff D i j k * fusionCoeff D k a b := by
        simp only [fusionCoeff_comm D j i]
      _ = _ := (fusionCoeff_assoc D i j a b).symm
  exact_mod_cast hn

theorem totalFusionMatrix_eq_sum_characterMatrix :
    totalFusionMatrix D = ∑ i, characterMatrix D i := by
  classical
  apply Matrix.ext
  intro j k
  simpa [totalFusionMatrix, characterMatrix, Matrix.sum_apply] using totalFusionMatrix_symmetric D j k

theorem total_commutes_characterMatrix (i : Fin (rank D)) :
    Commute (totalFusionMatrix D) (characterMatrix D i) := by
  classical
  rw [totalFusionMatrix_eq_sum_characterMatrix]
  change (∑ j, characterMatrix D j) * characterMatrix D i =
    characterMatrix D i * (∑ j, characterMatrix D j)
  rw [Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ ↦ characterMatrix_commute D j i

/-- The total matrix has a strictly positive common eigenvector for all
fusion matrices. -/
theorem exists_positive_common_eigenvector :
    ∃ (v : Fin (rank D) → ℝ), (∀ j, 0 < v j) ∧
      ∀ i, ∃ d : ℝ, characterMatrix D i *ᵥ v = d • v := by
  classical
  let : Nonempty (Fin (rank D)) := ⟨unitIndex D⟩
  have hs : (totalFusionMatrix D).IsHermitian := Matrix.isHermitian_iff_isSymm.mpr
    (Matrix.IsSymm.ext fun j k => totalFusionMatrix_symmetric D k j)
  obtain ⟨a, v, hvpos, hve⟩ := positive_symmetric_matrix_has_positive_eigenvector
    hs (totalFusionMatrix_pos D)
  refine ⟨v, hvpos, ?_⟩
  intro i
  have hcomm := total_commutes_characterMatrix D i
  have hve' : totalFusionMatrix D *ᵥ (characterMatrix D i *ᵥ v) =
      a • (characterMatrix D i *ᵥ v) := by
    rw [Matrix.mulVec_mulVec, hcomm.eq, ← Matrix.mulVec_mulVec, hve, Matrix.mulVec_smul]
  exact positive_matrix_eigenspace_unique (totalFusionMatrix_pos D) hvpos hve hve'

/-- A positive normalized character exists for the actual fusion rules. -/
theorem exists_positive_character :
    ∃ f : Fin (rank D) → ℝ,
      (∀ i, 0 < f i) ∧ f (unitIndex D) = 1 ∧
      ∀ i j, f i * f j = ∑ k, (fusionCoeff D i j k : ℝ) * f k := by
  classical
  obtain ⟨v, hvpos, hve⟩ := exists_positive_common_eigenvector D
  let f : Fin (rank D) → ℝ := fun i => v i / v (unitIndex D)
  have hunit : v (unitIndex D) ≠ 0 := ne_of_gt (hvpos _)
  refine ⟨f, fun i => div_pos (hvpos i) (hvpos _), ?_, ?_⟩
  · simp [f, hunit]
  · intro i j
    obtain ⟨d, hd⟩ := hve i
    have hscalar : d = f i := by
      have h := congrFun hd (unitIndex D)
      simp only [Matrix.mulVec, dotProduct, characterMatrix, Pi.smul_apply, smul_eq_mul] at h
      simp only [fusionCoeff_comm D i (unitIndex D), fusionCoeff_unit] at h
      simp at h
      dsimp [f]
      exact (eq_div_iff hunit).mpr h.symm
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

theorem character_total_eigenvector
    {f : Fin (rank D) → ℝ}
    (hf : ∀ i j, f i * f j = ∑ k, (fusionCoeff D i j k : ℝ) * f k) :
    totalFusionMatrix D *ᵥ f = (∑ i, f i) • f := by
  classical
  rw [totalFusionMatrix_eq_sum_characterMatrix, Matrix.sum_mulVec]
  ext j
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  change (∑ k, (fusionCoeff D i j k : ℝ) * f k) = f i * f j
  exact (hf i j).symm

/-- The positive normalized fusion character is unique. -/
theorem positive_character_unique
    {f g : Fin (rank D) → ℝ} (hfpos : ∀ i, 0 < f i) (hgpos : ∀ i, 0 < g i)
    (hfunit : f (unitIndex D) = 1) (hgunit : g (unitIndex D) = 1)
    (hf : ∀ i j, f i * f j = ∑ k, (fusionCoeff D i j k : ℝ) * f k)
    (hg : ∀ i j, g i * g j = ∑ k, (fusionCoeff D i j k : ℝ) * g k) : f = g := by
  classical
  let : Nonempty (Fin (rank D)) := ⟨unitIndex D⟩
  have hfe := character_total_eigenvector D hf
  have hge := character_total_eigenvector D hg
  have hsym : (totalFusionMatrix D)ᵀ = totalFusionMatrix D := by
    apply Matrix.ext
    intro i j
    exact totalFusionMatrix_symmetric D j i
  have hdot : f ⬝ᵥ totalFusionMatrix D *ᵥ g = g ⬝ᵥ totalFusionMatrix D *ᵥ f := by
    simpa [hsym] using Matrix.dotProduct_transpose_mulVec (totalFusionMatrix D) f g
  rw [hfe, hge, dotProduct_smul, dotProduct_smul, dotProduct_comm g f] at hdot
  have hdotpos : 0 < f ⬝ᵥ g := by
    apply Finset.sum_pos
    · intro i _
      exact mul_pos (hfpos i) (hgpos i)
    · exact Finset.univ_nonempty
  have heq : (∑ i, f i) = ∑ i, g i := mul_right_cancel₀ (ne_of_gt hdotpos) hdot.symm
  rw [← heq] at hge
  obtain ⟨c, hc⟩ := positive_matrix_eigenspace_unique
    (totalFusionMatrix_pos D) hfpos hfe hge
  have hc1 : c = 1 := by
    simpa [hfunit, hgunit] using (congrFun hc (unitIndex D)).symm
  rw [hc, hc1, one_smul]

/-- The unique positive normalized character of the fusion rules. -/
def fpCharacter (D : BraidedFusionCategory) : Fin (rank D) → ℝ :=
  Classical.choose (exists_positive_character D)

theorem fpCharacter_pos (i : Fin (rank D)) :
    0 < fpCharacter D i := (Classical.choose_spec (exists_positive_character D)).1 i

theorem fpCharacter_unit : fpCharacter D (unitIndex D) = 1 :=
  (Classical.choose_spec (exists_positive_character D)).2.1

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
theorem weighted_eigenvalue_bound {ι : Type*} [Fintype ι] (N : ι → ι → ℝ)
    (T : ι → ι → ℂ) (f : ι → ℝ) {F : ℝ} (v : ι → ℂ) {z : ℂ}
    {i₀ : ι} (hv : v i₀ ≠ 0) (hf : ∀ i, 0 < f i)
    (hN : ∀ i j, 0 ≤ N i j) (hdom : ∀ i j, ‖T i j‖ ≤ N i j)
    (hfp : ∀ i, ∑ j, N i j * f j = F * f i)
    (heig : ∀ i, ∑ j, T i j * v j = z * v i) :
    ‖z‖ ≤ F := by
  classical
  obtain ⟨i, _, hmax⟩ := Finset.exists_max_image Finset.univ
    (fun j => ‖v j‖ / f j) ⟨i₀, Finset.mem_univ _⟩
  let r := ‖v i‖ / f i
  have hvi : 0 < ‖v i‖ := (div_pos_iff_of_pos_right (hf i)).1 <|
    lt_of_lt_of_le (div_pos (norm_pos_iff.mpr hv) (hf i₀)) (hmax i₀ (Finset.mem_univ _))
  have hvbound (j : ι) : ‖v j‖ ≤ r * f j := by
    apply (div_le_iff₀ (hf j)).1
    exact hmax j (Finset.mem_univ _)
  have hbound : ‖z‖ * ‖v i‖ ≤ F * ‖v i‖ := by
    calc
      _ = ‖∑ j, T i j * v j‖ := by rw [heig i, norm_mul]
      _ ≤ ∑ j, ‖T i j * v j‖ := by simpa using norm_sum_le Finset.univ (fun j => T i j * v j)
      _ ≤ ∑ j, N i j * (r * f j) := Finset.sum_le_sum fun j _ ↦ by
        rw [norm_mul]
        exact mul_le_mul (hdom i j) (hvbound j) (norm_nonneg _) (hN i j)
      _ = r * (∑ j, N i j * f j) := by
        simp only [Finset.mul_sum, mul_left_comm]
      _ = F * ‖v i‖ := by
        rw [hfp i]
        dsimp [r]
        field_simp [ne_of_gt (hf i)]
  exact le_of_mul_le_mul_right hbound hvi

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
    (hA : ∀ i j, 0 ≤ A i j) (hw : ∀ i, 0 < w i) (hv : v ≠ 0) : ‖z‖ ≤ d := by
  obtain ⟨i₀, hi₀⟩ := Function.ne_iff.mp hv
  apply Dimensions.weighted_eigenvalue_bound (fun i j => A i j)
    (fun i j => (A i j : ℂ)) w v hi₀ hw hA
  · intro i j
    simp [Complex.norm_real, abs_of_nonneg (hA i j)]
  · intro i
    simpa [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] using congrFun hwe i
  · intro i
    simpa [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] using congrFun hve i

end PropertyF.Ground

end

/-! Agreement of the positive character with the target's spectral radius. -/

@[expose] public noncomputable section
open scoped BigOperators Matrix Matrix.Norms.Operator

namespace PropertyF.Ground

variable (D : BraidedFusionCategory)

theorem fpCharacter_le_fpSimple (i : Fin (rank D)) :
    fpCharacter D i ≤ fpSimple D i := by
  let χ : Fin (rank D) → ℂ := fun j => fpCharacter D j
  have hχ : χ (unitIndex D) ≠ 0 := by simp [χ, fpCharacter_unit]
  have hchar : ∀ j k, χ j * χ k = ∑ l, (fusionCoeff D j k l : ℂ) * χ l := by
    intro j k
    dsimp [χ]
    exact_mod_cast fpCharacter_mul D j k
  simpa [χ, Complex.norm_real, abs_of_pos (fpCharacter_pos D i)] using
    (Dimensions.character_norm_le_fpSimple D hχ hchar i)

theorem fpSimple_le_fpCharacter (i : Fin (rank D)) :
    fpSimple D i ≤ fpCharacter D i := by
  classical
  let : Nonempty (Fin (rank D)) := ⟨unitIndex D⟩
  let A := characterMatrix D i
  let B := A.map Complex.ofRealHom
  have hB : B = (fusionMatrix D i)ᵀ := by
    ext j k
    change (((fusionCoeff D i j k : ℝ) : ℂ)) = _
    simp [fusionMatrix, fusionCoeff]
  have hwe : A *ᵥ fpCharacter D = fpCharacter D i • fpCharacter D := by
    ext j
    change (∑ k, (fusionCoeff D i j k : ℝ) * fpCharacter D k) = _
    exact (fpCharacter_mul D i j).symm
  obtain ⟨z, hz, hzmax⟩ := spectrum.exists_nnnorm_eq_spectralRadius B
  have hz' : z ∈ spectrum ℂ B.toLin' := by simpa using hz
  obtain ⟨v, hv⟩ := (Module.End.hasEigenvalue_iff_mem_spectrum.mpr hz').exists_hasEigenvector
  have hve : A.map Complex.ofRealHom *ᵥ v = z • v := by
    simpa [B, Matrix.toLin'_apply] using hv.apply_eq_smul
  have hbound := complex_eigenvalue_le_positive_eigenvalue hwe hve
    (fun j k => Nat.cast_nonneg _) (fpCharacter_pos D) hv.2
  have hrad : fpSimple D i = ‖z‖ := by
    unfold fpSimple
    rw [← Matrix.spectralRadius_transpose (fusionMatrix D i), ← hB, ← hzmax]
    simp
  rw [hrad]
  exact hbound

/-- The target spectral-radius FP dimension is the unique positive character. -/
theorem fpSimple_eq_fpCharacter (i : Fin (rank D)) :
    fpSimple D i = fpCharacter D i :=
  le_antisymm (fpSimple_le_fpCharacter D i) (fpCharacter_le_fpSimple D i)

theorem fpSimple_pos (i : Fin (rank D)) :
    0 < fpSimple D i := (fpSimple_eq_fpCharacter D i).symm ▸ fpCharacter_pos D i

theorem fpSimple_mul (i j : Fin (rank D)) :
    fpSimple D i * fpSimple D j =
      ∑ k, (fusionCoeff D i j k : ℝ) * fpSimple D k :=
  by simp only [fpSimple_eq_fpCharacter, fpCharacter_mul]

/-- FP dimensions form a complex-valued fusion character. -/
theorem fpSimple_isFusionMultiplicative :
    IsFusionMultiplicative D (fun i ↦ (fpSimple D i : ℂ)) := by
  intro i j
  dsimp
  exact_mod_cast fpSimple_mul D i j

/-- The fusion matrix of a dual is the transpose of the original one. -/
theorem fusionMatrix_dual (i : Fin (rank D)) :
    fusionMatrix D (dualIndex D i) = (fusionMatrix D i)ᵀ := by
  ext j k
  change (fusionCoeff D (dualIndex D i) k j : ℂ) = (fusionCoeff D i j k : ℂ)
  rw [← fusionCoeff_dual_symmetry D i k j]

/-- Dual simple objects have the same FP dimension. -/
theorem fpSimple_dual (i : Fin (rank D)) :
    fpSimple D (dualIndex D i) = fpSimple D i :=
  by simp [fpSimple, fusionMatrix_dual, Matrix.spectralRadius_transpose]

/-- Every simple has FP dimension at least one. -/
theorem one_le_fpSimple (i : Fin (rank D)) :
    1 ≤ fpSimple D i := by
  classical
  have hsum : 1 ≤ ∑ k, (fusionCoeff D i (dualIndex D i) k : ℝ) * fpSimple D k := by
    have h := Finset.single_le_sum
      (f := fun k => (fusionCoeff D i (dualIndex D i) k : ℝ) * fpSimple D k)
      (fun k _ => mul_nonneg (Nat.cast_nonneg _) (fpSimple_pos D k).le)
      (Finset.mem_univ (unitIndex D))
    simpa [fusionCoeff_dual_unit, fpSimple_unit] using h
  rw [← fpSimple_mul, fpSimple_dual] at hsum
  exact (one_le_sq_iff₀ (fpSimple_pos D i).le).mp (by simpa only [pow_two] using hsum)

end PropertyF.Ground

end
