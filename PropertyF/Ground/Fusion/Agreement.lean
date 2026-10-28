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
    (A : Matrix ι ι ℝ) (hA : ∀ i j, 0 < A i j)
    (x y : ι → ℝ) (hx : ∀ i, 0 < x i) (d : ℝ)
    (hxe : A *ᵥ x = d • x) (hye : A *ᵥ y = d • y) :
    ∃ c : ℝ, y = c • x := by
  classical
  obtain ⟨i, _, hmin⟩ := Finset.exists_min_image Finset.univ (fun j => y j / x j)
    Finset.univ_nonempty
  let c := y i / x i
  have hnonneg (j : ι) : 0 ≤ y j - c * x j := by
    have hj := hmin j (Finset.mem_univ j)
    dsimp [c] at hj ⊢
    have hmul := mul_le_mul_of_nonneg_right hj (hx j).le
    have : y i / x i * x j ≤ y j := by
      simpa [div_mul_cancel₀ _ (ne_of_gt (hx j))] using hmul
    linarith
  have hzero : y i - c * x i = 0 := by
    simp [c, div_mul_cancel₀ _ (ne_of_gt (hx i))]
  have hsum : ∑ j, A i j * (y j - c * x j) = 0 := by
    have ex := congrFun hxe i
    have ey := congrFun hye i
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at ex ey
    calc
      _ = (∑ j, A i j * y j) - c * (∑ j, A i j * x j) := by
        simp only [mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
        apply congrArg₂ (· - ·) rfl
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = d * (y i - c * x i) := by rw [ex, ey]; ring
      _ = 0 := by rw [hzero, mul_zero]
  have hall : ∀ j, y j - c * x j = 0 := by
    intro j
    have hj := (Finset.sum_eq_zero_iff_of_nonneg
      (fun j _ => mul_nonneg (hA i j).le (hnonneg j))).mp hsum j (Finset.mem_univ j)
    exact (mul_eq_zero.mp hj).resolve_left (ne_of_gt (hA i j))
  refine ⟨c, ?_⟩
  funext j
  simp only [Pi.smul_apply, smul_eq_mul]
  linarith [hall j]

end PropertyF.Ground

end

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
open scoped BigOperators Matrix Matrix.Norms.Operator ENNReal
namespace PropertyF.Ground.Dimensions

/-- Each value of any nonzero fusion-ring character is bounded in absolute value
by the spectral-radius FP dimension. No positivity of the character is needed. -/
theorem character_norm_le_fpSimple (C : Ground.BraidedFusionCategory)
    (χ : Fin (Ground.rank C) → ℂ) (i₀ : Fin (Ground.rank C)) (hχ : χ i₀ ≠ 0)
    (hchar : ∀ i j, χ i * χ j = ∑ k,
      (Ground.fusionCoeff C i j k : ℂ) * χ k) (i : Fin (Ground.rank C)) :
    ‖χ i‖ ≤ Ground.fpSimple C i := by
  classical
  let A := (Ground.fusionMatrix C i)ᵀ
  have heigen : A *ᵥ χ = χ i • χ := by
    ext j
    change (∑ k, (Ground.fusionCoeff C i j k : ℂ) * χ k) = χ i * χ j
    exact (hchar i j).symm
  have hzero : (Matrix.scalar (Fin (Ground.rank C)) (χ i) - A) *ᵥ χ = 0 := by
    rw [Matrix.sub_mulVec, heigen]
    ext j
    simp [Matrix.scalar_apply]
  have hdet : (Matrix.scalar (Fin (Ground.rank C)) (χ i) - A).det = 0 :=
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
  have hreal := ENNReal.toReal_mono htop hle
  simpa [Ground.fpSimple, A, Matrix.spectralRadius_transpose] using hreal

/-- Every complex field conjugate of a fusion character obeys the same FP
bound, because field automorphisms preserve the integer fusion coefficients. -/
theorem galois_character_norm_le_fpSimple (C : Ground.BraidedFusionCategory)
    (χ : Fin (Ground.rank C) → ℂ) (i₀ : Fin (Ground.rank C)) (hχ : χ i₀ ≠ 0)
    (hchar : ∀ i j, χ i * χ j = ∑ k,
      (Ground.fusionCoeff C i j k : ℂ) * χ k)
    (σ : ℂ ≃+* ℂ) (i : Fin (Ground.rank C)) :
    ‖σ (χ i)‖ ≤ Ground.fpSimple C i := by
  apply character_norm_le_fpSimple C (fun j => σ (χ j)) i₀
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

def euclideanAbs {ι : Type*} [Fintype ι] (x : EuclideanSpace ℝ ι) : EuclideanSpace ℝ ι :=
  toLp 2 (fun i => |x i|)

theorem euclideanAbs_norm {ι : Type*} [Fintype ι] (x : EuclideanSpace ℝ ι) :
    ‖euclideanAbs x‖ = ‖x‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp [EuclideanSpace.real_norm_sq_eq, euclideanAbs]

/-- Replacing coordinates by absolute values cannot decrease the quadratic
form of a matrix with nonnegative entries. -/
theorem quadratic_le_abs {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℝ) (hA : ∀ i j, 0 ≤ A i j) (x : ι → ℝ) :
    ∑ i, ∑ j, x i * A i j * x j ≤
      ∑ i, ∑ j, |x i| * A i j * |x j| := by
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  have h := mul_le_mul_of_nonneg_left (le_abs_self (x i * x j)) (hA i j)
  simpa [abs_mul, mul_assoc, mul_comm, mul_left_comm] using h

theorem matrix_quadratic_form {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (x : EuclideanSpace ℝ ι) :
    (Matrix.toEuclideanLin A).toContinuousLinearMap.reApplyInnerSelf x =
      ∑ i, ∑ j, x i * A i j * x j := by
  simp [ContinuousLinearMap.reApplyInnerSelf, EuclideanSpace.inner_eq_star_dotProduct,
    Matrix.toLpLin_apply, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc,
    mul_comm, mul_left_comm]

/-- A strictly positive symmetric real matrix has a strictly positive
eigenvector. -/
theorem positive_symmetric_matrix_has_positive_eigenvector {ι : Type*} [Fintype ι]
    [DecidableEq ι] [Nonempty ι] (A : Matrix ι ι ℝ)
    (hsym : A.IsHermitian) (hpos : ∀ i j, 0 < A i j) :
    ∃ (d : ℝ) (v : ι → ℝ), (∀ i, 0 < v i) ∧ A *ᵥ v = d • v := by
  classical
  let T : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι :=
    (Matrix.toEuclideanLin A).toContinuousLinearMap
  have hself : IsSelfAdjoint T := by
    apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
    exact Matrix.isSymmetric_toEuclideanLin_iff.mpr hsym
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
    have := hynorm
    rw [h] at this
    simp only [norm_zero] at this
    exact hz (norm_eq_zero.mp this.symm)
  have hynonneg (i : ι) : 0 ≤ y i := abs_nonneg _
  have hyexists : ∃ i, 0 < y i := by
    by_contra h
    push Not at h
    apply hyne
    ext i
    have := hynonneg i
    have := h i
    simp only [PiLp.zero_apply]
    linarith
  have hyquad : T.reApplyInnerSelf x ≤ T.reApplyInnerSelf y := by
    change (Matrix.toEuclideanLin A).toContinuousLinearMap.reApplyInnerSelf x ≤
      (Matrix.toEuclideanLin A).toContinuousLinearMap.reApplyInnerSelf y
    rw [matrix_quadratic_form, matrix_quadratic_form]
    simpa [y, euclideanAbs] using quadratic_le_abs A (fun i j => (hpos i j).le) (fun i => x i)
  have hymax : IsMaxOn T.reApplyInnerSelf (Metric.sphere 0 ‖y‖) y := by
    intro w hw
    have hw' : w ∈ Metric.sphere (0 : EuclideanSpace ℝ ι) ‖z‖ := by simpa [hynorm] using hw
    exact (hxmax hw').trans hyquad
  have heigen := hself.eq_smul_self_of_isLocalExtrOn (Or.inr hymax.isLocalMaxOn)
  let d := T.rayleighQuotient y
  have heigen' : A *ᵥ (fun i => y i) = d • (fun i => y i) := by
    have h := congrArg ofLp heigen
    simpa [T, d, Matrix.toLpLin_apply] using h
  obtain ⟨j, hj⟩ := hyexists
  have hypos (i : ι) : 0 < y i := by
    have hsum : 0 < ∑ k, A i k * y k :=
      Finset.sum_pos' (fun k _ => mul_nonneg (hpos i k).le (hynonneg k))
        ⟨j, Finset.mem_univ _, mul_pos (hpos i j) hj⟩
    have hi := congrFun heigen' i
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at hi
    have : 0 < d * y i := by linarith
    by_contra hn
    have : y i = 0 := le_antisymm (le_of_not_gt hn) (hynonneg i)
    simp [this] at *
  exact ⟨d, fun i => y i, hypos, heigen'⟩

end PropertyF.Ground

end

/-! The symmetric total fusion matrix. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open scoped BigOperators

namespace PropertyF.Ground
attribute [local instance] Abelian.hasFiniteBiproducts

/-- Sum of all simple fusion matrices, over the real numbers. -/
def totalFusionMatrix (D : BraidedFusionCategory) :
    Matrix (Fin (rank D)) (Fin (rank D)) ℝ :=
  fun j k => ∑ i, (fusionCoeff D i k j : ℝ)

/-- Duality and Frobenius reciprocity make the total fusion matrix symmetric. -/
theorem totalFusionMatrix_symmetric (D : BraidedFusionCategory) (j k : Fin (rank D)) :
    totalFusionMatrix D j k = totalFusionMatrix D k j := by
  classical
  unfold totalFusionMatrix
  calc
    _ = ∑ i, (fusionCoeff D (dualIndex D i) j k : ℝ) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [fusionCoeff_comm D i k, fusionCoeff_reciprocity_labels,
        fusionCoeff_comm D j (dualIndex D i)]
    _ = _ := by
      have h := Equiv.sum_comp (dualEquiv D) (fun i => (fusionCoeff D i j k : ℝ))
      change (∑ i, (fusionCoeff D (dualIndex D i) j k : ℝ)) = _ at h
      exact h

/-- The total fusion matrix is strictly positive in every entry. -/
theorem totalFusionMatrix_pos (D : BraidedFusionCategory) (j k : Fin (rank D)) :
    0 < totalFusionMatrix D j k := by
  classical
  letI : Simple (simples D j) := simples_simple D j
  letI : Simple (simples D k) := simples_simple D k
  letI : Simple (ᘁ(simples D k)) := simple_leftDual D (simples D k)
  obtain ⟨s, r, hsr⟩ := unit_retract_leftDual_tensor (simples D j)
  letI : (tensorLeft (simples D j)).Faithful :=
    PropertyF.tensorLeft_faithful_of_unit_retract _ _ s r hsr
  let Y : D.Obj := simples D j ⊗ (ᘁ(simples D k))
  have hid : (𝟙 Y : Y ⟶ Y) ≠ 0 := by
    intro h
    have hh : (tensorLeft (simples D j)).map (𝟙 (ᘁ(simples D k))) =
        (tensorLeft (simples D j)).map 0 := by simpa [Y] using h
    exact id_nonzero (ᘁ(simples D k)) ((tensorLeft (simples D j)).map_injective hh)
  obtain ⟨m, ⟨e⟩⟩ := simples_decompose D Y
  let V : (Σ i, Fin (m i)) → D.Obj := fun p => simples D p.1
  have he : e.hom ≠ 0 := by
    intro h
    apply hid
    have hh := congrArg (fun t => t ≫ e.inv) h
    simpa using hh
  have hp : ∃ p, e.hom ≫ biproduct.π V p ≠ 0 := by
    by_contra h
    push Not at h
    apply he
    apply biproduct.hom_ext
    intro p
    simpa using h p
  obtain ⟨p, hp⟩ := hp
  letI : ∀ A B : D.Obj, FiniteDimensional ℂ (A ⟶ B) := IsFusionCategory.hom_finite
  have hm : 0 < Module.finrank ℂ (simples D p.1 ⟶ Y) := by
    rw [← finrank_to_simple_eq_from_simple D Y p.1]
    exact Module.finrank_pos_iff_exists_ne_zero.mpr ⟨_, hp⟩
  have hc : 0 < fusionCoeff D p.1 k j := by
    rw [fusionCoeff_reciprocity_labels]
    obtain ⟨e'⟩ := dualIndex_iso D k
    change 0 < Module.finrank ℂ (simples D p.1 ⟶ simples D j ⊗ simples D (dualIndex D k))
    rw [(CategoryTheory.Linear.homCongr ℂ (Iso.refl _)
      (Iso.refl (simples D j) ⊗ᵢ e'.symm)).finrank_eq]
    exact hm
  unfold totalFusionMatrix
  exact Finset.sum_pos' (fun _ _ => Nat.cast_nonneg _)
    ⟨p.1, Finset.mem_univ _, Nat.cast_pos.mpr hc⟩

end PropertyF.Ground

end

/-! Constructing the positive fusion character from the total matrix. -/

@[expose] public noncomputable section
open scoped BigOperators Matrix

namespace PropertyF.Ground

/-- The transpose convention: its rows encode the fusion equations. -/
def characterMatrix (D : BraidedFusionCategory) (i : Fin (rank D)) :
    Matrix (Fin (rank D)) (Fin (rank D)) ℝ :=
  fun j k => fusionCoeff D i j k

theorem characterMatrix_commute (D : BraidedFusionCategory) (i j : Fin (rank D)) :
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

theorem totalFusionMatrix_eq_sum_characterMatrix (D : BraidedFusionCategory) :
    totalFusionMatrix D = ∑ i, characterMatrix D i := by
  classical
  apply Matrix.ext
  intro j k
  simpa [totalFusionMatrix, characterMatrix, Matrix.sum_apply] using totalFusionMatrix_symmetric D j k

theorem total_commutes_characterMatrix (D : BraidedFusionCategory) (i : Fin (rank D)) :
    Commute (totalFusionMatrix D) (characterMatrix D i) := by
  classical
  rw [totalFusionMatrix_eq_sum_characterMatrix]
  change (∑ j, characterMatrix D j) * characterMatrix D i =
    characterMatrix D i * (∑ j, characterMatrix D j)
  rw [Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  exact characterMatrix_commute D j i

/-- The total matrix has a strictly positive common eigenvector for all
fusion matrices. -/
theorem exists_positive_common_eigenvector (D : BraidedFusionCategory) :
    ∃ (v : Fin (rank D) → ℝ), (∀ j, 0 < v j) ∧
      ∀ i, ∃ d : ℝ, characterMatrix D i *ᵥ v = d • v := by
  classical
  letI : Nonempty (Fin (rank D)) := ⟨unitIndex D⟩
  have hs : (totalFusionMatrix D).IsHermitian := by
    rw [Matrix.isHermitian_iff_isSymm]
    exact Matrix.IsSymm.ext (fun j k => totalFusionMatrix_symmetric D k j)
  obtain ⟨a, v, hvpos, hve⟩ := positive_symmetric_matrix_has_positive_eigenvector
    (totalFusionMatrix D) hs (totalFusionMatrix_pos D)
  refine ⟨v, hvpos, ?_⟩
  intro i
  have hcomm := total_commutes_characterMatrix D i
  have hve' : totalFusionMatrix D *ᵥ (characterMatrix D i *ᵥ v) =
      a • (characterMatrix D i *ᵥ v) := by
    rw [Matrix.mulVec_mulVec, hcomm.eq, ← Matrix.mulVec_mulVec, hve]
    rw [Matrix.mulVec_smul]
  obtain ⟨d, hd⟩ := positive_matrix_eigenspace_unique (totalFusionMatrix D)
    (totalFusionMatrix_pos D) v (characterMatrix D i *ᵥ v) hvpos a hve hve'
  exact ⟨d, hd⟩

/-- A positive normalized character exists for the actual fusion rules. -/
theorem exists_positive_character (D : BraidedFusionCategory) :
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
      exact (eq_div_iff hunit).mpr (by linarith)
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

theorem character_total_eigenvector (D : BraidedFusionCategory)
    (f : Fin (rank D) → ℝ)
    (hf : ∀ i j, f i * f j = ∑ k, (fusionCoeff D i j k : ℝ) * f k) :
    totalFusionMatrix D *ᵥ f = (∑ i, f i) • f := by
  classical
  rw [totalFusionMatrix_eq_sum_characterMatrix, Matrix.sum_mulVec]
  ext j
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  change (∑ k, (fusionCoeff D i j k : ℝ) * f k) = f i * f j
  exact (hf i j).symm

/-- The positive normalized fusion character is unique. -/
theorem positive_character_unique (D : BraidedFusionCategory)
    (f g : Fin (rank D) → ℝ) (hfpos : ∀ i, 0 < f i) (hgpos : ∀ i, 0 < g i)
    (hfunit : f (unitIndex D) = 1) (hgunit : g (unitIndex D) = 1)
    (hf : ∀ i j, f i * f j = ∑ k, (fusionCoeff D i j k : ℝ) * f k)
    (hg : ∀ i j, g i * g j = ∑ k, (fusionCoeff D i j k : ℝ) * g k) : f = g := by
  classical
  letI : Nonempty (Fin (rank D)) := ⟨unitIndex D⟩
  have hfe := character_total_eigenvector D f hf
  have hge := character_total_eigenvector D g hg
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
  have heq : (∑ i, f i) = ∑ i, g i := by
    have := mul_right_cancel₀ (ne_of_gt hdotpos) hdot.symm
    exact this
  rw [← heq] at hge
  obtain ⟨c, hc⟩ := positive_matrix_eigenspace_unique (totalFusionMatrix D)
    (totalFusionMatrix_pos D) f g hfpos _ hfe hge
  have hc1 : c = 1 := by
    have h := congrFun hc (unitIndex D)
    simpa [hfunit, hgunit] using h.symm
  rw [hc, hc1, one_smul]

/-- The unique positive normalized character of the fusion rules. -/
def fpCharacter (D : BraidedFusionCategory) : Fin (rank D) → ℝ :=
  Classical.choose (exists_positive_character D)

theorem fpCharacter_pos (D : BraidedFusionCategory) (i : Fin (rank D)) :
    0 < fpCharacter D i := (Classical.choose_spec (exists_positive_character D)).1 i

theorem fpCharacter_unit (D : BraidedFusionCategory) : fpCharacter D (unitIndex D) = 1 :=
  (Classical.choose_spec (exists_positive_character D)).2.1

theorem fpCharacter_mul (D : BraidedFusionCategory) (i j : Fin (rank D)) :
    fpCharacter D i * fpCharacter D j =
      ∑ k, (fusionCoeff D i j k : ℝ) * fpCharacter D k :=
  (Classical.choose_spec (exists_positive_character D)).2.2 i j

end PropertyF.Ground

end

/-! Spectral bounds from a positive eigenvector. -/

@[expose] public noncomputable section
open scoped BigOperators Matrix

namespace PropertyF.Ground

/-- A positive real eigenvector bounds the modulus of every complex eigenvalue
of a nonnegative real matrix. -/
theorem complex_eigenvalue_le_positive_eigenvalue {ι : Type*} [Fintype ι] [Nonempty ι]
    (A : Matrix ι ι ℝ) (hA : ∀ i j, 0 ≤ A i j) (w : ι → ℝ)
    (hw : ∀ i, 0 < w i) (d : ℝ) (hwe : A *ᵥ w = d • w)
    (z : ℂ) (v : ι → ℂ) (hv : v ≠ 0)
    (hve : A.map Complex.ofRealHom *ᵥ v = z • v) : ‖z‖ ≤ d := by
  classical
  obtain ⟨i, _, hmax⟩ := Finset.exists_max_image Finset.univ (fun j => ‖v j‖ / w j)
    Finset.univ_nonempty
  have hiv : v i ≠ 0 := by
    intro hi
    have hall : ∀ j, v j = 0 := by
      intro j
      have h := hmax j (Finset.mem_univ j)
      simp [hi] at h
      have : ‖v j‖ = 0 := by
        apply le_antisymm
        · have hh := (div_le_iff₀ (hw j)).mp h
          simpa using hh
        · exact norm_nonneg _
      exact norm_eq_zero.mp this
    apply hv
    funext j
    simpa using hall j
  have hbound (j : ι) : ‖v j‖ ≤ (‖v i‖ / w i) * w j := by
    have h := hmax j (Finset.mem_univ j)
    exact (div_le_iff₀ (hw j)).mp h
  have hrow := congrFun hwe i
  have hrowc := congrFun hve i
  simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at hrow hrowc
  change (∑ j, (A i j : ℂ) * v j) = z * v i at hrowc
  have hineq : ‖z‖ * ‖v i‖ ≤ d * ‖v i‖ := by
    calc
      _ = ‖∑ j, (A i j : ℂ) * v j‖ := by rw [hrowc, norm_mul]
      _ ≤ ∑ j, ‖(A i j : ℂ) * v j‖ := norm_sum_le _ _
      _ = ∑ j, A i j * ‖v j‖ := by
        apply Finset.sum_congr rfl
        intro j _
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hA i j)]
      _ ≤ ∑ j, A i j * ((‖v i‖ / w i) * w j) := by
        exact Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hbound j) (hA i j)
      _ = (‖v i‖ / w i) * (∑ j, A i j * w j) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = (‖v i‖ / w i) * (d * w i) := by rw [hrow]
      _ = d * ‖v i‖ := by field_simp [ne_of_gt (hw i)]
  exact le_of_mul_le_mul_right hineq (norm_pos_iff.mpr hiv)

end PropertyF.Ground

end

/-! Agreement of the positive character with the target's spectral radius. -/

@[expose] public noncomputable section
open scoped BigOperators Matrix Matrix.Norms.Operator

namespace PropertyF.Ground

theorem fpCharacter_le_fpSimple (D : BraidedFusionCategory) (i : Fin (rank D)) :
    fpCharacter D i ≤ fpSimple D i := by
  let χ : Fin (rank D) → ℂ := fun j => fpCharacter D j
  have hχ : χ (unitIndex D) ≠ 0 := by simp [χ, fpCharacter_unit]
  have hchar : ∀ j k, χ j * χ k = ∑ l, (fusionCoeff D j k l : ℂ) * χ l := by
    intro j k
    dsimp [χ]
    exact_mod_cast fpCharacter_mul D j k
  have h := Dimensions.character_norm_le_fpSimple D χ (unitIndex D) hχ hchar i
  simpa [χ, Complex.norm_real, abs_of_pos (fpCharacter_pos D i)] using h

theorem fpSimple_le_fpCharacter (D : BraidedFusionCategory) (i : Fin (rank D)) :
    fpSimple D i ≤ fpCharacter D i := by
  classical
  letI : Nonempty (Fin (rank D)) := ⟨unitIndex D⟩
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
  have hbound := complex_eigenvalue_le_positive_eigenvalue A
    (fun j k => Nat.cast_nonneg _) (fpCharacter D) (fpCharacter_pos D)
    (fpCharacter D i) hwe z v hv.2 hve
  have hrad : fpSimple D i = ‖z‖ := by
    unfold fpSimple
    rw [← Matrix.spectralRadius_transpose (fusionMatrix D i), ← hB, ← hzmax]
    simp
  rw [hrad]
  exact hbound

/-- The target spectral-radius FP dimension is the unique positive character. -/
theorem fpSimple_eq_fpCharacter (D : BraidedFusionCategory) (i : Fin (rank D)) :
    fpSimple D i = fpCharacter D i :=
  le_antisymm (fpSimple_le_fpCharacter D i) (fpCharacter_le_fpSimple D i)

theorem fpSimple_pos (D : BraidedFusionCategory) (i : Fin (rank D)) :
    0 < fpSimple D i := by rw [fpSimple_eq_fpCharacter]; exact fpCharacter_pos D i

theorem fpSimple_mul (D : BraidedFusionCategory) (i j : Fin (rank D)) :
    fpSimple D i * fpSimple D j =
      ∑ k, (fusionCoeff D i j k : ℝ) * fpSimple D k := by
  simp only [fpSimple_eq_fpCharacter, fpCharacter_mul]

/-- The fusion matrix of a dual is the transpose of the original one. -/
theorem fusionMatrix_dual (D : BraidedFusionCategory) (i : Fin (rank D)) :
    fusionMatrix D (dualIndex D i) = (fusionMatrix D i)ᵀ := by
  ext j k
  change (fusionCoeff D (dualIndex D i) k j : ℂ) = (fusionCoeff D i j k : ℂ)
  rw [fusionCoeff_comm D (dualIndex D i) k, fusionCoeff_reciprocity_labels,
    dualIndex_involutive, fusionCoeff_comm D j i]

/-- Dual simple objects have the same FP dimension. -/
theorem fpSimple_dual (D : BraidedFusionCategory) (i : Fin (rank D)) :
    fpSimple D (dualIndex D i) = fpSimple D i := by
  simp [fpSimple, fusionMatrix_dual, Matrix.spectralRadius_transpose]

theorem fusionCoeff_dual_unit (D : BraidedFusionCategory) (i : Fin (rank D)) :
    fusionCoeff D i (dualIndex D i) (unitIndex D) = 1 := by
  rw [fusionCoeff_comm D i (dualIndex D i), fusionCoeff_reciprocity_labels,
    fusionCoeff_unit]
  simp

/-- Every simple has FP dimension at least one. -/
theorem one_le_fpSimple (D : BraidedFusionCategory) (i : Fin (rank D)) :
    1 ≤ fpSimple D i := by
  classical
  have hsum : 1 ≤ ∑ k, (fusionCoeff D i (dualIndex D i) k : ℝ) * fpSimple D k := by
    have h := Finset.single_le_sum
      (f := fun k => (fusionCoeff D i (dualIndex D i) k : ℝ) * fpSimple D k)
      (fun k _ => mul_nonneg (Nat.cast_nonneg _) (fpSimple_pos D k).le)
      (Finset.mem_univ (unitIndex D))
    simpa [fusionCoeff_dual_unit, fpSimple_unit] using h
  rw [← fpSimple_mul, fpSimple_dual] at hsum
  nlinarith [fpSimple_pos D i]

end PropertyF.Ground

end
