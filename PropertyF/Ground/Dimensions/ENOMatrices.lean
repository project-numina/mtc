module
public import PropertyF.Ground.Fusion.Agreement
public import PropertyF.Ground.Dimensions.MultiplicityDefect
public import PropertyF.Ground.Dimensions.BiproductTrace
public import PropertyF.Ground.Dimensions.DimensionCharacter
public import PropertyF.Ground.Integrate.CharacterReality
public import PropertyF.Ground.Modular.SMatrix

/-! # Trace matrices, eigenvalue bounds, and saturation

Weighted eigenvalue estimates and root traces produce matrix bounds for fusion coefficients.
Saturated complex bounds determine the phases of their eigenvectors.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open scoped BigOperators
namespace PropertyF.Ground.Dimensions
universe v u

variable (C : BraidedFusionCategory.{v,u})
attribute [local instance] Abelian.hasFiniteBiproducts

/-- Trace with the actual natural square root of the fourth dual, without
assuming that root is monoidal. -/
def rootTrace (C : BraidedFusionCategory.{v,u}) {X : C.Obj} (f : X ⟶ X) :
    End (𝟙_ C.Obj) := rightTraceWith ((fourthDualRootNaturalIso C).app X) f

/-- The root trace of the identity is the quantum trace of the root component. -/
theorem rootTrace_id (X : C.Obj) :
    rootTrace C (𝟙 X) = rightQuantumTrace ((fourthDualRootNaturalIso C).app X) :=
  rightTraceWith_id _

set_option backward.isDefEq.respectTransparency false in
/-- The root trace is linear in its endomorphism. -/
def rootTraceLinear (C : BraidedFusionCategory.{v,u}) (X : C.Obj) :
    (X ⟶ X) →ₗ[ℂ] End (𝟙_ C.Obj) where
  toFun := rootTrace C
  map_add' := by
    intro f g
    apply End.homEquiv.injective
    simp [rootTrace, rightTraceWith, tensorHom_def]
  map_smul' := by
    intro z f
    apply End.homEquiv.injective
    simp [rootTrace, rightTraceWith, tensorHom_def]

set_option backward.isDefEq.respectTransparency false in
/-- Naturality of the square root makes its trace cyclic. -/
theorem rootTrace_cyclic {X Y : C.Obj}
    (f : X ⟶ Y) (g : Y ⟶ X) : rootTrace C (f ≫ g) = rootTrace C (g ≫ f) :=
  rightTraceWith_cyclic f g ((fourthDualRootNaturalIso C).hom.naturality f)

/-- The natural-root trace of the identity is invariant under isomorphism. -/
theorem rootTrace_id_iso {X Y : C.Obj} (e : X ≅ Y) :
    rootTrace C (𝟙 X) = rootTrace C (𝟙 Y) := by simpa using rootTrace_cyclic C e.hom e.inv

/-- On a finite biproduct of simples, the natural-root trace is the sum of
simple dimensions weighted by the scalar diagonal blocks. -/
theorem rootTrace_biproduct_simple
    {ι : Type*} [Fintype ι] (F : ι → C.Obj) [HasBiproduct F]
    (hs : ∀ i, Simple (F i)) (f : (⨁ F) ⟶ (⨁ F)) :
    ∃ c : ι → ℂ,
      (∀ i, biproduct.ι F i ≫ f ≫ biproduct.π F i = c i • 𝟙 (F i)) ∧
      rootTrace C f = ∑ i, c i • rootTrace C (𝟙 (F i)) :=
  cyclicTrace_biproduct_simple (rootTraceLinear C) (fun f g => rootTrace_cyclic C f g)
    hs (fun _ => IsFusionCategory.hom_finite _ _) f

end PropertyF.Ground.Dimensions

end

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
open scoped BigOperators Matrix
namespace PropertyF.Ground.Dimensions
universe v u

variable (C : BraidedFusionCategory.{v,u})
/-- The dimension of a simple object with respect to the natural double-dual
square root. -/
def rootDimension (C : BraidedFusionCategory.{v,u}) (i : Fin (rank C)) : ℂ :=
  unitScalar C (rootTrace C (𝟙 (simples C i)))

set_option backward.isDefEq.respectTransparency false in
/-- All natural-root simple dimensions are nonzero. -/
theorem rootDimension_ne_zero (i : Fin (rank C)) :
    rootDimension C i ≠ 0 := by
  let : Simple (simples C i) := simples_simple C i
  change unitScalar C (rootTrace C (𝟙 (simples C i))) ≠ 0
  rw [rootTrace_id, Ground.unitScalar_eq_equiv]
  exact (Ground.unitScalarEquiv C).toRingEquiv.map_ne_zero_iff.mpr
    (rightQuantumTrace_simple_ne_zero (X := simples C i)
      ((fourthDualRootNaturalIso C).app (simples C i)))

/-- The matrix of traces of the actual natural-root multiplicity defects. -/
def enoTraceMatrix (C : BraidedFusionCategory.{v,u}) (i : Fin (rank C)) :
    Fin (rank C) → Fin (rank C) → ℂ := fun j k =>
  LinearMap.trace ℂ _ (multiplicityDefect C i j k).toLinearMap

/-- The root-dimension vector is an eigenvector of every trace matrix. -/
abbrev ENOTraceMatrixEigenvector (C : BraidedFusionCategory.{v,u}) : Prop :=
  ∀ i j, ∑ k, enoTraceMatrix C i j k * rootDimension C k =
    rootDimension C i * rootDimension C j

/-- Intrinsic simple norms are the squared complex norms of their root dimensions. -/
abbrev RootNormIdentity (C : BraidedFusionCategory.{v,u}) : Prop :=
  ∀ i, squaredNorm C (simples C i) = ((‖rootDimension C i‖ ^ 2 : ℝ) : ℂ)

/-- The trace of an involutive multiplicity defect is bounded by its multiplicity. -/
theorem enoTraceMatrix_norm_le_fusionCoeff {i j k : Fin (rank C)}
    (h : (multiplicityDefect C i j k).toLinearMap *
      (multiplicityDefect C i j k).toLinearMap = 1) :
    ‖enoTraceMatrix C i j k‖ ≤ (fusionCoeff C i j k : ℝ) := by
  obtain ⟨n, hn, hb⟩ := multiplicityDefect_trace_integer_bound C h
  change ‖LinearMap.trace ℂ _ (multiplicityDefect C i j k).toLinearMap‖ ≤ _
  rw [hn, Complex.norm_intCast, ← Int.cast_abs]
  exact_mod_cast hb

/-- Once the categorical multiplicity defects are involutive and their trace
matrix has the natural-root dimension vector as an eigenvector, ENO's FP
bound follows. Both remaining identities are explicit hypotheses. -/
theorem rootDimension_norm_le_fp_of_trace_matrix {i : Fin (rank C)}
    (hinv : ∀ j k, (multiplicityDefect C i j k).toLinearMap *
      (multiplicityDefect C i j k).toLinearMap = 1)
    (heig : ∀ j, ∑ k, enoTraceMatrix C i j k * rootDimension C k =
      rootDimension C i * rootDimension C j) :
    ‖rootDimension C i‖ ≤ fpSimple C i :=
  weighted_eigenvalue_bound (fun j k ↦ fusionCoeff C i j k) (enoTraceMatrix C i)
    (fpSimple C) (rootDimension C) (rootDimension_ne_zero C (unitIndex C)) (fpSimple_pos C)
    (fun _ _ ↦ Nat.cast_nonneg _) (fun j k ↦ enoTraceMatrix_norm_le_fusionCoeff C (hinv j k))
    (fun j ↦ (fpSimple_mul C i j).symm) heig

end PropertyF.Ground.Dimensions

end

@[expose] public noncomputable section
open scoped BigOperators
namespace PropertyF.Ground.Dimensions

/-- Dividing a complex number by its positive norm gives a unit-norm phase. -/
theorem norm_div_ofReal_eq_one {z : ℂ} {r : ℝ} (hr : 0 < r) (h : ‖z‖ = r) :
    ‖z / (r : ℂ)‖ = 1 := by
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr, h, div_self (ne_of_gt hr)]

/-- If a complex weighted sum reaches its nonnegative termwise norm bound,
all its positive-weight terms equal their respective bounds. -/
theorem complex_weighted_saturation {ι : Type*} [Fintype ι]
    {N f : ι → ℝ} {x : ι → ℂ} (hf : ∀ k, 0 < f k)
    (hdom : ∀ k, ‖x k‖ ≤ N k)
    (heq : ∑ k, x k * (f k : ℂ) = ((∑ k, N k * f k : ℝ) : ℂ)) :
    ∀ k, x k = (N k : ℂ) := by
  classical
  have hnonneg (k : ι) : 0 ≤ (N k - (x k).re) * f k :=
    mul_nonneg (sub_nonneg.mpr (le_trans (Complex.re_le_norm _) (hdom k))) (le_of_lt (hf k))
  have hsum : ∑ k, (N k - (x k).re) * f k = 0 := by
    simpa only [Complex.re_sum, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, sub_zero, sub_mul, Finset.sum_sub_distrib, sub_eq_zero] using
      (congrArg Complex.re heq).symm
  intro k
  have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hnonneg j)).1 hsum k (Finset.mem_univ k)
  have hre : (x k).re = N k :=
    (sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_right (ne_of_gt (hf k)))).symm
  have him : (x k).im = 0 := Complex.abs_re_eq_norm.mp <| by
    rw [hre, abs_of_nonneg ((norm_nonneg _).trans (hdom k))]
    exact le_antisymm (hre ▸ Complex.re_le_norm _) (hdom k)
  apply Complex.ext <;> simp [hre, him]

/-- Saturation of a weighted complex eigenvector forces each entry to have
  the phase of the product of its eigenvector values. -/
theorem weighted_eigenvalue_saturation {ι : Type*} [Fintype ι]
    {N : ι → ι → ι → ℝ} {T : ι → ι → ι → ℂ} {f : ι → ℝ} {d : ι → ℂ}
    (hf : ∀ i, 0 < f i) (hmul : ∀ i j, f i * f j = ∑ k, N i j k * f k)
    (hd : ∀ i, ‖d i‖ = f i) (hdom : ∀ i j k, ‖T i j k‖ ≤ N i j k)
    (heig : ∀ i j, ∑ k, T i j k * d k = d i * d j) :
    ∀ i j k, T i j k * (d k / (f k : ℂ)) /
      ((d i / (f i : ℂ)) * (d j / (f j : ℂ))) = (N i j k : ℂ) := by
  classical
  let q : ι → ℂ := fun i => d i / (f i : ℂ)
  have hq : ∀ i, ‖q i‖ = 1 := fun i ↦ norm_div_ofReal_eq_one (hf i) (hd i)
  have hqn : ∀ i, q i ≠ 0 := fun i => norm_pos_iff.mp (by rw [hq]; norm_num)
  have hrepr (i) : q i * (f i : ℂ) = d i :=
    div_mul_cancel₀ _ (by exact_mod_cast (ne_of_gt (hf i)))
  intro i j k
  let x : ι → ℂ := fun l => T i j l * q l / (q i * q j)
  have hx : ∀ l, ‖x l‖ ≤ N i j l := by
    intro l
    dsimp [x]
    rw [norm_div, norm_mul, norm_mul, hq l, hq i, hq j]
    simpa using hdom i j l
  have heq : ∑ l, x l * (f l : ℂ) = ((∑ l, N i j l * f l : ℝ) : ℂ) := by
    calc
      _ = (∑ l, T i j l * d l) / (q i * q j) := by
        rw [Finset.sum_div]
        refine Finset.sum_congr rfl fun l _ ↦ ?_
        rw [← hrepr l]
        dsimp [x]
        ring
      _ = (d i * d j) / (q i * q j) := by rw [heig]
      _ = ((f i * f j : ℝ) : ℂ) := by
        rw [← hrepr i, ← hrepr j, Complex.ofReal_mul]
        field_simp [hqn i, hqn j]
      _ = _ := by rw [hmul]
  exact complex_weighted_saturation hf hx heq k

end PropertyF.Ground.Dimensions
