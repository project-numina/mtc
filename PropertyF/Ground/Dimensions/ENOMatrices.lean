module
public import PropertyF.Ground.Fusion.Agreement
public import PropertyF.Ground.Dimensions.MultiplicityDefect
public import PropertyF.Ground.Dimensions.BiproductTrace
public import PropertyF.Ground.Dimensions.IntrinsicNonzero

/-! # Trace matrices and eigenvalue bounds

Weighted eigenvalue estimates and root traces produce matrix bounds for fusion coefficients.
-/

@[expose] public noncomputable section
open scoped BigOperators
namespace PropertyF.Ground.Dimensions

/-- A matrix dominated entrywise by a nonnegative matrix cannot have an
eigenvalue larger than the latter's positive eigenvalue. -/
theorem weighted_eigenvalue_bound {ι : Type*} [Fintype ι] (N : ι → ι → ℝ)
    (T : ι → ι → ℂ) (f : ι → ℝ) (F : ℝ) (v : ι → ℂ) (z : ℂ)
    (i₀ : ι) (hv : v i₀ ≠ 0) (hf : ∀ i, 0 < f i)
    (hN : ∀ i j, 0 ≤ N i j) (hdom : ∀ i j, ‖T i j‖ ≤ N i j)
    (hfp : ∀ i, ∑ j, N i j * f j = F * f i)
    (heig : ∀ i, ∑ j, T i j * v j = z * v i) :
    ‖z‖ ≤ F := by
  classical
  obtain ⟨i, _, hmax⟩ := Finset.exists_max_image Finset.univ
    (fun j => ‖v j‖ / f j) ⟨i₀, Finset.mem_univ _⟩
  let r := ‖v i‖ / f i
  have hr0 : 0 ≤ r := div_nonneg (norm_nonneg _) (le_of_lt (hf i))
  have hvi : 0 < ‖v i‖ := by
    have h0 : 0 < ‖v i₀‖ / f i₀ := div_pos (norm_pos_iff.mpr hv) (hf i₀)
    have hm : ‖v i₀‖ / f i₀ ≤ r := hmax i₀ (Finset.mem_univ _)
    have hr : 0 < r := lt_of_lt_of_le h0 hm
    exact (div_pos_iff_of_pos_right (hf i)).1 hr
  have hvbound (j : ι) : ‖v j‖ ≤ r * f j := by
    apply (div_le_iff₀ (hf j)).1
    exact hmax j (Finset.mem_univ _)
  have hbound : ‖z‖ * ‖v i‖ ≤ F * ‖v i‖ := by
    calc
      _ = ‖∑ j, T i j * v j‖ := by rw [heig i, norm_mul]
      _ ≤ ∑ j, ‖T i j * v j‖ := by simpa using norm_sum_le Finset.univ (fun j => T i j * v j)
      _ ≤ ∑ j, N i j * (r * f j) := by
        apply Finset.sum_le_sum
        intro j _
        rw [norm_mul]
        exact mul_le_mul (hdom i j) (hvbound j) (norm_nonneg _) (hN i j)
      _ = r * (∑ j, N i j * f j) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = F * ‖v i‖ := by
        rw [hfp i]
        dsimp [r]
        field_simp [ne_of_gt (hf i)]
  exact le_of_mul_le_mul_right hbound hvi

/-- ENO's trace-matrix eigenvalues are bounded by the FP dimension whenever
their entries are dominated by fusion multiplicities. -/
theorem fusion_dominated_eigenvalue_bound (C : BraidedFusionCategory)
    (i : Fin (rank C)) (T : Fin (rank C) → Fin (rank C) → ℂ)
    (v : Fin (rank C) → ℂ) (z : ℂ) (i₀ : Fin (rank C))
    (hv : v i₀ ≠ 0) (hdom : ∀ j k, ‖T j k‖ ≤ Ground.fusionCoeff C i j k)
    (heig : ∀ j, ∑ k, T j k * v k = z * v j) : ‖z‖ ≤ fpSimple C i := by
  apply weighted_eigenvalue_bound (fun j k => Ground.fusionCoeff C i j k) T
    (fpSimple C) (fpSimple C i) v z i₀ hv (Ground.fpSimple_pos C)
  · intro j k
    exact Nat.cast_nonneg _
  · exact hdom
  · intro j
    exact (Ground.fpSimple_mul C i j).symm
  · exact heig

end PropertyF.Ground.Dimensions

end

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
    (f : X ⟶ Y) (g : Y ⟶ X) : rootTrace C (f ≫ g) = rootTrace C (g ≫ f) := by
  apply rightTraceWith_cyclic
  exact (fourthDualRootNaturalIso C).hom.naturality f

/-- The root trace of a finite biproduct is the sum of its diagonal block traces. -/
theorem rootTrace_biproduct
    {ι : Type*} [Fintype ι] (F : ι → C.Obj) [HasBiproduct F]
    (f : (⨁ F) ⟶ (⨁ F)) :
    rootTrace C f = ∑ i, rootTrace C (biproduct.ι F i ≫ f ≫ biproduct.π F i) := by
  classical
  calc
    _ = rootTrace C ((∑ i, biproduct.π F i ≫ biproduct.ι F i) ≫ f) := by
      rw [biproduct.total]; simp
    _ = ∑ i, rootTrace C ((biproduct.π F i ≫ biproduct.ι F i) ≫ f) := by
      rw [Preadditive.sum_comp]
      exact map_sum (rootTraceLinear C _) _ _
    _ = ∑ i, rootTrace C (biproduct.ι F i ≫ f ≫ biproduct.π F i) := by
      apply Finset.sum_congr rfl
      intro i _
      simp only [Category.assoc]
      simpa only [Category.assoc] using rootTrace_cyclic C (biproduct.π F i) (biproduct.ι F i ≫ f)

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
      rootTrace C f = ∑ i, c i • rootTrace C (𝟙 (F i)) := by
  classical
  have h : ∀ i, ∃ c : ℂ, biproduct.ι F i ≫ f ≫ biproduct.π F i = c • 𝟙 (F i) := by
    intro i
    let : Simple (F i) := hs i
    let : FiniteDimensional ℂ (F i ⟶ F i) := Ground.IsFusionCategory.hom_finite _ _
    obtain ⟨c, hc⟩ := endomorphism_simple_eq_smul_id ℂ (biproduct.ι F i ≫ f ≫ biproduct.π F i)
    exact ⟨c, hc.symm⟩
  choose c hc using h
  refine ⟨c, hc, ?_⟩
  rw [rootTrace_biproduct]
  apply Finset.sum_congr rfl
  intro i _
  rw [hc i]
  exact (rootTraceLinear C (F i)).map_smul _ _

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
  Ground.unitScalar C (rootTrace C (𝟙 (simples C i)))

set_option backward.isDefEq.respectTransparency false in
/-- All natural-root simple dimensions are nonzero. -/
theorem rootDimension_ne_zero (i : Fin (rank C)) :
    rootDimension C i ≠ 0 := by
  let : Simple (simples C i) := Ground.simples_simple C i
  have h := rightQuantumTrace_simple_ne_zero C (simples C i)
    ((fourthDualRootNaturalIso C).app (simples C i))
  intro hz
  apply h
  apply (groundUnitScalarEquiv C).injective
  have hz' : Ground.unitScalar C (rightQuantumTrace
      ((fourthDualRootNaturalIso C).app (simples C i))) = 0 := by
    simpa [rootDimension, rootTrace, rightTraceWith, rightQuantumTrace, tensorHom_def] using hz
  simpa only [map_zero, groundUnitScalarEquiv_apply] using hz'

/-- The matrix of traces of the actual natural-root multiplicity defects. -/
def enoTraceMatrix (C : BraidedFusionCategory.{v,u}) (i : Fin (rank C)) :
    Fin (rank C) → Fin (rank C) → ℂ := fun j k =>
  LinearMap.trace ℂ _ (multiplicityDefect C i j k).toLinearMap

/-- Once the categorical multiplicity defects are involutive and their trace
matrix has the natural-root dimension vector as an eigenvector, ENO's FP
bound follows. Both remaining identities are explicit hypotheses. -/
theorem rootDimension_norm_le_fp_of_trace_matrix (i : Fin (rank C))
    (hinv : ∀ j k, (multiplicityDefect C i j k).toLinearMap *
      (multiplicityDefect C i j k).toLinearMap = 1)
    (heig : ∀ j, ∑ k, enoTraceMatrix C i j k * rootDimension C k =
      rootDimension C i * rootDimension C j) :
    ‖rootDimension C i‖ ≤ fpSimple C i := by
  apply fusion_dominated_eigenvalue_bound C i (enoTraceMatrix C i) (rootDimension C)
    (rootDimension C i) (unitIndex C) (rootDimension_ne_zero C _)
  · intro j k
    obtain ⟨n, hn, hb⟩ := multiplicityDefect_trace_integer_bound C i j k (hinv j k)
    change ‖LinearMap.trace ℂ _ (multiplicityDefect C i j k).toLinearMap‖ ≤ _
    rw [hn, Complex.norm_intCast, ← Int.cast_abs]
    exact_mod_cast hb
  · exact heig

end PropertyF.Ground.Dimensions

end
