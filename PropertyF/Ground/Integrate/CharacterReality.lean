module
public import PropertyF.Ground.Fusion.Agreement
public import Mathlib.LinearAlgebra.Matrix.DotProduct
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.Analysis.RCLike.Basic

/-! Reality of self-dual fusion characters via transposed fusion matrices. -/

@[expose] public noncomputable section
open CategoryTheory
open scoped BigOperators Matrix ComplexOrder
namespace PropertyF.Ground
universe v u

/-- Left and right eigenvectors with nonzero pairing have the same eigenvalue. -/
theorem eigenvalue_eq_of_dotProduct_ne_zero {ι K : Type*} [Fintype ι]
    [CommSemiring K] [IsDomain K] {A : Matrix ι ι K} {u v : ι → K} {z w : K}
    (h : A *ᵥ v = z • v) (ht : u ᵥ* A = w • u) (hn : u ⬝ᵥ v ≠ 0) : z = w :=
  mul_right_cancel₀ hn <| by
    simpa only [h, ht, dotProduct_smul, smul_dotProduct, smul_eq_mul] using
      Matrix.dotProduct_mulVec u A v

/-- If a matrix has conjugation-invariant entries, its eigenvalue and that of
its transpose on a common nonzero eigenvector are conjugate. -/
theorem conjugate_of_transpose_eigenvector {ι K : Type*} [Fintype ι] [RCLike K]
    (A : Matrix ι ι K) (hA : ∀ i j, star (A i j) = A i j)
    {v : ι → K} (hv : v ≠ 0) {z w : K}
    (h : A *ᵥ v = z • v) (ht : Aᵀ *ᵥ v = w • v) : star w = z := by
  have hAt : Aᵀᴴ = A := Matrix.ext fun i j ↦ by simpa [Matrix.conjTranspose_apply] using hA i j
  exact (eigenvalue_eq_of_dotProduct_ne_zero h
    (by simpa [Matrix.star_mulVec, hAt] using congrArg star ht)
    (fun hz ↦ hv (dotProduct_star_self_eq_zero.mp hz))).symm

/-- A multiplicative character is an eigenvector of each fusion matrix. -/
theorem fusion_character_eigenvector {ι K : Type*} [Fintype ι] [Semiring K]
    {N : ι → ι → ι → K} {χ : ι → K} (hchar : ∀ i j, χ i * χ j = ∑ k, N i j k * χ k)
    (i : ι) : (fun j k ↦ N i j k) *ᵥ χ = χ i • χ :=
  funext fun j ↦ (hchar i j).symm

variable {ι K : Type*} [Fintype ι] [RCLike K] {N : ι → ι → ι → ℕ} {d : ι → ι}
variable {χ : ι → K} {i₀ : ι}
variable (hN : ∀ i j k, N (d i) j k = N i k j)
variable (hχ : χ i₀ ≠ 0) (hchar : ∀ i j, χ i * χ j = ∑ k, (N i j k : K) * χ k)
include hN hχ hchar

/-- A nonzero character takes conjugate values on labels with transposed multiplication matrices. -/
theorem fusion_character_dual_eq_conj (i : ι) : χ (d i) = star (χ i) := by
  simpa using congrArg star (conjugate_of_transpose_eigenvector (fun j k ↦ (N i j k : K))
    (fun j k ↦ star_natCast _) (fun hz ↦ hχ (congrFun hz i₀))
    (fusion_character_eigenvector hchar i) (by
      have hA : (fun j k ↦ (N (d i) j k : K)) = (fun j k ↦ (N i j k : K))ᵀ :=
        Matrix.ext fun j k ↦ congrArg (fun n : ℕ ↦ (n : K)) (hN i j k)
      simpa only [hA] using fusion_character_eigenvector hchar (d i)))

variable (hdual : ∀ i, χ (d i) = χ i)
include hdual

/-- A nonzero fusion character invariant under duality has real values. -/
theorem selfDual_character_real (i : ι) :
    star (χ i) = χ i :=
  (fusion_character_dual_eq_conj hN hχ hchar i).symm.trans (hdual i)

/-- Every field conjugate of a self-dual fusion character is real as well. -/
theorem selfDual_character_galois_real (σ : K ≃+* K) (i : ι) :
    star (σ (χ i)) = σ (χ i) :=
  selfDual_character_real (χ := fun j ↦ σ (χ j)) (i₀ := i₀) hN ((map_ne_zero σ).2 hχ)
    (fun j k ↦ by simpa using congrArg σ (hchar j k)) (fun j ↦ by rw [hdual]) i

omit hN hχ hchar hdual
variable (C : BraidedFusionCategory.{v,u})

/-- Every Galois conjugate of an actual simple FP dimension is real. -/
theorem fp_simple_galois_real (σ : ℂ ≃+* ℂ) (i : Fin (rank C)) :
    (((σ (fpSimple C i : ℂ)).re : ℝ) : ℂ) = σ (fpSimple C i : ℂ) :=
  Complex.conj_eq_iff_re.mp <| by simpa only [← Complex.star_def] using (
    selfDual_character_galois_real (N := fusionCoeff C) (d := dualIndex C)
      (χ := fun i ↦ (fpSimple C i : ℂ)) (i₀ := unitIndex C)
      (fun i j k ↦ (fusionCoeff_dual_symmetry C i j k).symm)
      (by simp [fpSimple_unit]) (fpSimple_isFusionMultiplicative C) (by simp [fpSimple_dual]) σ i)

end PropertyF.Ground
