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
variable (C : BraidedFusionCategory.{v,u})

/-- Frobenius reciprocity identifies the transpose of the fusion matrix of a
simple with the fusion matrix of its dual. -/
theorem fusionCoeff_dual_transpose (i j k : Fin (rank C)) :
    fusionCoeff C i j k = fusionCoeff C (dualIndex C i) k j := by
  rw [fusionCoeff_comm C i j, fusionCoeff_reciprocity_labels,
    fusionCoeff_comm C k (dualIndex C i)]

/-- Eigenvalues on a common eigenvector for a real matrix and its transpose
are complex conjugates. -/
theorem conjugate_of_transpose_eigenvector {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℂ) (hA : ∀ i j, star (A i j) = A i j)
    {v : ι → ℂ} (hv : v ≠ 0) {z w : ℂ}
    (h : A *ᵥ v = z • v) (ht : Aᵀ *ᵥ v = w • v) : star w = z := by
  have hAt : Aᵀᴴ = A := Matrix.ext fun i j ↦ by simpa [Matrix.conjTranspose_apply] using hA i j
  have hs : (star v) ᵥ* A = (star w) • (star v) := by
    simpa [Matrix.star_mulVec, hAt] using congrArg star ht
  have hn : star v ⬝ᵥ v ≠ 0 := fun hz ↦ hv (dotProduct_star_self_eq_zero.mp hz)
  have heq : z * (star v ⬝ᵥ v) = (star w) * (star v ⬝ᵥ v) := by
    calc
      _ = star v ⬝ᵥ (A *ᵥ v) := by rw [h, dotProduct_smul]; rfl
      _ = (star v ᵥ* A) ⬝ᵥ v := Matrix.dotProduct_mulVec _ _ _
      _ = _ := by rw [hs, smul_dotProduct]; rfl
  exact (mul_right_cancel₀ hn heq).symm

variable {χ : Fin (rank C) → ℂ} {i₀ : Fin (rank C)}

/-- A fusion character is an eigenvector of each fusion matrix. -/
theorem fusion_character_eigenvector (hchar : IsFusionMultiplicative C χ) (i : Fin (rank C)) :
    (fun j k ↦ (fusionCoeff C i j k : ℂ)) *ᵥ χ = χ i • χ :=
  funext fun j ↦ (hchar i j).symm

/-- Every nonzero fusion character takes complex-conjugate values on dual
simple objects, with no pivotal or spherical hypothesis. -/
theorem fusion_character_dual_eq_conj (hχ : χ i₀ ≠ 0)
    (hchar : IsFusionMultiplicative C χ)
    (i : Fin (rank C)) : χ (dualIndex C i) = star (χ i) := by
  classical
  let A : Matrix (Fin (rank C)) (Fin (rank C)) ℂ :=
    fun j k => (fusionCoeff C i j k : ℂ)
  have hv : χ ≠ 0 := fun hz ↦ hχ (congrFun hz i₀)
  have h : A *ᵥ χ = χ i • χ := fusion_character_eigenvector C hchar i
  have ht : Aᵀ *ᵥ χ = χ (dualIndex C i) • χ := by
    convert fusion_character_eigenvector C hchar (dualIndex C i) using 1
    congr 1
    ext j k
    change (fusionCoeff C i k j : ℂ) = _
    exact_mod_cast fusionCoeff_dual_transpose C i k j
  simpa using congrArg star (conjugate_of_transpose_eigenvector A (by intro j k; simp [A]) hv h ht)

/-- A nonzero fusion character invariant under duality has real values. -/
theorem selfDual_character_real (hχ : χ i₀ ≠ 0)
    (hchar : IsFusionMultiplicative C χ)
    (hdual : ∀ i, χ (dualIndex C i) = χ i) (i : Fin (rank C)) :
    star (χ i) = χ i :=
  (fusion_character_dual_eq_conj C hχ hchar i).symm.trans (hdual i)

/-- Every field conjugate of a self-dual fusion character is real as well. -/
theorem selfDual_character_galois_real (hχ : χ i₀ ≠ 0)
    (hchar : IsFusionMultiplicative C χ)
    (hdual : ∀ i, χ (dualIndex C i) = χ i) (σ : ℂ ≃+* ℂ) (i : Fin (rank C)) :
    star (σ (χ i)) = σ (χ i) :=
  selfDual_character_real C (χ := fun j ↦ σ (χ j)) (i₀ := i₀) ((map_ne_zero σ).2 hχ)
    (fun j k ↦ by simpa using congrArg σ (hchar j k)) (fun j ↦ by rw [hdual]) i

/-- Every Galois conjugate of an actual simple FP dimension is real. -/
theorem fp_simple_galois_real (σ : ℂ ≃+* ℂ) (i : Fin (rank C)) :
    (((σ (fpSimple C i : ℂ)).re : ℝ) : ℂ) = σ (fpSimple C i : ℂ) :=
  Complex.conj_eq_iff_re.mp <| by
    simpa only [← Complex.star_def] using
      selfDual_character_galois_real C (χ := fun i ↦ (fpSimple C i : ℂ))
        (i₀ := unitIndex C) (by simp [fpSimple_unit]) (fpSimple_isFusionMultiplicative C)
        (by intro i; simp [fpSimple_dual]) σ i

end PropertyF.Ground
