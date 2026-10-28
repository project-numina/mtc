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

/-- An eigenvalue shared by a real matrix and its transpose on the same
nonzero complex eigenvector is real. -/
theorem real_of_common_transpose_eigenvector {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℂ) (hA : ∀ i j, star (A i j) = A i j)
    (v : ι → ℂ) (hv : v ≠ 0) (z : ℂ)
    (h : A *ᵥ v = z • v) (ht : Aᵀ *ᵥ v = z • v) : star z = z := by
  have hAt : Aᵀᴴ = A := by
    ext i j
    simp [Matrix.conjTranspose_apply, hA]
  have hs : (star v) ᵥ* A = (star z) • (star v) := by
    have hh := congrArg star ht
    rw [Matrix.star_mulVec, hAt] at hh
    simpa using hh
  have hn : star v ⬝ᵥ v ≠ 0 := by
    intro hz
    exact hv (dotProduct_star_self_eq_zero.mp hz)
  have heq : z * (star v ⬝ᵥ v) = (star z) * (star v ⬝ᵥ v) := by
    calc
      _ = star v ⬝ᵥ (A *ᵥ v) := by rw [h, dotProduct_smul]; rfl
      _ = (star v ᵥ* A) ⬝ᵥ v := Matrix.dotProduct_mulVec _ _ _
      _ = _ := by rw [hs, smul_dotProduct]; rfl
  exact (mul_right_cancel₀ hn heq).symm

/-- Frobenius reciprocity identifies the transpose of the fusion matrix of a
simple with the fusion matrix of its dual. -/
theorem fusionCoeff_dual_transpose (C : BraidedFusionCategory) (i j k : Fin (rank C)) :
    fusionCoeff C i j k = fusionCoeff C (dualIndex C i) k j := by
  rw [fusionCoeff_comm C i j, fusionCoeff_reciprocity_labels,
    fusionCoeff_comm C k (dualIndex C i)]

/-- A nonzero fusion character invariant under duality has real values. -/
theorem selfDual_character_real (C : BraidedFusionCategory)
    (χ : Fin (rank C) → ℂ) (i₀ : Fin (rank C)) (hχ : χ i₀ ≠ 0)
    (hchar : ∀ i j, χ i * χ j = ∑ k, (fusionCoeff C i j k : ℂ) * χ k)
    (hdual : ∀ i, χ (dualIndex C i) = χ i) (i : Fin (rank C)) :
    star (χ i) = χ i := by
  classical
  let A : Matrix (Fin (rank C)) (Fin (rank C)) ℂ :=
    fun j k => (fusionCoeff C i j k : ℂ)
  have hv : χ ≠ 0 := by
    intro hz
    apply hχ
    exact congrFun hz i₀
  have h : A *ᵥ χ = χ i • χ := by
    ext j
    change (∑ k, (fusionCoeff C i j k : ℂ) * χ k) = χ i * χ j
    exact (hchar i j).symm
  have ht : Aᵀ *ᵥ χ = χ i • χ := by
    ext j
    change (∑ k, (fusionCoeff C i k j : ℂ) * χ k) = χ i * χ j
    simp_rw [fusionCoeff_dual_transpose C i]
    rw [← hdual i]
    exact (hchar (dualIndex C i) j).symm
  apply real_of_common_transpose_eigenvector A _ χ hv (χ i) h ht
  intro j k
  simp [A]

/-- Every field conjugate of a self-dual fusion character is real as well. -/
theorem selfDual_character_galois_real (C : BraidedFusionCategory)
    (χ : Fin (rank C) → ℂ) (i₀ : Fin (rank C)) (hχ : χ i₀ ≠ 0)
    (hchar : ∀ i j, χ i * χ j = ∑ k, (fusionCoeff C i j k : ℂ) * χ k)
    (hdual : ∀ i, χ (dualIndex C i) = χ i) (σ : ℂ ≃+* ℂ) (i : Fin (rank C)) :
    star (σ (χ i)) = σ (χ i) := by
  apply selfDual_character_real C (fun j => σ (χ j)) i₀
  · exact (map_ne_zero σ).2 hχ
  · intro j k
    simpa using congrArg σ (hchar j k)
  · intro j
    rw [hdual]

/-- Every Galois conjugate of an actual simple FP dimension is real. -/
theorem fp_simple_galois_real (C : BraidedFusionCategory.{v,u})
    (σ : ℂ ≃+* ℂ) (i : Fin (rank C)) :
    (((σ (fpSimple C i : ℂ)).re : ℝ) : ℂ) = σ (fpSimple C i : ℂ) := by
  let χ : Fin (rank C) → ℂ := fun i => (fpSimple C i : ℂ)
  have hχ : χ (unitIndex C) ≠ 0 := by simp [χ, fpSimple_unit]
  have hchar : ∀ i j, χ i * χ j = ∑ k, (fusionCoeff C i j k : ℂ) * χ k := by
    intro i j
    dsimp [χ]
    exact_mod_cast fpSimple_mul C i j
  have hdual : ∀ i, χ (dualIndex C i) = χ i := by intro i; simp [χ, fpSimple_dual]
  apply Complex.conj_eq_iff_re.mp
  simpa only [← Complex.star_def] using selfDual_character_galois_real C χ (unitIndex C)
    hχ hchar hdual σ i

end PropertyF.Ground
