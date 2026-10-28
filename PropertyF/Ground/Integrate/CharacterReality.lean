module
public import PropertyF.Ground.Fusion.Agreement
public import Mathlib.LinearAlgebra.Matrix.DotProduct
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.Analysis.RCLike.Basic
public import PropertyF.Ground.Fusion.Simples

/-! # Representatives and real fusion characters

Mutually covering families of pairwise nonisomorphic objects have equivalent
index types. For a finite multiplication table with dual-transpose symmetry,
nonzero characters take conjugate values at dual labels.

## Main results

* `representatives_equiv` constructs the equivalence of representative labels.
* `selfDual_character_galois_real` shows that conjugates of self-dual characters are real.
-/

@[expose] public noncomputable section
open CategoryTheory
open scoped BigOperators
namespace PropertyF.Ground
universe v u
variable {C : Type u} [Category.{v} C] {ι κ : Type*}

/-- Two complete, pairwise nonisomorphic families of objects have equivalent indices. -/
theorem representatives_equiv (S : ι → C) (T : κ → C)
    (hS : ∀ i j, Nonempty (S i ≅ S j) → i = j) (hT : ∀ i j, Nonempty (T i ≅ T j) → i = j)
    (hST : ∀ i, ∃ j, Nonempty (S i ≅ T j)) (hTS : ∀ j, ∃ i, Nonempty (S i ≅ T j)) :
    ∃ e : ι ≃ κ, ∀ i, Nonempty (S i ≅ T (e i)) := by
  classical
  choose f hf using hST
  refine ⟨Equiv.ofBijective f ⟨?_, ?_⟩, hf⟩
  · intro i j hij
    exact hS i j <| (hf i).elim fun ei ↦
      (hf j).map fun ej ↦ ei ≪≫ eqToIso (congrArg T hij) ≪≫ ej.symm
  · intro j
    obtain ⟨i, e⟩ := hTS j
    exact ⟨i, hT _ _ ((hf i).elim fun ei ↦ e.map fun e ↦ ei.symm ≪≫ e)⟩

end PropertyF.Ground
end

/-! Reality of self-dual fusion characters via transposed fusion matrices. -/

@[expose] public noncomputable section
open CategoryTheory
open scoped BigOperators Matrix ComplexOrder
namespace PropertyF.Ground
universe v u
variable {ι K : Type*} [Fintype ι]

/-- Left and right eigenvectors with nonzero pairing have the same eigenvalue. -/
theorem eigenvalue_eq_of_dotProduct_ne_zero [CommSemiring K] [IsDomain K] {A : Matrix ι ι K} {u v : ι → K} {z w : K}
    (h : A *ᵥ v = z • v) (ht : u ᵥ* A = w • u) (hn : u ⬝ᵥ v ≠ 0) : z = w :=
  mul_right_cancel₀ hn <| by
    simpa only [h, ht, dotProduct_smul, smul_dotProduct, smul_eq_mul] using
      Matrix.dotProduct_mulVec u A v

/-- If a matrix has conjugation-invariant entries, its eigenvalue and that of
its transpose on a common nonzero eigenvector are conjugate. -/
theorem conjugate_of_transpose_eigenvector [RCLike K]
    (A : Matrix ι ι K) (hA : ∀ i j, star (A i j) = A i j)
    {v : ι → K} (hv : v ≠ 0) {z w : K}
    (h : A *ᵥ v = z • v) (ht : Aᵀ *ᵥ v = w • v) : star w = z := by
  have hAt : Aᵀᴴ = A := Matrix.ext fun i j ↦ by simpa [Matrix.conjTranspose_apply] using hA i j
  exact (eigenvalue_eq_of_dotProduct_ne_zero h
    (by simpa [Matrix.star_mulVec, hAt] using congrArg star ht)
    (fun hz ↦ hv (dotProduct_star_self_eq_zero.mp hz))).symm

/-- A multiplicative character is an eigenvector of each fusion matrix. -/
theorem fusion_character_eigenvector [Semiring K]
    {N : ι → ι → ι → K} {χ : ι → K} (hchar : ∀ i j, χ i * χ j = ∑ k, N i j k * χ k)
    (i : ι) : (fun j k ↦ N i j k) *ᵥ χ = χ i • χ :=
  funext fun j ↦ (hchar i j).symm

variable [RCLike K] {N : ι → ι → ι → ℕ} {d : ι → ι}
variable {χ : ι → K} {i₀ : ι}
variable (hN : ∀ i j k, N (d i) j k = N i k j)
variable (hχ : χ i₀ ≠ 0) (hchar : ∀ i j, χ i * χ j = ∑ k, (N i j k : K) * χ k)
include hN hχ hchar

/-- A nonzero character takes conjugate values on labels with transposed multiplication matrices. -/
theorem fusion_character_dual_eq_conj (i : ι) : χ (d i) = star (χ i) := by
  simpa using congrArg star (conjugate_of_transpose_eigenvector (fun j k ↦ (N i j k : K))
    (fun j k ↦ star_natCast _) (fun hz ↦ hχ (congrFun hz i₀))
    (fusion_character_eigenvector hchar i) (by
      change (fun j k ↦ (N i k j : K)) *ᵥ χ = χ (d i) • χ
      simpa only [hN] using fusion_character_eigenvector hchar (d i)))

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

/-- A conjugate of a self-dual character is the image of its real part. -/
theorem selfDual_character_galois_re (σ : K ≃+* K) (i : ι) :
    (RCLike.re (σ (χ i)) : K) = σ (χ i) :=
  RCLike.conj_eq_iff_re.mp <| by
    simpa only [← RCLike.star_def] using selfDual_character_galois_real hN hχ hchar hdual σ i

omit hN hχ hchar hdual
variable (C : BraidedFusionCategory.{v,u})

/-- Every Galois conjugate of an actual simple FP dimension is real. -/
theorem fp_simple_galois_real (σ : ℂ ≃+* ℂ) (i : Fin (rank C)) :
    (((σ (fpSimple C i : ℂ)).re : ℝ) : ℂ) = σ (fpSimple C i : ℂ) :=
  by simpa only [RCLike.re_eq_complex_re, RCLike.ofReal_eq_complex_ofReal] using
    selfDual_character_galois_re (N := fusionCoeff C) (d := dualIndex C)
      (χ := fun i ↦ (fpSimple C i : ℂ)) (i₀ := unitIndex C)
      (fun i j k ↦ (fusionCoeff_dual_symmetry C i j k).symm)
      (by simp [fpSimple_unit]) (fpSimple_isFusionMultiplicative C) (by simp [fpSimple_dual]) σ i

end PropertyF.Ground
