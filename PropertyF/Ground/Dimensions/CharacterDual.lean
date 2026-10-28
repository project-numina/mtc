module
public import PropertyF.Ground.Dimensions.DimensionCharacter
public import PropertyF.Ground.Integrate.CharacterReality
public import PropertyF.Ground.Dimensions.IntrinsicNonzero
public import Mathlib.CategoryTheory.Monoidal.Rigid.Braided

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
open scoped BigOperators Matrix ComplexOrder
namespace PropertyF.Ground.Dimensions
universe v u

/-- Eigenvalues on a common eigenvector for a real matrix and its transpose
are complex conjugates. -/
theorem conjugate_of_transpose_eigenvector {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℂ) (hA : ∀ i j, star (A i j) = A i j)
    (v : ι → ℂ) (hv : v ≠ 0) (z w : ℂ)
    (h : A *ᵥ v = z • v) (ht : Aᵀ *ᵥ v = w • v) : star w = z := by
  have hAt : Aᵀᴴ = A := by
    ext i j
    simp [Matrix.conjTranspose_apply, hA]
  have hs : (star v) ᵥ* A = (star w) • (star v) := by
    have hh := congrArg star ht
    rw [Matrix.star_mulVec, hAt] at hh
    simpa using hh
  have hn : star v ⬝ᵥ v ≠ 0 := by
    intro hz
    exact hv (dotProduct_star_self_eq_zero.mp hz)
  have heq : z * (star v ⬝ᵥ v) = (star w) * (star v ⬝ᵥ v) := by
    calc
      _ = star v ⬝ᵥ (A *ᵥ v) := by rw [h, dotProduct_smul]; rfl
      _ = (star v ᵥ* A) ⬝ᵥ v := Matrix.dotProduct_mulVec _ _ _
      _ = _ := by rw [hs, smul_dotProduct]; rfl
  exact (mul_right_cancel₀ hn heq).symm

/-- Every nonzero fusion character takes complex-conjugate values on dual
simple objects, with no pivotal or spherical hypothesis. -/
theorem fusion_character_dual_eq_conj (C : Ground.BraidedFusionCategory.{v,u})
    (χ : Fin (Ground.rank C) → ℂ) (i₀ : Fin (Ground.rank C)) (hχ : χ i₀ ≠ 0)
    (hchar : ∀ i j, χ i * χ j = ∑ k, (Ground.fusionCoeff C i j k : ℂ) * χ k)
    (i : Fin (Ground.rank C)) : χ (Ground.dualIndex C i) = star (χ i) := by
  classical
  let A : Matrix (Fin (Ground.rank C)) (Fin (Ground.rank C)) ℂ :=
    fun j k => (Ground.fusionCoeff C i j k : ℂ)
  have hv : χ ≠ 0 := by
    intro hz
    apply hχ
    exact congrFun hz i₀
  have h : A *ᵥ χ = χ i • χ := by
    ext j
    change (∑ k, (Ground.fusionCoeff C i j k : ℂ) * χ k) = χ i * χ j
    exact (hchar i j).symm
  have ht : Aᵀ *ᵥ χ = χ (Ground.dualIndex C i) • χ := by
    ext j
    change (∑ k, (Ground.fusionCoeff C i k j : ℂ) * χ k) =
      χ (Ground.dualIndex C i) * χ j
    simp_rw [Ground.fusionCoeff_dual_transpose C i]
    exact (hchar (Ground.dualIndex C i) j).symm
  have heq := conjugate_of_transpose_eigenvector A (by intro j k; simp [A]) χ hv
    (χ i) (χ (Ground.dualIndex C i)) h ht
  have hh := congrArg star heq
  simpa using hh

/-- Simple pivotal dimensions on duals are conjugate, for any pivotal
structure on a genuine braided fusion category. -/
theorem pivotalDimension_dual_eq_conj (C : Ground.BraidedFusionCategory.{v,u})
    (p : PivotalStructure (C := C.Obj)) (i : Fin (Ground.rank C)) :
    pivotalDimension C p (Ground.simples C (Ground.dualIndex C i)) =
      star (pivotalDimension C p (Ground.simples C i)) := by
  apply fusion_character_dual_eq_conj C
    (fun j => pivotalDimension C p (Ground.simples C j)) (Ground.unitIndex C)
  · obtain ⟨e⟩ := Ground.unitIndex_iso C
    rw [pivotalDimension_iso C p e, pivotalDimension_unit]
    exact one_ne_zero
  · exact pivotalDimension_character C p

/-- Galois conjugates of pivotal dimensions also interchange complex
conjugation and duality. -/
theorem galois_pivotalDimension_dual_eq_conj (C : Ground.BraidedFusionCategory.{v,u})
    (p : PivotalStructure (C := C.Obj)) (σ : ℂ ≃+* ℂ) (i : Fin (Ground.rank C)) :
    σ (pivotalDimension C p (Ground.simples C (Ground.dualIndex C i))) =
      star (σ (pivotalDimension C p (Ground.simples C i))) := by
  apply fusion_character_dual_eq_conj C
    (fun j => σ (pivotalDimension C p (Ground.simples C j))) (Ground.unitIndex C)
  · obtain ⟨e⟩ := Ground.unitIndex_iso C
    rw [pivotalDimension_iso C p e, pivotalDimension_unit, map_one]
    exact one_ne_zero
  · intro j k
    simpa using congrArg σ (pivotalDimension_character C p j k)

end PropertyF.Ground.Dimensions
