module
public import PropertyF.Ground.Calculus.GaloisMatrices
public import PropertyF.Ground.Calculus.BraidTraceBound
public import PropertyF.BlockTrace

/-! Semilinear Galois transport of actual finite braid-algebra blocks. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
open scoped BigOperators
namespace PropertyF.Ground.Calculus
universe v u

set_option backward.isDefEq.respectTransparency false in
/-- Any finite actual braid image has a semilinear block presentation whose
group elements are unitary and whose weighted trace is the Galois transform
of the categorical trace. -/
theorem exists_galois_unitary_braid_blocks
    (C : Ground.BraidedFusionCategory.{v,u}) (X : C.Obj) (n : ℕ)
    (hfinite : Finite (braidImage X n)) (p : Dimensions.PivotalStructure (C := C.Obj))
    (σ : ℂ ≃+* ℂ) :
    ∃ (r : ℕ) (size : Fin r → ℕ)
      (T : braidAlgebra X n ≃+* ∀ i, Matrix (Fin (size i)) (Fin (size i)) ℂ)
      (mult : Fin (Ground.rank C) → Fin r → ℕ),
      (∀ i, 0 < size i) ∧
      (∀ i, ∃ j, 0 < mult j i) ∧
      (∀ g i, T (groupInImage (braidEndRepresentation X n) g) i ∈
        Matrix.unitaryGroup (Fin (size i)) ℂ) ∧
      (∀ (z : ℂ) a, T (z • a) = σ z • T a) ∧
      (∀ a : braidAlgebra X n, σ (Dimensions.groundUnitScalarEquiv C
        (p.rightTrace (a : End (tensorPower X (n + 2))).asHom)) =
        ∑ j, (∑ i, (mult i j : ℂ) * σ (Dimensions.groundUnitScalarEquiv C
          (p.rightTrace (𝟙 (Ground.simples C i))))) * (T a j).trace) := by
  classical
  let _ : Fintype (braidImage X n) := Fintype.ofFinite _
  obtain ⟨r, size, b, mult, hsize, _, hret, _, htrace⟩ :=
    exists_unitary_braid_trace_blocks C X n hfinite p (Dimensions.groundUnitScalarEquiv C)
  let rep (i : Fin r) : braidImage X n →* Matrix (Fin (size i)) (Fin (size i)) ℂ :=
    { toFun := fun g => b (groupInImage (braidEndRepresentation X n) g) i
      map_one' := by simp
      map_mul' := by intros; simp }
  choose P hunit htr hsmul using fun i => exists_galois_unitary_matrix_equiv σ (rep i).toHomUnits
  let T := b.toRingEquiv.trans (RingEquiv.piCongrRight (fun i => galoisMatrixEquiv σ (P i)))
  refine ⟨r, size, T, mult, hsize, hret, ?_, ?_, ?_⟩
  · intro g i
    exact hunit i g
  · intro z a
    funext i
    change galoisMatrixEquiv σ (P i) (b (z • a) i) =
      σ z • galoisMatrixEquiv σ (P i) (b a i)
    simp only [map_smul, Pi.smul_apply, hsmul]
  · intro a
    rw [htrace]
    simp only [map_sum, map_mul, map_natCast]
    apply Finset.sum_congr rfl
    intro j _
    congr 1
    exact (htr j (b a j)).symm

/-- Positive original dimensions with real Galois conjugates give nonzero
real weights on the transported actual braid blocks. -/
theorem exists_galois_real_braid_trace_blocks
    (C : Ground.BraidedFusionCategory.{v,u}) (X : C.Obj) (n : ℕ)
    (hfinite : Finite (braidImage X n)) (p : Dimensions.PivotalStructure (C := C.Obj))
    (σ : ℂ ≃+* ℂ) (original conjugate : Fin (Ground.rank C) → ℝ)
    (hpos : ∀ i, 0 < original i)
    (hdim : ∀ i, Dimensions.groundUnitScalarEquiv C
      (p.rightTrace (𝟙 (Ground.simples C i))) = (original i : ℂ))
    (hreal : ∀ i, σ (original i : ℂ) = (conjugate i : ℂ)) :
    ∃ (r : ℕ) (size : Fin r → ℕ)
      (T : braidAlgebra X n ≃+* ∀ i, Matrix (Fin (size i)) (Fin (size i)) ℂ)
      (w : Fin r → ℝ),
      (∀ i, 0 < size i) ∧ (∀ i, w i ≠ 0) ∧
      (∀ g i, T (groupInImage (braidEndRepresentation X n) g) i ∈
        Matrix.unitaryGroup (Fin (size i)) ℂ) ∧
      (∀ (z : ℂ) a, T (z • a) = σ z • T a) ∧
      (∀ a : braidAlgebra X n, σ (Dimensions.groundUnitScalarEquiv C
        (p.rightTrace (a : End (tensorPower X (n + 2))).asHom)) =
          (PropertyF.Blocks.mk r size).trace w (T a)) := by
  classical
  obtain ⟨r, size, T, mult, hsize, hret, hunit, hsmul, htrace⟩ :=
    exists_galois_unitary_braid_blocks C X n hfinite p σ
  let w : Fin r → ℝ := fun j => ∑ i, (mult i j : ℝ) * conjugate i
  refine ⟨r, size, T, w, hsize, ?_, hunit, hsmul, ?_⟩
  · intro j
    have hn := transported_weight_ne_zero (fun i => mult i j) original σ hpos (hret j)
    simp only [hreal, ← Complex.ofReal_natCast, ← Complex.ofReal_mul,
      ← Complex.ofReal_sum] at hn
    exact_mod_cast hn
  · intro a
    rw [htrace]
    simp only [PropertyF.Blocks.trace, w, Complex.ofReal_sum, Complex.ofReal_mul,
      Complex.ofReal_natCast, hdim, hreal]

end PropertyF.Ground.Calculus
