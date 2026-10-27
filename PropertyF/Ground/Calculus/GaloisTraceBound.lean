module
public import PropertyF.Ground.Calculus.GaloisBlocks

/-! The ordinary trace bound after semilinear Galois transport. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
open scoped BigOperators
namespace PropertyF.Ground.Calculus
universe v u

/-- The ordinary unitary trace bound for any semilinear presentation with the
constructed categorical multiplicities and transported trace formula. -/
theorem galois_unitary_braid_bound_of_weights
    (C : Ground.BraidedFusionCategory.{v,u}) (X : C.Obj) (n : ℕ)
    (p : Dimensions.PivotalStructure (C := C.Obj)) (σ : ℂ ≃+* ℂ)
    (r : ℕ) (size : Fin r → ℕ)
    (T : braidAlgebra X n ≃+* ∀ j, Matrix (Fin (size j)) (Fin (size j)) ℂ)
    (mult : Fin (Ground.rank C) → Fin r → ℕ)
    (hdim : ∀ i, Module.finrank ℂ (Ground.simples C i ⟶ tensorPower X (n + 2)) =
      ∑ j, mult i j * size j)
    (htrace : ∀ a : braidAlgebra X n, σ (Dimensions.groundUnitScalarEquiv C
      (p.rightTrace (a : End (tensorPower X (n + 2))).asHom)) =
      ∑ j, (∑ i, (mult i j : ℂ) * σ (Dimensions.groundUnitScalarEquiv C
        (p.rightTrace (𝟙 (Ground.simples C i))))) * (T a j).trace)
    (a : braidAlgebra X n) (ha : ∀ j, T a j ∈ Matrix.unitaryGroup (Fin (size j)) ℂ) :
    ‖σ (Dimensions.groundUnitScalarEquiv C
      (p.rightTrace (a : End (tensorPower X (n + 2))).asHom))‖ ≤
        Ground.fpDimension C X ^ (n + 2) := by
  have hbound (i : Fin (Ground.rank C)) : ‖σ (Dimensions.groundUnitScalarEquiv C
      (p.rightTrace (𝟙 (Ground.simples C i))))‖ ≤ Ground.fpSimple C i := by
    have h := Dimensions.galois_pivotalDimension_norm_le_fpSimple C p σ i
    simpa only [Dimensions.pivotalDimension, Dimensions.groundUnitScalarEquiv_apply] using h
  have hw (j : Fin r) :
      ‖∑ i, (mult i j : ℂ) * σ (Dimensions.groundUnitScalarEquiv C
        (p.rightTrace (𝟙 (Ground.simples C i))))‖ ≤
          ∑ i, (mult i j : ℝ) * Ground.fpSimple C i := by
    calc
      _ ≤ ∑ i, ‖(mult i j : ℂ) * σ (Dimensions.groundUnitScalarEquiv C
          (p.rightTrace (𝟙 (Ground.simples C i))))‖ := norm_sum_le _ _
      _ = ∑ i, (mult i j : ℝ) * ‖σ (Dimensions.groundUnitScalarEquiv C
          (p.rightTrace (𝟙 (Ground.simples C i))))‖ := by simp
      _ ≤ _ := Finset.sum_le_sum fun i _ =>
        mul_le_mul_of_nonneg_left (hbound i) (Nat.cast_nonneg _)
  have hmass : (∑ i, (Module.finrank ℂ (Ground.simples C i ⟶ tensorPower X (n + 2)) : ℝ) *
      Ground.fpSimple C i) = Ground.fpDimension C X ^ (n + 2) := by
    change Ground.fpDimension C (tensorPower X (n + 2)) = _
    exact fpDimension_tensorPower C X (n + 2)
  calc
    _ = ‖∑ j, (∑ i, (mult i j : ℂ) * σ (Dimensions.groundUnitScalarEquiv C
        (p.rightTrace (𝟙 (Ground.simples C i))))) * (T a j).trace‖ := by rw [htrace]
    _ ≤ ∑ j, ‖(∑ i, (mult i j : ℂ) * σ (Dimensions.groundUnitScalarEquiv C
        (p.rightTrace (𝟙 (Ground.simples C i))))) * (T a j).trace‖ := norm_sum_le _ _
    _ ≤ ∑ j, (∑ i, (mult i j : ℝ) * Ground.fpSimple C i) * (size j : ℝ) := by
      apply Finset.sum_le_sum
      intro j _
      rw [norm_mul]
      apply mul_le_mul (hw j)
        (by simpa using PropertyF.norm_trace_le_card (PropertyF.columnUnitary_of_unitary (ha j)))
        (norm_nonneg _)
      exact Finset.sum_nonneg fun i _ => mul_nonneg (Nat.cast_nonneg _) (Ground.fpSimple_pos C i).le
    _ = _ := (multiplicity_mass_eq _ size mult (Ground.fpSimple C) hdim).trans hmass

/-- Finite braid image constructs a semilinear unitary presentation satisfying
the ordinary bound for the Galois-transformed categorical trace. -/
theorem exists_galois_unitary_braid_trace_bound
    (C : Ground.BraidedFusionCategory.{v,u}) (X : C.Obj) (n : ℕ)
    (hfinite : Finite (braidImage X n)) (p : Dimensions.PivotalStructure (C := C.Obj))
    (σ : ℂ ≃+* ℂ) :
    ∃ (r : ℕ) (size : Fin r → ℕ)
      (T : braidAlgebra X n ≃+* ∀ j, Matrix (Fin (size j)) (Fin (size j)) ℂ),
      (∀ j, 0 < size j) ∧
      (∀ g j, T (groupInImage (braidEndRepresentation X n) g) j ∈
        Matrix.unitaryGroup (Fin (size j)) ℂ) ∧
      (∀ (z : ℂ) a, T (z • a) = σ z • T a) ∧
      (∀ a : braidAlgebra X n, (∀ j, T a j ∈ Matrix.unitaryGroup (Fin (size j)) ℂ) →
        ‖σ (Dimensions.groundUnitScalarEquiv C
          (p.rightTrace (a : End (tensorPower X (n + 2))).asHom))‖ ≤
            Ground.fpDimension C X ^ (n + 2)) := by
  obtain ⟨r, size, T, mult, hsize, _, hdim, hunit, hsmul, htrace⟩ :=
    exists_galois_unitary_braid_blocks C X n hfinite p σ
  exact ⟨r, size, T, hsize, hunit, hsmul,
    fun a ha => galois_unitary_braid_bound_of_weights C X n p σ r size T mult hdim htrace a ha⟩

/-- The same transported presentation has nonzero real trace weights and the
ordinary power bound whenever the simple Galois dimensions are real. -/
theorem exists_galois_real_braid_trace_bound
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
          (PropertyF.Blocks.mk r size).trace w (T a)) ∧
      (∀ a : braidAlgebra X n, (∀ i, T a i ∈ Matrix.unitaryGroup (Fin (size i)) ℂ) →
        ‖σ (Dimensions.groundUnitScalarEquiv C
          (p.rightTrace (a : End (tensorPower X (n + 2))).asHom))‖ ≤
            Ground.fpDimension C X ^ (n + 2)) := by
  classical
  obtain ⟨r, size, T, mult, hsize, hret, hmass, hunit, hsmul, htrace⟩ :=
    exists_galois_unitary_braid_blocks C X n hfinite p σ
  let w : Fin r → ℝ := fun j => ∑ i, (mult i j : ℝ) * conjugate i
  refine ⟨r, size, T, w, hsize, ?_, hunit, hsmul, ?_, ?_⟩
  · intro j
    have hn := transported_weight_ne_zero (fun i => mult i j) original σ hpos (hret j)
    simp only [hreal, ← Complex.ofReal_natCast, ← Complex.ofReal_mul,
      ← Complex.ofReal_sum] at hn
    exact_mod_cast hn
  · intro a
    rw [htrace]
    simp only [PropertyF.Blocks.trace, w, Complex.ofReal_sum, Complex.ofReal_mul,
      Complex.ofReal_natCast, hdim, hreal]
  · exact fun a ha =>
      galois_unitary_braid_bound_of_weights C X n p σ r size T mult hmass htrace a ha

end PropertyF.Ground.Calculus
