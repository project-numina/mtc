module
public import PropertyF.Ground.Calculus.BraidWeights
public import PropertyF.Ground.Calculus.WeightFacts
public import PropertyF.UnitaryTrace
public import PropertyF.Ground.Fusion.ObjectDimension

/-! The ordinary weighted trace bound for actual braid algebras. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open scoped BigOperators
namespace PropertyF.Ground.Calculus
universe v u
attribute [local instance] Abelian.hasFiniteBiproducts

/-- In actual categorical braid blocks, the norm of the pivotal trace of a
unitary is bounded by the simple-multiplicity mass. The explicit dimension
bound is supplied by the fusion/Perron and dimensions workstreams. -/
theorem pivotalTrace_braid_unitary_bound
    (C : Ground.BraidedFusionCategory.{v,u}) (X : C.Obj) (n : ℕ)
    (p : Dimensions.PivotalStructure (C := C.Obj)) (scalar : End (𝟙_ C.Obj) ≃ₐ[ℂ] ℂ)
    (m : Fin (Ground.rank C) → ℕ)
    (e : tensorPower X (n + 2) ≅ ⨁ (fun q : Σ i, Fin (m i) => Ground.simples C q.1))
    (r : ℕ) (d : Fin r → ℕ) (hd : ∀ j, 0 < d j)
    (b : braidAlgebra X n ≃ₐ[ℂ] ∀ j, Matrix (Fin (d j)) (Fin (d j)) ℂ)
    (fp : Fin (Ground.rank C) → ℝ)
    (hbound : ∀ i, ‖scalar (p.rightTrace (𝟙 (Ground.simples C i)))‖ ≤ fp i)
    (a : braidAlgebra X n) (ha : ∀ j, b a j ∈ Matrix.unitaryGroup (Fin (d j)) ℂ) :
    ‖scalar (p.rightTrace (a : End (tensorPower X (n + 2))).asHom)‖ ≤
      ∑ i, (m i : ℝ) * fp i := by
  obtain ⟨mult, _, hdim, htrace⟩ := pivotalTrace_braid_multiplicities C X n p scalar m e r d hd b
  have hfp : ∀ i, 0 ≤ fp i := fun i => (norm_nonneg _).trans (hbound i)
  have hw (j : Fin r) :
      ‖∑ i, (mult i j : ℂ) * scalar (p.rightTrace (𝟙 (Ground.simples C i)))‖ ≤
        ∑ i, (mult i j : ℝ) * fp i := by
    calc
      _ ≤ ∑ i, ‖(mult i j : ℂ) * scalar (p.rightTrace (𝟙 (Ground.simples C i)))‖ := norm_sum_le _ _
      _ = ∑ i, (mult i j : ℝ) * ‖scalar (p.rightTrace (𝟙 (Ground.simples C i)))‖ := by simp
      _ ≤ _ := Finset.sum_le_sum fun i _ =>
        mul_le_mul_of_nonneg_left (hbound i) (Nat.cast_nonneg _)
  calc
    _ = ‖∑ j, (∑ i, (mult i j : ℂ) * scalar (p.rightTrace (𝟙 (Ground.simples C i)))) *
      (b a j).trace‖ := by rw [htrace]
    _ ≤ ∑ j, ‖(∑ i, (mult i j : ℂ) * scalar (p.rightTrace (𝟙 (Ground.simples C i)))) *
      (b a j).trace‖ := norm_sum_le _ _
    _ ≤ ∑ j, (∑ i, (mult i j : ℝ) * fp i) * (d j : ℝ) := by
      apply Finset.sum_le_sum
      intro j _
      rw [norm_mul]
      apply mul_le_mul (hw j)
        (by simpa using PropertyF.norm_trace_le_card (PropertyF.columnUnitary_of_unitary (ha j)))
        (norm_nonneg _)
      exact Finset.sum_nonneg fun i _ => mul_nonneg (Nat.cast_nonneg _) (hfp i)
    _ = ∑ i, (m i : ℝ) * fp i := multiplicity_mass_eq m d mult fp hdim

/-- The actual FP dimension of a tensor power is the corresponding power. -/
theorem fpDimension_tensorPower (C : Ground.BraidedFusionCategory.{v,u})
    (X : C.Obj) (n : ℕ) : Ground.fpDimension C (tensorPower X n) = Ground.fpDimension C X ^ n := by
  induction n with
  | zero => simp [tensorPower, Ground.fpDimension_unit]
  | succ n ih =>
    simp only [tensorPower, Ground.fpDimension_tensor, ih, pow_succ]
    ring

/-- Finite braid image constructs unitary blocks in which the ordinary
categorical trace bound is the n-strand FP-dimension power. -/
theorem exists_unitary_braid_trace_power_bound
    (C : Ground.BraidedFusionCategory.{v,u}) (X : C.Obj) (n : ℕ)
    (hfinite : Finite (braidImage X n))
    (p : Dimensions.PivotalStructure (C := C.Obj)) (scalar : End (𝟙_ C.Obj) ≃ₐ[ℂ] ℂ)
    (hbound : ∀ i, ‖scalar (p.rightTrace (𝟙 (Ground.simples C i)))‖ ≤ Ground.fpSimple C i) :
    ∃ (r : ℕ) (d : Fin r → ℕ)
      (b : braidAlgebra X n ≃ₐ[ℂ] ∀ j, Matrix (Fin (d j)) (Fin (d j)) ℂ),
      (∀ j, 0 < d j) ∧
      (∀ g j, b (groupInImage (braidEndRepresentation X n) g) j ∈
        Matrix.unitaryGroup (Fin (d j)) ℂ) ∧
      ∀ a : braidAlgebra X n, (∀ j, b a j ∈ Matrix.unitaryGroup (Fin (d j)) ℂ) →
        ‖scalar (p.rightTrace (a : End (tensorPower X (n + 2))).asHom)‖ ≤
          Ground.fpDimension C X ^ (n + 2) := by
  let m : Fin (Ground.rank C) → ℕ := fun i =>
    Module.finrank ℂ (Ground.simples C i ⟶ tensorPower X (n + 2))
  obtain ⟨e⟩ := Ground.exists_canonical_decomposition C (tensorPower X (n + 2))
  obtain ⟨r, d, b, hnonzero, hunitary⟩ := braidAlgebra_unitary_blocks X n hfinite
  have hd : ∀ j, 0 < d j := fun j => Nat.pos_of_ne_zero (hnonzero j).ne
  refine ⟨r, d, b, hd, hunitary, fun a ha => ?_⟩
  have h := pivotalTrace_braid_unitary_bound C X n p scalar m e r d hd b
    (Ground.fpSimple C) hbound a ha
  change ‖scalar (p.rightTrace (a : End (tensorPower X (n + 2))).asHom)‖ ≤
    Ground.fpDimension C (tensorPower X (n + 2)) at h
  simpa only [fpDimension_tensorPower] using h

end PropertyF.Ground.Calculus
