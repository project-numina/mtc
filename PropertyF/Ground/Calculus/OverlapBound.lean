module
public import PropertyF.Ground.Calculus.BraidWeights
public import PropertyF.UnitaryTrace
public import PropertyF.Ground.Fusion.ObjectDimension
public import PropertyF.Ground.Dimensions.DimensionCharacter
public import PropertyF.Ground.Calculus.ThreeTrace
public import PropertyF.PowerBound

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

/-- The ordinary bound holds in any block presentation, not only a particular
presentation chosen by the finite-group unitarization theorem. -/
theorem braid_trace_unitary_bound_ground
    (C : Ground.BraidedFusionCategory.{v,u}) (X : C.Obj) (n : ℕ)
    (p : Dimensions.PivotalStructure (C := C.Obj)) (r : ℕ) (d : Fin r → ℕ)
    (hd : ∀ j, 0 < d j)
    (b : braidAlgebra X n ≃ₐ[ℂ] ∀ j, Matrix (Fin (d j)) (Fin (d j)) ℂ)
    (a : braidAlgebra X n) (ha : ∀ j, b a j ∈ Matrix.unitaryGroup (Fin (d j)) ℂ) :
    ‖Dimensions.groundUnitScalarEquiv C
      (p.rightTrace (a : End (tensorPower X (n + 2))).asHom)‖ ≤
        Ground.fpDimension C X ^ (n + 2) := by
  let m : Fin (Ground.rank C) → ℕ := fun i =>
    Module.finrank ℂ (Ground.simples C i ⟶ tensorPower X (n + 2))
  obtain ⟨e⟩ := Ground.exists_canonical_decomposition C (tensorPower X (n + 2))
  have hbound : ∀ i, ‖Dimensions.groundUnitScalarEquiv C
      (p.rightTrace (𝟙 (Ground.simples C i)))‖ ≤ Ground.fpSimple C i := by
    intro i
    have h := Dimensions.galois_pivotalDimension_norm_le_fpSimple C p (RingEquiv.refl ℂ) i
    simpa only [RingEquiv.refl_apply, Dimensions.pivotalDimension,
      Dimensions.groundUnitScalarEquiv_apply] using h
  have h := pivotalTrace_braid_unitary_bound C X n p (Dimensions.groundUnitScalarEquiv C)
    m e r d hd b (Ground.fpSimple C) hbound a ha
  change ‖Dimensions.groundUnitScalarEquiv C
    (p.rightTrace (a : End (tensorPower X (n + 2))).asHom)‖ ≤
      Ground.fpDimension C (tensorPower X (n + 2)) at h
  simpa only [fpDimension_tensorPower] using h

end PropertyF.Ground.Calculus

/-! Actual overlapping braid products, using the constructed strand maps. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.Calculus
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]

/-- The repository's strand index for `k+1` overlapping copies of an operator
on `t+2` strands. -/
def overlapIndex (t : ℕ) : ℕ → ℕ
  | 0 => t
  | k + 1 => overlapIndex t k + (t + 1)

theorem overlapIndex_formula (t k : ℕ) : overlapIndex t k = t + k * (t + 1) := by
  induction k with
  | zero => simp [overlapIndex]
  | succ k ih => simp [overlapIndex, ih, Nat.succ_mul, Nat.add_assoc]

/-- Extend the existing product by `t+1` identity strands on the right. -/
def overlapLeft (X : C) (t k : ℕ) :
    braidAlgebra X (overlapIndex t k) →ₐ[ℂ] braidAlgebra X (overlapIndex t (k + 1)) := by
  exact addRightBraidAlgebraIter X (overlapIndex t k) (t + 1)

/-- Place a fresh copy at the right, overlapping the old product in one strand. -/
def overlapRight (X : C) (t k : ℕ) :
    braidAlgebra X t →ₐ[ℂ] braidAlgebra X (overlapIndex t (k + 1)) := by
  rw [overlapIndex_formula]
  exact addLeftBraidAlgebraIter X t ((k + 1) * (t + 1))

/-- The actual product of `k+1` successive overlapping braid-algebra elements. -/
def overlapProduct (X : C) (t : ℕ) (u : braidAlgebra X t) :
    ∀ k : ℕ, braidAlgebra X (overlapIndex t k)
  | 0 => u
  | k + 1 => overlapLeft X t k (overlapProduct X t u k) * overlapRight X t k u

end PropertyF.Ground.Calculus

/-! Unitarity of the actual overlapping braid products. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.Calculus

/-- A star-algebra map between products of matrix algebras preserves
blockwise unitarity. -/
theorem starMap_preserves_block_unitary {r s : ℕ} {d : Fin r → ℕ} {q : Fin s → ℕ}
    (F : (∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ) →⋆ₐ[ℂ]
      (∀ i, Matrix (Fin (q i)) (Fin (q i)) ℂ))
    (u : ∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ)
    (hu : ∀ i, u i ∈ Matrix.unitaryGroup (Fin (d i)) ℂ) :
    ∀ j, F u j ∈ Matrix.unitaryGroup (Fin (q j)) ℂ := by
  have h : u * star u = 1 := by
    funext i
    exact Matrix.mem_unitaryGroup_iff.mp (hu i)
  intro j
  apply Matrix.mem_unitaryGroup_iff.mpr
  have hf := congrArg (fun x => x j) (congrArg F h)
  simpa only [map_mul, map_star, map_one, Pi.mul_apply, Pi.star_apply, Pi.one_apply] using hf

universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]

/-- Adding right identity strands preserves unitarity in any compatible
presentations of the actual braid-image algebras. -/
theorem addRight_braid_unitary (X : C) (n k : ℕ) {r s : ℕ}
    {d : Fin r → ℕ} {q : Fin s → ℕ}
    (e : braidAlgebra X n ≃ₐ[ℂ] ∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ)
    (f : braidAlgebra X (n + k) ≃ₐ[ℂ] ∀ i, Matrix (Fin (q i)) (Fin (q i)) ℂ)
    (he : IsUnitaryPresentation (braidEndRepresentation X n) e)
    (hf : IsUnitaryPresentation (braidEndRepresentation X (n + k)) f)
    (u : braidAlgebra X n) (hu : ∀ i, e u i ∈ Matrix.unitaryGroup (Fin (d i)) ℂ) :
    ∀ j, f (addRightBraidAlgebraIter X n k u) j ∈ Matrix.unitaryGroup (Fin (q j)) ℂ := by
  simpa [addRightBlocksIterStarMap, addRightBlocksIter] using
    starMap_preserves_block_unitary (addRightBlocksIterStarMap X n k e f he hf) (e u) hu

/-- Adding left identity strands preserves unitarity in any compatible
presentations of the actual braid-image algebras. -/
theorem addLeft_braid_unitary (X : C) (n k : ℕ) {r s : ℕ}
    {d : Fin r → ℕ} {q : Fin s → ℕ}
    (e : braidAlgebra X n ≃ₐ[ℂ] ∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ)
    (f : braidAlgebra X (n + k) ≃ₐ[ℂ] ∀ i, Matrix (Fin (q i)) (Fin (q i)) ℂ)
    (he : IsUnitaryPresentation (braidEndRepresentation X n) e)
    (hf : IsUnitaryPresentation (braidEndRepresentation X (n + k)) f)
    (u : braidAlgebra X n) (hu : ∀ i, e u i ∈ Matrix.unitaryGroup (Fin (d i)) ℂ) :
    ∀ j, f (addLeftBraidAlgebraIter X n k u) j ∈ Matrix.unitaryGroup (Fin (q j)) ℂ := by
  simpa [addLeftBlocksIterStarMap, addLeftBlocksIter] using
    starMap_preserves_block_unitary (addLeftBlocksIterStarMap X n k e f he hf) (e u) hu

/-- Successive actual overlapping products remain blockwise unitary. The
presentations may be chosen independently at every strand count. -/
theorem overlapProduct_unitary (X : C) (t : ℕ)
    (r : ℕ → ℕ) (d : ∀ n, Fin (r n) → ℕ)
    (e : ∀ n, braidAlgebra X n ≃ₐ[ℂ]
      ∀ i, Matrix (Fin (d n i)) (Fin (d n i)) ℂ)
    (he : ∀ n, IsUnitaryPresentation (braidEndRepresentation X n) (e n))
    (u : braidAlgebra X t) (hu : ∀ i, e t u i ∈ Matrix.unitaryGroup (Fin (d t i)) ℂ) :
    ∀ k i, e (overlapIndex t k) (overlapProduct X t u k) i ∈
      Matrix.unitaryGroup (Fin (d (overlapIndex t k) i)) ℂ := by
  intro k
  induction k with
  | zero => exact hu
  | succ k ih =>
    intro i
    rw [overlapProduct, map_mul, Pi.mul_apply]
    apply Submonoid.mul_mem
    · exact addRight_braid_unitary X (overlapIndex t k) (t + 1)
        (e _) (e _) (he _) (he _) _ ih i
    · have hr := addLeft_braid_unitary X t ((k + 1) * (t + 1))
        (e t) (e _) (he t) (he _) u hu
      have hcast : ∀ (a b : ℕ) (h : a = b)
          (f : braidAlgebra X t →ₐ[ℂ] braidAlgebra X b),
          (∀ j, e b (f u) j ∈ Matrix.unitaryGroup (Fin (d b j)) ℂ) →
          ∀ j, e a ((Eq.mpr (congrArg (fun n => braidAlgebra X t →ₐ[ℂ] braidAlgebra X n) h) f) u) j ∈
            Matrix.unitaryGroup (Fin (d a j)) ℂ := by
        intro a b h f hunit
        cases h
        exact hunit
      have hs : ∀ j, e (overlapIndex t (k + 1)) (overlapRight X t k u) j ∈
          Matrix.unitaryGroup (Fin (d (overlapIndex t (k + 1)) j)) ℂ := by
        exact hcast _ _ (overlapIndex_formula t (k + 1)) _ hr
      exact hs i

end PropertyF.Ground.Calculus

/-! Reduction of the sharp trace bound to the categorical overlap recurrence. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory

namespace PropertyF.Ground.Calculus
universe v u

/-- A scaled overlap recurrence and bounds at its strand counts imply the sharp norm bound. -/
theorem norm_bound_of_overlapIndex {δ z : ℂ} {f : ℝ} (hδ : δ ≠ 0) (hf : 0 < f)
    (t : ℕ) (a : ℕ → ℂ) (hbound : ∀ k, ‖a k‖ ≤ f ^ (overlapIndex t k + 2))
    (hrec : ∀ k, a k * δ ^ k = z ^ (k + 1)) : ‖z‖ ≤ ‖δ‖ * f ^ (t + 1) := by
  apply PropertyF.norm_bound_of_overlap (m := t + 2) hδ hf a ?_ hrec
  intro k
  have hexp : overlapIndex t k + 2 = (k + 1) * ((t + 2) - 1) + 1 := by
    rw [overlapIndex_formula]
    have h : (t + 2) - 1 = t + 1 := by omega
    rw [h]
    ring
  simpa only [hexp] using hbound k

/-- Pivotal trace of an element of an actual categorical braid algebra. -/
def actualBraidTrace (C : Ground.BraidedFusionCategory.{v,u}) (X : C.Obj)
    (p : Dimensions.PivotalStructure (C := C.Obj)) (n : ℕ) (a : braidAlgebra X n) : ℂ :=
  Dimensions.groundUnitScalarEquiv C
    (p.rightTrace (a : End (tensorPower X (n + 2))).asHom)

/-- Iterating a single overlap step gives the scaled power identity, without
dividing by the simple dimension. -/
theorem overlap_trace_power_of_step
    (C : Ground.BraidedFusionCategory.{v,u}) (X : C.Obj)
    (p : Dimensions.PivotalStructure (C := C.Obj)) (t : ℕ) (u : braidAlgebra X t)
    (hstep : ∀ k, actualBraidTrace C X p (overlapIndex t (k + 1))
        (overlapProduct X t u (k + 1)) *
        Dimensions.groundUnitScalarEquiv C (p.rightTrace (𝟙 X)) =
      actualBraidTrace C X p (overlapIndex t k) (overlapProduct X t u k) *
        actualBraidTrace C X p t u) :
    ∀ k, actualBraidTrace C X p (overlapIndex t k) (overlapProduct X t u k) *
      (Dimensions.groundUnitScalarEquiv C (p.rightTrace (𝟙 X))) ^ k =
        actualBraidTrace C X p t u ^ (k + 1) := by
  intro k
  induction k with
  | zero => simp [overlapIndex, overlapProduct]
  | succ k ih =>
    rw [pow_succ, pow_succ]
    linear_combination (hstep k) *
      (Dimensions.groundUnitScalarEquiv C (p.rightTrace (𝟙 X))) ^ k +
      ih * actualBraidTrace C X p t u

/-- The sharp bound works in any family of unitary braid-block presentations;
it does not depend on a particular choice made by finite-group averaging. -/
theorem sharp_trace_bound_for_presentations_of_overlap_identity
    (C : Ground.BraidedFusionCategory.{v,u}) (X : C.Obj) [Simple X]
    (p : Dimensions.PivotalStructure (C := C.Obj)) (t : ℕ)
    (r : ℕ → ℕ) (d : ∀ n, Fin (r n) → ℕ)
    (e : ∀ n, braidAlgebra X n ≃ₐ[ℂ]
      ∀ i, Matrix (Fin (d n i)) (Fin (d n i)) ℂ)
    (hd : ∀ n i, 0 < d n i)
    (he : ∀ n, IsUnitaryPresentation (braidEndRepresentation X n) (e n))
    (u : braidAlgebra X t)
    (hu : ∀ i, e t u i ∈ Matrix.unitaryGroup (Fin (d t i)) ℂ)
    (hrec : ∀ k, actualBraidTrace C X p (overlapIndex t k) (overlapProduct X t u k) *
      (Dimensions.groundUnitScalarEquiv C (p.rightTrace (𝟙 X))) ^ k =
        actualBraidTrace C X p t u ^ (k + 1)) :
    ‖actualBraidTrace C X p t u‖ ≤
      ‖Dimensions.groundUnitScalarEquiv C (p.rightTrace (𝟙 X))‖ *
        Ground.fpDimension C X ^ (t + 1) := by
  have hδ : Dimensions.groundUnitScalarEquiv C (p.rightTrace (𝟙 X)) ≠ 0 := by
    intro h
    apply Modular.pivotalTrace_simple_ne_zero C p X
    apply (Dimensions.groundUnitScalarEquiv C).injective
    simpa using h
  have hf : 0 < Ground.fpDimension C X :=
    lt_of_lt_of_le zero_lt_one (Ground.one_le_fpDimension C X (Simple.not_isZero X))
  apply norm_bound_of_overlapIndex hδ hf t
    (fun k => actualBraidTrace C X p (overlapIndex t k) (overlapProduct X t u k)) ?_ hrec
  intro k
  have hbound := braid_trace_unitary_bound_ground C X (overlapIndex t k) p
    (r _) (d _) (hd _) (e _) (overlapProduct X t u k) (overlapProduct_unitary X t r d e he u hu k)
  change ‖actualBraidTrace C X p (overlapIndex t k) (overlapProduct X t u k)‖ ≤ _ at hbound
  exact hbound

end PropertyF.Ground.Calculus
