module
public import PropertyF.Ground.Calculus.BraidWeights
public import PropertyF.BlockTrace
public import PropertyF.Ground.Fusion.ObjectDimension
public import PropertyF.Ground.Dimensions.DimensionCharacter
public import PropertyF.Ground.Calculus.ThreeTrace
public import PropertyF.PowerBound

/-!
# Trace bounds from overlapping braids

The categorical braid trace obeys a weighted unitary bound. Repeated overlapping
products remain unitary, and their trace recurrence yields the sharper bound.
-/

open PropertyF.Ground.Dimensions

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open scoped BigOperators
namespace PropertyF.Ground.Calculus
universe v u
attribute [local instance] Abelian.hasFiniteBiproducts
variable (C : BraidedFusionCategory.{v,u}) (p : PivotalStructure (C := C.Obj))

/-- Pivotal trace of an element of an actual categorical braid algebra. -/
def actualBraidTrace {X : C.Obj} {n : ℕ} (a : braidAlgebra X n) : ℂ :=
  Ground.unitScalarEquiv C
    (p.rightTrace (a : End (tensorPower X (n + 2))).asHom)

/-- A block presentation realizes the categorical braid trace with the given weights. -/
abbrev IsTracePresentation {X : C.Obj}
    {n r : ℕ} {d : Fin r → ℕ}
    (b : braidAlgebra X n ≃ₐ[ℂ] Blocks.Algebra ⟨_, d⟩) (w : Fin r → ℝ) : Prop :=
  ∀ z : braidAlgebra X n, actualBraidTrace C p z = (Blocks.mk r d).trace w (b z)

/-- A uniform bound for the trace of unitary elements in a block presentation. -/
abbrev HasUnitaryTraceBound {X : C.Obj}
    {n r : ℕ} {d : Fin r → ℕ}
    (b : braidAlgebra X n ≃ₐ[ℂ] Blocks.Algebra ⟨_, d⟩) (R : ℝ) : Prop :=
  ∀ a, Blocks.IsUnitary ⟨_, d⟩ (b a) → ‖actualBraidTrace C p a‖ ≤ R

/-- The actual FP dimension of a tensor power is the corresponding power. -/
theorem fpDimension_tensorPower (X : C.Obj) :
    ∀ n, Ground.fpDimension C (tensorPower X n) = Ground.fpDimension C X ^ n
  | 0 => Ground.fpDimension_unit C
  | n + 1 => by simp [tensorPower, Ground.fpDimension_tensor, fpDimension_tensorPower X n,
      pow_succ, mul_comm]

section BraidTraceBound

variable {X : C.Obj} {n r : ℕ} {d : Fin r → ℕ} (hd : ∀ j, 0 < d j)
  (b : braidAlgebra X n ≃ₐ[ℂ] Blocks.Algebra ⟨_, d⟩)
include hd

/-- In actual categorical braid blocks, the norm of the pivotal trace of a
unitary is bounded by the simple-multiplicity mass. The explicit dimension
bound is supplied by the fusion/Perron and dimensions workstreams. -/
theorem pivotalTrace_braid_unitary_bound
    (scalar : End (𝟙_ C.Obj) ≃ₐ[ℂ] ℂ)
    {m : Fin (Ground.rank C) → ℕ}
    (e : tensorPower X (n + 2) ≅ ⨁ (simpleCopies C m))
    {fp : Fin (Ground.rank C) → ℝ}
    (hbound : ∀ i, ‖scalar (p.rightTrace (𝟙 (Ground.simples C i)))‖ ≤ fp i)
    (a : braidAlgebra X n) (ha : Blocks.IsUnitary ⟨_, d⟩ (b a)) :
    ‖scalar (p.rightTrace (a : End (tensorPower X (n + 2))).asHom)‖ ≤
      ∑ i, (m i : ℝ) * fp i := by
  obtain ⟨mult, _, hdim, htrace⟩ := pivotalTrace_braid_multiplicities C p scalar e hd b
  rw [htrace a, ← multiplicity_mass_eq m d mult fp hdim]
  refine (norm_sum_le _ _).trans ?_
  apply Finset.sum_le_sum
  intro j _
  rw [norm_mul]
  apply mul_le_mul ?_ (by simpa using norm_trace_le_card (ha j)) (norm_nonneg _)
  · exact Finset.sum_nonneg fun i _ =>
      mul_nonneg (Nat.cast_nonneg _) ((norm_nonneg _).trans (hbound i))
  · exact (norm_sum_le _ _).trans <| Finset.sum_le_sum fun i _ => by
      simpa using mul_le_mul_of_nonneg_left (hbound i) (Nat.cast_nonneg (mult i j))

/-- The ordinary bound holds in any block presentation, not only a particular
presentation chosen by the finite-group unitarization theorem. -/
theorem braid_trace_unitary_bound_ground :
    HasUnitaryTraceBound C p b (Ground.fpDimension C X ^ (n + 2)) := by
  intro a ha
  let m : Fin (Ground.rank C) → ℕ := fun i =>
    Module.finrank ℂ (Ground.simples C i ⟶ tensorPower X (n + 2))
  obtain ⟨e⟩ := Ground.exists_canonical_decomposition C (tensorPower X (n + 2))
  rw [← fpDimension_tensorPower]
  change ‖Ground.unitScalarEquiv C
    (p.rightTrace (a : End (tensorPower X (n + 2))).asHom)‖ ≤
      Ground.fpDimension C (tensorPower X (n + 2))
  exact pivotalTrace_braid_unitary_bound C p hd b (Ground.unitScalarEquiv C) e (fun i => by
    simpa only [RingEquiv.refl_apply, Dimensions.pivotalDimension, unitScalar_eq_equiv] using
      Dimensions.galois_pivotalDimension_norm_le_fpSimple C p (RingEquiv.refl ℂ) i) a ha

end BraidTraceBound

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

/-- The number of strands added by repeated overlaps grows linearly. -/
theorem overlapIndex_formula (t : ℕ) : ∀ k, overlapIndex t k = t + k * (t + 1)
  | 0 => by rw [overlapIndex, Nat.zero_mul, Nat.add_zero]
  | k + 1 => by simp [overlapIndex, overlapIndex_formula t k, Nat.succ_mul, Nat.add_assoc]

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
def overlapProduct {X : C} {t : ℕ} (u : braidAlgebra X t) :
    ∀ k : ℕ, braidAlgebra X (overlapIndex t k)
  | 0 => u
  | k + 1 => overlapLeft X t k (overlapProduct u k) * overlapRight X t k u

end PropertyF.Ground.Calculus

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.Calculus
universe v u

/-- The scaled trace of overlapping products is the corresponding trace power. -/
abbrev HasOverlapTracePower (C : BraidedFusionCategory.{v,u}) {X : C.Obj}
    (p : PivotalStructure (C := C.Obj)) {t : ℕ} (u : braidAlgebra X t) : Prop :=
  ∀ k, actualBraidTrace C p (overlapProduct u k) *
    (pivotalDimension C p X) ^ k = actualBraidTrace C p u ^ (k + 1)

end PropertyF.Ground.Calculus

/-! Unitarity of the actual overlapping braid products. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.Calculus

/-- A star-algebra map between products of matrix algebras preserves
blockwise unitarity. -/
theorem starMap_preserves_block_unitary {r s : ℕ} {d : Fin r → ℕ} {q : Fin s → ℕ}
    (F : (Blocks.Algebra ⟨_, d⟩) →⋆ₐ[ℂ]
      (Blocks.Algebra ⟨_, q⟩))
    {u : Blocks.Algebra ⟨_, d⟩}
    (hu : Blocks.IsUnitary ⟨_, d⟩ u) :
    Blocks.IsUnitary ⟨_, q⟩ (F u) :=
  Pi.mem_unitary_iff.mp (Unitary.map_mem F (Pi.mem_unitary_iff.mpr hu))

universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]

/-- Successive actual overlapping products remain blockwise unitary. The
presentations may be chosen independently at every strand count. -/
theorem overlapProduct_unitary {X : C} {t : ℕ}
    {r : ℕ → ℕ} {d : ∀ n, Fin (r n) → ℕ}
    (e : ∀ n, braidAlgebra X n ≃ₐ[ℂ]
      Blocks.Algebra ⟨_, d n⟩)
    (he : ∀ n, IsUnitaryBraidPresentation (e n))
    {u : braidAlgebra X t} (hu : Blocks.IsUnitary ⟨_, d t⟩ (e t u)) :
    ∀ k, Blocks.IsUnitary ⟨_, d (overlapIndex t k)⟩
      (e (overlapIndex t k) (overlapProduct u k)) := by
  intro k
  induction k with
  | zero => exact hu
  | succ k ih =>
    intro i
    rw [overlapProduct, map_mul, Pi.mul_apply]
    apply Submonoid.mul_mem
    · change e (overlapIndex t k + (t + 1))
        (addRightBraidAlgebraIter X (overlapIndex t k) (t + 1) (overlapProduct u k)) i ∈
          Matrix.unitaryGroup (Fin (d (overlapIndex t k + (t + 1)) i)) ℂ
      simpa [addRightBlocksIterStarMap] using
        (starMap_preserves_block_unitary
          (addRightBlocksIterStarMap X (overlapIndex t k) (t + 1) (e _) (e _) (he _) (he _)) ih) i
    · have hcast : ∀ (a b : ℕ) (h : a = b)
          (f : braidAlgebra X t →ₐ[ℂ] braidAlgebra X b),
          Blocks.IsUnitary ⟨_, d b⟩ (e b (f u)) →
          Blocks.IsUnitary ⟨_, d a⟩
            (e a ((Eq.mpr (congrArg (fun n => braidAlgebra X t →ₐ[ℂ] braidAlgebra X n) h) f) u)) := by
        intro a b h f hunit
        cases h
        exact hunit
      exact hcast _ _ (overlapIndex_formula t (k + 1)) _ (by
        simpa [addLeftBlocksIterStarMap] using
          starMap_preserves_block_unitary
            (addLeftBlocksIterStarMap X t ((k + 1) * (t + 1)) (e t) (e _) (he t) (he _)) hu) i

end PropertyF.Ground.Calculus

/-! Reduction of the sharp trace bound to the categorical overlap recurrence. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory

namespace PropertyF.Ground.Calculus
universe v u
variable (C : BraidedFusionCategory.{v,u})

/-- A scaled overlap recurrence and bounds at its strand counts imply the sharp norm bound. -/
theorem norm_bound_of_overlapIndex {δ z : ℂ} {f : ℝ} (hδ : δ ≠ 0) (hf : 0 < f)
    (t : ℕ) (a : ℕ → ℂ) (hbound : ∀ k, ‖a k‖ ≤ f ^ (overlapIndex t k + 2))
    (hrec : ∀ k, a k * δ ^ k = z ^ (k + 1)) : ‖z‖ ≤ ‖δ‖ * f ^ (t + 1) := by
  apply norm_bound_of_overlap (m := t + 2) hδ hf a ?_ hrec
  intro k
  have hexp : overlapIndex t k + 2 = (k + 1) * ((t + 2) - 1) + 1 := by
    rw [overlapIndex_formula, show (t + 2) - 1 = t + 1 by omega]
    ring
  simpa only [hexp] using hbound k

variable (p : PivotalStructure (C := C.Obj)) {X : C.Obj} {t : ℕ} (u : braidAlgebra X t)

/-- Iterating a single overlap step gives the scaled power identity, without
dividing by the simple dimension. -/
theorem overlap_trace_power_of_step
    (hstep : ∀ k, actualBraidTrace C p
        (overlapProduct u (k + 1)) *
        pivotalDimension C p X =
      actualBraidTrace C p (overlapProduct u k) *
        actualBraidTrace C p u) :
    HasOverlapTracePower C p u := by
  intro k
  induction k with
  | zero => simp [overlapIndex, overlapProduct]
  | succ k ih =>
    rw [pow_succ, pow_succ]
    linear_combination (hstep k) *
      (pivotalDimension C p X) ^ k +
      ih * actualBraidTrace C p u

/-- The sharp bound works in any family of unitary braid-block presentations;
it does not depend on a particular choice made by finite-group averaging. -/
theorem sharp_trace_bound_for_presentations_of_overlap_identity
    [Simple X] {r : ℕ → ℕ} {d : ∀ n, Fin (r n) → ℕ}
    (e : ∀ n, braidAlgebra X n ≃ₐ[ℂ]
      Blocks.Algebra ⟨_, d n⟩)
    (hd : ∀ n i, 0 < d n i)
    (he : ∀ n, IsUnitaryBraidPresentation (e n))
    (hu : Blocks.IsUnitary ⟨_, d t⟩ (e t u))
    (hrec : HasOverlapTracePower C p u) :
    ‖actualBraidTrace C p u‖ ≤
      ‖pivotalDimension C p X‖ *
        Ground.fpDimension C X ^ (t + 1) := by
  simp only [HasOverlapTracePower, pivotalDimension, unitScalar_eq_equiv] at hrec ⊢
  apply norm_bound_of_overlapIndex (Modular.unitScalar_rightTrace_ne_zero C p X)
    (lt_of_lt_of_le zero_lt_one (Ground.one_le_fpDimension C (Simple.not_isZero X))) t
    (fun k => actualBraidTrace C p (overlapProduct u k)) ?_ hrec
  intro k
  have hbound := braid_trace_unitary_bound_ground C p
    (hd _) (e _) (overlapProduct u k) (overlapProduct_unitary e he hu k)
  change ‖actualBraidTrace C p (overlapProduct u k)‖ ≤ _ at hbound
  exact hbound

end PropertyF.Ground.Calculus
