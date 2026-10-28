module
public import PropertyF.Ground.Centre.Calculus.TypeA
public import PropertyF.Ground.CentreCalculus.ProjectorReduction
public import Mathlib.GroupTheory.Perm.Fin
public import PropertyF.Ground.Dimensions.TensorMultiplicativity

/-!
# Permutation actions and traces

Self-transparent tensor powers carry permutation actions. We relate their
signed traces to one-strand deletion and insertion identities. The notation
`tr C p ρ n σ` is the scalar pivotal trace of the permutation action.
-/
@[expose] public noncomputable section
open PropertyF.Ground.Modular (HasFPSimpleDimensions)
open PropertyF.Ground.Centre (permutationSign)
open Equiv.Perm (decomposeFin)
open PropertyF.Ground.Dimensions
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.CentreCalculus
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]

/-- The actual self-transparent permutation action, including the trivial
zero- and one-strand cases, as endomorphisms. -/
def tensorPermAction (X : C)
    (hX : SelfTransparent X) :
    ∀ n : ℕ, Equiv.Perm (Fin n) →* End (tensorPower X n)
  | 0 => 1
  | 1 => 1
  | n + 2 => Aut.toEnd.comp (permutationAction X hX n)

/-- Every adjacent transposition acts by the actual categorical crossing. -/
theorem tensorPermAction_swap {X : C} (hX : SelfTransparent X) {n : ℕ} (i : Fin (n + 1)) :
    tensorPermAction X hX (n + 2) (adjacentSwap i) = Aut.toEnd (braidGenerator X n i) :=
  congrArg Aut.toEnd (permutationAction_swap hX i)

end PropertyF.Ground.CentreCalculus

open CategoryTheory CategoryTheory.MonoidalCategory
open scoped BigOperators
namespace PropertyF.Ground.CentreCalculus

/-- Signed permutation trace sum, with no categorical assumptions. -/
def signedTraceSum (F : ∀ n : ℕ, Equiv.Perm (Fin n) → ℂ) (n : ℕ) : ℂ :=
  ∑ σ, (permutationSign ℂ n σ : ℂ) * F n σ

/-- The sign changes precisely when the newly inserted point is moved. -/
theorem sign_decomposeFin {n : ℕ} (p : Fin (n + 1)) (σ : Equiv.Perm (Fin n)) :
    (permutationSign ℂ (n + 1) (decomposeFin.symm (p, σ)) : ℂ) =
      (if p = 0 then 1 else -1) * (permutationSign ℂ n σ : ℂ) := by
  by_cases hp : p = 0 <;>
    simp [permutationSign, decomposeFin.symm_sign, hp]

variable {F : ∀ n : ℕ, Equiv.Perm (Fin n) → ℂ} {d c : ℂ} {n : ℕ}

/-- A deletion identity for the trace gives the signed-sum recurrence. -/
theorem signedTraceSum_succ
    (hfixed : ∀ σ, F (n + 1) (decomposeFin.symm (0, σ)) = d * F n σ)
    (hmoved : ∀ (p : Fin (n + 1)), p ≠ 0 → ∀ σ, F (n + 1) (decomposeFin.symm (p, σ)) = c * F n σ) :
    signedTraceSum F (n + 1) = (d - (n : ℂ) * c) * signedTraceSum F n := by
  unfold signedTraceSum
  rw [← decomposeFin.symm.sum_comp,
    Fintype.sum_prod_type, Fin.sum_univ_succ]
  simp only [sign_decomposeFin, ite_true, one_mul, hfixed, Fin.succ_ne_zero,
    ite_false, hmoved _ (Fin.succ_ne_zero _), neg_mul, Finset.sum_neg_distrib,
    mul_left_comm, ← Finset.mul_sum,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

/-- Deleting the first adjacent crossing leaves the permutation trace unchanged. -/
abbrev HasAdjacentTrace (F : ∀ n : ℕ, Equiv.Perm (Fin n) → ℂ) : Prop :=
  ∀ n (σ : Equiv.Perm (Fin (n + 1))),
    F (n + 2) (decomposeFin.symm (1, σ)) = F (n + 1) σ

/-- Deleting a moved strand leaves the permutation trace unchanged. -/
abbrev HasMovedTrace (F : ∀ n : ℕ, Equiv.Perm (Fin n) → ℂ) : Prop :=
  ∀ n (p : Fin (n + 1)), p ≠ 0 → ∀ σ,
    F (n + 1) (decomposeFin.symm (p, σ)) = F n σ

/-- The trace contribution of deleting a fixed or a moved strand. -/
structure IsTraceDeletion (F : ∀ n : ℕ, Equiv.Perm (Fin n) → ℂ) (d : ℂ) : Prop where
  fixed : ∀ n σ, F (n + 1) (decomposeFin.symm (0, σ)) = d * F n σ
  moved : HasMovedTrace F

/-- The deletion identities imply the falling-factorial signed trace sum.
This isolates the categorical trace calculation from the permutation sum. -/
theorem signedTraceSum_falling
    (hzero : F 0 1 = 1) (h : IsTraceDeletion F d) :
    ∀ n, signedTraceSum F n = ∏ k ∈ Finset.range n, (d - (k : ℂ)) := by
  intro n
  induction n with
  | zero =>
    let : Unique (Equiv.Perm (Fin 0)) := ⟨⟨1⟩, fun _ => Subsingleton.elim _ _⟩
    simp [signedTraceSum, hzero, permutationSign]
  | succ n ih =>
    rw [signedTraceSum_succ (c := 1) (h.fixed n) (by simpa using h.moved n), ih,
      Finset.prod_range_succ]
    ring

universe v u
/-- Scalar pivotal trace of a permutation action on a tensor power. -/
abbrev permScalarTrace (C : BraidedFusionCategory.{v,u})
    (p : PivotalStructure (C := C.Obj)) {X : C.Obj}
    (ρ : ∀ n : ℕ, Equiv.Perm (Fin n) →* End (tensorPower X n))
    (n : ℕ) (σ : Equiv.Perm (Fin n)) : ℂ :=
  unitScalar C (p.rightTrace ((ρ n) σ).asHom)

local notation "tr" => permScalarTrace

/-- Integrality follows from one-strand trace deletion for any compatible
(possibly sign-twisted) family of actual actions. -/
theorem integral_of_trace_deletion {C : BraidedFusionCategory} {p : PivotalStructure (C := C.Obj)}
    (hdim : HasFPSimpleDimensions C p) {X : C.Obj}
    (ρ : ∀ n : ℕ, Equiv.Perm (Fin n) →* End (tensorPower X n))
    (h : IsTraceDeletion (tr C p ρ) (fpDimension C X : ℂ)) : IsFPIntegral C X := by
  let F := tr C p ρ
  have hz : F 0 1 = 1 := by
    change unitScalar C (p.rightTrace (((ρ 0) 1).asHom)) = 1
    rw [map_one]
    change unitScalar C (p.rightTrace (𝟙 (𝟙_ C.Obj))) = 1
    rw [Dimensions.rightTrace_unit, unitScalar_eq_equiv, map_one]
  apply integral_of_signed_permutation_traces hdim
  intro n
  exact ⟨ρ n, signedTraceSum_falling hz h n⟩

end PropertyF.Ground.CentreCalculus

open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.CentreCalculus
local notation "tr" => permScalarTrace
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]

/-- Extend a permutation by fixing the first strand. -/
def fixHead (n : ℕ) : Equiv.Perm (Fin n) →* Equiv.Perm (Fin (n + 1)) where
  toFun σ := decomposeFin.symm (0, σ)
  map_one' := by
    ext x
    refine Fin.cases ?_ (fun j => ?_) x <;> simp
  map_mul' σ τ := by
    ext x
    refine Fin.cases ?_ (fun j => ?_) x <;>
      simp [Equiv.Perm.mul_apply]

/-- A one-point permutation extension is the swap of that point with zero,
followed by the fixed-head extension of the smaller permutation. -/
theorem decomposeFin_eq_swap_fixHead {n : ℕ} (q : Fin (n + 1)) (σ : Equiv.Perm (Fin n)) :
    decomposeFin.symm (q, σ) = Equiv.swap 0 q * fixHead n σ := by
  ext x
  induction x using Fin.cases <;> simp [fixHead, Equiv.Perm.mul_apply]

theorem fixHead_swap {n : ℕ} (i : Fin n) :
    fixHead (n + 1) (adjacentSwap i) =
      adjacentSwap i.succ := by
  dsimp only [adjacentSwap]
  have h : i.succ.castSucc = i.castSucc.succ := Fin.ext rfl
  rw [h]
  ext x
  refine Fin.cases ?_ (fun j => ?_) x <;> simp [fixHead, Equiv.swap_apply_def, Fin.ext_iff]
  split_ifs <;> rfl

section
variable {X : C} (hX : SelfTransparent X)

set_option backward.isDefEq.respectTransparency false in
/-- Inserting a fixed first strand acts by tensoring the old automorphism
on the left with the identity of the new strand. -/
theorem permutationAction_fixHead {n : ℕ}
    (σ : Equiv.Perm (Fin (n + 2))) :
    permutationAction X hX (n + 1) (fixHead (n + 2) σ) =
      (tensorLeft X).mapAut (tensorPower X (n + 2)) (permutationAction X hX n σ) := by
  let f := (permutationAction X hX (n + 1)).comp (fixHead (n + 2))
  let g := ((tensorLeft X).mapAut (tensorPower X (n + 2))).comp (permutationAction X hX n)
  obtain ⟨w, rfl⟩ := strandPermutation_surjective n σ
  have hh : f.comp (strandPermutation n) = g.comp (strandPermutation n) := by
    refine FreeGroup.ext_hom _ _ fun i ↦ ?_
    change permutationAction X hX (n + 1) (fixHead (n + 2) (strandPermutation n (FreeGroup.of i))) =
      (tensorLeft X).mapAut (tensorPower X (n + 2))
        (permutationAction X hX n (strandPermutation n (FreeGroup.of i)))
    simp only [strandPermutation, FreeGroup.lift_apply_of, fixHead_swap, permutationAction_swap]
    exact (braidGenerator_succ X i).symm
  exact DFunLike.congr_fun hh w

/-- Inserting a fixed strand tensors the permutation action with its identity. -/
theorem tensorPermAction_fixHead :
    ∀ {n} (σ : Equiv.Perm (Fin n)),
      tensorPermAction X hX (n + 1) (fixHead n σ) =
        (tensorLeft X).mapEnd (tensorPower X n) (tensorPermAction X hX n σ) := by
  intro n σ
  rcases n with _ | _ | n
  · obtain rfl : σ = 1 := Subsingleton.elim _ _
    simp [tensorPermAction, Functor.mapEnd]
    rfl
  · obtain rfl : σ = 1 := Equiv.ext fun x ↦ (Fin.eq_zero (σ x)).trans (Fin.eq_zero x).symm
    simp [tensorPermAction, Functor.mapEnd]
    rfl
  · change Aut.toEnd (permutationAction X hX (n + 1) (fixHead (n + 2) σ)) = _
    rw [permutationAction_fixHead]
    rfl

set_option backward.isDefEq.respectTransparency false in
/-- An adjacent moved strand acts by the first crossing followed by fixed-head insertion. -/
theorem tensorPermAction_adjacent {n : ℕ} (σ : Equiv.Perm (Fin (n + 1))) :
    tensorPermAction X hX (n + 2) (decomposeFin.symm (1, σ)) =
      (Aut.toEnd (braidGenerator X n 0) : End (X ⊗ tensorPower X (n + 1))) *
        End.of (X ◁ ((tensorPermAction X hX (n + 1)) σ).asHom) := by
  rw [decomposeFin_eq_swap_fixHead, map_mul]
  change tensorPermAction X hX (n + 2)
    (adjacentSwap (0 : Fin (n + 1))) * _ = _
  rw [tensorPermAction_swap, tensorPermAction_fixHead]
  rfl

end

set_option backward.isDefEq.respectTransparency false in
/-- A fixed inserted strand contributes its positive categorical dimension to
 the actual permutation trace. -/
theorem tensorPermTrace_fixHead {D : BraidedFusionCategory} {p : PivotalStructure (C := D.Obj)}
    (hdim : HasFPSimpleDimensions D p) {X : D.Obj} (hX : SelfTransparent X)
    {n : ℕ} (σ : Equiv.Perm (Fin n)) : tr D p (tensorPermAction X hX) (n + 1) (fixHead n σ) =
      (fpDimension D X : ℂ) * tr D p (tensorPermAction X hX) n σ := by
  simp only [permScalarTrace]
  rw [tensorPermAction_fixHead]
  change unitScalar D (p.rightTrace (X ◁ ((tensorPermAction X hX n) σ).asHom)) = _
  simpa only [id_tensorHom, ← unitScalar_eq_equiv,
    ← pivotalDimension_eq_fpDimension hdim, pivotalDimension] using
    Dimensions.pivotalTrace_tensor p (unitScalarEquiv D)
      (𝟙 X) ((tensorPermAction X hX n) σ).asHom

end PropertyF.Ground.CentreCalculus
