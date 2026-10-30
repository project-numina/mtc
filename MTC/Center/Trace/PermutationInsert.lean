module
public import MTC.Center.BraidWords.TypeA
public import MTC.Center.Trace.ProjectorReduction
public import Mathlib.GroupTheory.Perm.Fin
public import MTC.CategoryTheory.Dimensions.TensorMultiplicativity

/-!
# Permutation actions and traces

Self-transparent tensor powers carry permutation actions. We relate their
signed traces to one-strand deletion and insertion identities. The notation
`tr C p ρ n σ` is the scalar pivotal trace of the permutation action, and
`sgn R n σ` is the permutation sign in the scalar ring.
-/
@[expose] public noncomputable section
open PropertyF.Ground.Modular (HasFPSimpleDimensions)
local notation "sgn" => PropertyF.Ground.Centre.permutationSign
open Equiv.Perm (decomposeFin)
open PropertyF.Ground.Dimensions
open Equiv (Perm)
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.CentreCalculus
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]

/-- The actual self-transparent permutation action, including the trivial
zero- and one-strand cases, as endomorphisms. -/
def tensorPermAction (X : C)
    (hX : SelfTransparent X) :
    ∀ n : ℕ, Perm (Fin n) →* End (tensorPower X n)
  | 0 => 1
  | 1 => 1
  | n + 2 => Aut.toEnd.comp (permAction X hX n)

end PropertyF.Ground.CentreCalculus

open CategoryTheory CategoryTheory.MonoidalCategory
open scoped BigOperators
namespace PropertyF.Ground.CentreCalculus

section
variable {R : Type*} [CommRing R]

/-- The sign changes precisely when the newly inserted point is moved. -/
theorem sign_decomposeFin {n : ℕ} (p : Fin (n + 1)) (σ : Perm (Fin n)) :
    (sgn R (n + 1) (decomposeFin.symm (p, σ)) : R) =
      (if p = 0 then 1 else -1) * (sgn R n σ : R) := by
  by_cases hp : p = 0 <;>
    simp [Centre.permutationSign, decomposeFin.symm_sign, hp]

variable {F : ∀ n : ℕ, Perm (Fin n) → R} {d : R} {n : ℕ}

/-- A deletion identity for the trace gives the signed-sum recurrence. -/
theorem signedTraceSum_succ
    (hfixed : ∀ σ, F (n + 1) (decomposeFin.symm (0, σ)) = d * F n σ)
    (hmoved : ∀ (p : Fin (n + 1)), p ≠ 0 → ∀ σ, F (n + 1) (decomposeFin.symm (p, σ)) = F n σ) :
    signedTraceSum (F (n + 1)) = (d - (n : R)) * signedTraceSum (F n) := by
  rw [signedTraceSum, ← decomposeFin.symm.sum_comp,
    Fintype.sum_prod_type, Fin.sum_univ_succ]
  simp only [signedTraceSum, sign_decomposeFin, ite_true, one_mul, hfixed, Fin.succ_ne_zero,
    ite_false, hmoved _ (Fin.succ_ne_zero _), neg_mul, Finset.sum_neg_distrib,
    mul_left_comm, ← Finset.mul_sum,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

/-- Deleting the first adjacent crossing leaves the permutation trace unchanged. -/
abbrev HasAdjacentTrace (F : ∀ n : ℕ, Perm (Fin n) → R) : Prop :=
  ∀ n (σ : Perm (Fin (n + 1))),
    F (n + 2) (decomposeFin.symm (1, σ)) = F (n + 1) σ

/-- Deleting a moved strand leaves the permutation trace unchanged. -/
abbrev HasMovedTrace (F : ∀ n : ℕ, Perm (Fin n) → R) : Prop :=
  ∀ n (p : Fin (n + 1)), p ≠ 0 → ∀ σ,
    F (n + 1) (decomposeFin.symm (p, σ)) = F n σ

/-- The trace contribution of deleting a fixed or a moved strand. -/
structure IsTraceDeletion (F : ∀ n : ℕ, Perm (Fin n) → R) (d : R) : Prop where
  fixed : ∀ n σ, F (n + 1) (decomposeFin.symm (0, σ)) = d * F n σ
  moved : HasMovedTrace F

/-- The deletion identities imply the falling-factorial signed trace sum.
This isolates the categorical trace calculation from the permutation sum. -/
theorem signedTraceSum_falling
    (hzero : F 0 1 = 1) (h : IsTraceDeletion F d) (n : ℕ) :
    signedTraceSum (F n) = ∏ k ∈ Finset.range n, (d - (k : R)) := by
  induction n with
  | zero =>
    simp [signedTraceSum, hzero, Centre.permutationSign]
  | succ n ih =>
    simpa [ih, Finset.prod_range_succ, mul_comm] using
      signedTraceSum_succ (h.fixed n) (h.moved n)

end

universe v u
/-- Evaluate the pivotal trace of a permutation action in any codomain. -/
abbrev scalarPermTrace {D : Type u} [Category.{v} D] [MonoidalCategory D] [RightRigidCategory D]
    {R : Type*} (p : PivotalStructure (C := D)) (scalar : End (𝟙_ D) → R) {X : D}
    (ρ : ∀ n : ℕ, Perm (Fin n) →* End (tensorPower X n))
    (n : ℕ) (σ : Perm (Fin n)) : R :=
  scalar (p.rightTrace ((ρ n) σ).asHom)

/-- The scalar pivotal trace of a permutation action in a fusion category. -/
abbrev permScalarTrace (C : BraidedFusionCategory.{v,u})
    (p : PivotalStructure (C := C.Obj)) {X : C.Obj}
    (ρ : ∀ n : ℕ, Perm (Fin n) →* End (tensorPower X n)) :=
  scalarPermTrace p (unitScalarEquiv C).toLinearMap ρ

local notation "tr" => permScalarTrace

/-- Integrality follows from one-strand trace deletion for any compatible
(possibly sign-twisted) family of actual actions. -/
theorem integral_of_trace_deletion {C : BraidedFusionCategory} {p : PivotalStructure (C := C.Obj)}
    (hdim : HasFPSimpleDimensions C p) {X : C.Obj}
    (ρ : ∀ n : ℕ, Perm (Fin n) →* End (tensorPower X n))
    (h : IsTraceDeletion (tr C p ρ) (fpDimension C X : ℂ)) : IsFPIntegral C X :=
  let hz : tr C p ρ 0 1 = 1 := by
    change unitScalarEquiv C (p.rightTrace (((ρ 0) 1).asHom)) = 1
    rw [map_one]
    simpa only [End.one_asHom, tensorPower, Dimensions.rightTrace_unit] using (map_one (unitScalarEquiv C))
  integral_of_signed_permutation_traces hdim fun n ↦ ⟨ρ n, by
    simpa [permScalarTrace, scalarPermTrace, signedTraceSum, ← unitScalar_eq_equiv] using
      signedTraceSum_falling hz h n⟩

end PropertyF.Ground.CentreCalculus

open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.CentreCalculus
local notation "tr" => permScalarTrace
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]

/-- Extend a permutation by fixing the first strand. -/
def fixHead (n : ℕ) : Perm (Fin n) →* Perm (Fin (n + 1)) where
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
theorem decomposeFin_eq_swap_fixHead {n : ℕ} (q : Fin (n + 1)) (σ : Perm (Fin n)) :
    decomposeFin.symm (q, σ) = Equiv.swap 0 q * fixHead n σ := by
  ext x
  induction x using Fin.cases <;> simp [fixHead, Equiv.Perm.mul_apply]

/-- Inserting a fixed first strand shifts each adjacent swap by one position. -/
theorem fixHead_swap {n : ℕ} (i : Fin n) :
    fixHead (n + 1) (adjacentSwap i) =
      adjacentSwap i.succ :=
  Equiv.ext <| Fin.cases (by simp [fixHead, adjacentSwap, Equiv.swap_apply_def, Fin.ext_iff]) fun j ↦ by
    simpa [fixHead, adjacentSwap] using (Fin.succ_injective _).map_swap i.castSucc i.succ j

section
variable {X : C} (hX : SelfTransparent X) {n : ℕ}

/-- Every adjacent transposition acts by the actual categorical crossing. -/
theorem tensorPermAction_swap (i : Fin (n + 1)) :
    tensorPermAction X hX (n + 2) (adjacentSwap i) = Aut.toEnd (braidGenerator X n i) :=
  congrArg Aut.toEnd (permAction_swap hX i)

set_option backward.isDefEq.respectTransparency false in
/-- Inserting a fixed first strand acts by tensoring the old automorphism
on the left with the identity of the new strand. -/
theorem permAction_fixHead
    (σ : Perm (Fin (n + 2))) :
    permAction X hX (n + 1) (fixHead (n + 2) σ) =
      (tensorLeft X).mapAut (tensorPower X (n + 2)) (permAction X hX n σ) := by
  let f := (permAction X hX (n + 1)).comp (fixHead (n + 2))
  let g := ((tensorLeft X).mapAut (tensorPower X (n + 2))).comp (permAction X hX n)
  have hh : f.comp (strandPermutation n) = g.comp (strandPermutation n) :=
    FreeGroup.ext_hom _ _ fun i ↦ by
      change permAction X hX (n + 1) (fixHead (n + 2) (strandPermutation n (FreeGroup.of i))) =
        (tensorLeft X).mapAut (tensorPower X (n + 2))
          (permAction X hX n (strandPermutation n (FreeGroup.of i)))
      simpa only [strandPermutation, FreeGroup.lift_apply_of, fixHead_swap, permAction_swap] using
        (braidGenerator_succ X i).symm

  exact DFunLike.congr_fun ((MonoidHom.cancel_right (strandPermutation_surjective n)).mp hh) σ

/-- Inserting a fixed strand tensors the permutation action with its identity. -/
theorem tensorPermAction_fixHead :
    ∀ {n} (σ : Perm (Fin n)),
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
  · exact congrArg Aut.toEnd (permAction_fixHead hX σ)

set_option backward.isDefEq.respectTransparency false in
/-- An adjacent moved strand acts by the first crossing followed by fixed-head insertion. -/
theorem tensorPermAction_adjacent (σ : Perm (Fin (n + 1))) :
    tensorPermAction X hX (n + 2) (decomposeFin.symm (1, σ)) =
      (Aut.toEnd (braidGenerator X n 0) : End (X ⊗ tensorPower X (n + 1))) *
        End.of (X ◁ ((tensorPermAction X hX (n + 1)) σ).asHom) := by
  rw [decomposeFin_eq_swap_fixHead, map_mul]
  change tensorPermAction X hX (n + 2) (adjacentSwap (0 : Fin (n + 1))) * _ = _
  exact congrArg₂ (· * ·) (tensorPermAction_swap hX 0) (tensorPermAction_fixHead hX σ)

end

section
variable {D : Type u} [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]
  [RightRigidCategory D] [Preadditive D] [Linear ℂ D] [MonoidalPreadditive D] [MonoidalLinear ℂ D]
variable (p : PivotalStructure (C := D)) (scalar : End (𝟙_ D) ≃ₐ[ℂ] ℂ)
  {X : D} (hX : SelfTransparent X) {n : ℕ}

set_option backward.isDefEq.respectTransparency false in
/-- A fixed inserted strand contributes its pivotal dimension to the scalar trace. -/
theorem tensorPermTrace_fixHead (σ : Perm (Fin n)) :
    scalarPermTrace p scalar (tensorPermAction X hX) (n + 1) (fixHead n σ) =
      scalar (p.rightTrace (𝟙 X)) * scalarPermTrace p scalar (tensorPermAction X hX) n σ :=
  (congrArg (fun a : End (tensorPower X (n + 1)) ↦ scalar (p.rightTrace a.asHom))
    (tensorPermAction_fixHead hX σ)).trans <| by
      change scalar (p.rightTrace (X ◁ ((tensorPermAction X hX n) σ).asHom)) = _
      simpa only [id_tensorHom] using Dimensions.pivotalTrace_tensor p scalar
        (𝟙 X) ((tensorPermAction X hX n) σ).asHom

end

end PropertyF.Ground.CentreCalculus
