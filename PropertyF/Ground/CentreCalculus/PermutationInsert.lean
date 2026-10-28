module
public import PropertyF.Ground.Centre.Calculus.TypeA
public import PropertyF.Ground.CentreCalculus.ProjectorReduction
public import Mathlib.GroupTheory.Perm.Fin
public import PropertyF.Ground.Dimensions.TensorMultiplicativity

/-!
# Permutation actions and traces

Self-transparent tensor powers carry permutation actions. We relate their
signed traces to one-strand deletion and insertion identities.
-/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.CentreCalculus
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]

/-- The actual self-transparent permutation action, including the trivial
zero- and one-strand cases, as endomorphisms. -/
def tensorPermutationAction (X : C)
    (hX : SelfTransparent X) :
    ∀ n : ℕ, Equiv.Perm (Fin n) →* End (tensorPower X n)
  | 0 => 1
  | 1 => 1
  | n + 2 => Aut.toEnd.comp (permutationAction X hX n)

/-- Every adjacent transposition acts by the actual categorical crossing. -/
theorem tensorPermutationAction_swap {X : C}
    (hX : SelfTransparent X)
    {n : ℕ} (i : Fin (n + 1)) :
    tensorPermutationAction X hX (n + 2) (Equiv.swap i.castSucc i.succ) =
      Aut.toEnd (braidGenerator X n i) :=
  congrArg Aut.toEnd (permutationAction_swap hX i)

end PropertyF.Ground.CentreCalculus

open CategoryTheory CategoryTheory.MonoidalCategory
open scoped BigOperators
namespace PropertyF.Ground.CentreCalculus

/-- Signed permutation trace sum, with no categorical assumptions. -/
def signedTraceSum (F : ∀ n : ℕ, Equiv.Perm (Fin n) → ℂ) (n : ℕ) : ℂ :=
  ∑ σ, (Centre.permutationSign ℂ n σ : ℂ) * F n σ

/-- The sign changes precisely when the newly inserted point is moved. -/
theorem sign_decomposeFin {n : ℕ} (p : Fin (n + 1)) (σ : Equiv.Perm (Fin n)) :
    (Centre.permutationSign ℂ (n + 1) (Equiv.Perm.decomposeFin.symm (p, σ)) : ℂ) =
      (if p = 0 then 1 else -1) * (Centre.permutationSign ℂ n σ : ℂ) := by
  by_cases hp : p = 0 <;>
    simp [Centre.permutationSign, Equiv.Perm.decomposeFin.symm_sign, hp]

/-- A deletion identity for the trace gives the signed-sum recurrence. -/
theorem signedTraceSum_succ {F : ∀ n : ℕ, Equiv.Perm (Fin n) → ℂ}
    {d c : ℂ} {n : ℕ}
    (hfixed : ∀ σ, F (n + 1) (Equiv.Perm.decomposeFin.symm (0, σ)) = d * F n σ)
    (hmoved : ∀ (p : Fin (n + 1)), p ≠ 0 → ∀ σ,
      F (n + 1) (Equiv.Perm.decomposeFin.symm (p, σ)) = c * F n σ) :
    signedTraceSum F (n + 1) = (d - (n : ℂ) * c) * signedTraceSum F n := by
  unfold signedTraceSum
  rw [← Equiv.Perm.decomposeFin.symm.sum_comp,
    Fintype.sum_prod_type, Fin.sum_univ_succ]
  simp only [sign_decomposeFin, ite_true, one_mul, hfixed, Fin.succ_ne_zero,
    ite_false, hmoved _ (Fin.succ_ne_zero _), neg_mul]
  simp only [Finset.sum_neg_distrib]
  simp only [show ∀ (a b c : ℂ), a * (b * c) = b * (a * c) by intros; ring, ← Finset.mul_sum]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

/-- The deletion identities imply the falling-factorial signed trace sum.
This isolates the categorical trace calculation from the permutation sum. -/
theorem signedTraceSum_falling {F : ∀ n : ℕ, Equiv.Perm (Fin n) → ℂ} {d : ℂ}
    (hzero : F 0 1 = 1)
    (hfixed : ∀ n σ, F (n + 1) (Equiv.Perm.decomposeFin.symm (0, σ)) = d * F n σ)
    (hmoved : ∀ n (p : Fin (n + 1)), p ≠ 0 → ∀ σ,
      F (n + 1) (Equiv.Perm.decomposeFin.symm (p, σ)) = F n σ) :
    ∀ n, signedTraceSum F n = ∏ k ∈ Finset.range n, (d - (k : ℂ)) := by
  intro n
  induction n with
  | zero =>
    let : Unique (Equiv.Perm (Fin 0)) := ⟨⟨1⟩, fun _ => Subsingleton.elim _ _⟩
    simp [signedTraceSum, hzero, Centre.permutationSign]
  | succ n ih =>
    rw [signedTraceSum_succ (c := 1) (hfixed n) (by simpa using hmoved n), ih,
      Finset.prod_range_succ]
    ring

universe v u
/-- Integrality follows from one-strand trace deletion for any compatible
(possibly sign-twisted) family of actual actions. -/
theorem integral_of_trace_deletion (C : BraidedFusionCategory.{v,u})
    (p : Dimensions.PivotalStructure (C := C.Obj))
    (hdim : Modular.HasFPSimpleDimensions C p) (X : C.Obj)
    (ρ : ∀ n : ℕ, Equiv.Perm (Fin n) →* End (tensorPower X n))
    (hfixed : ∀ n σ,
      unitScalar C (p.rightTrace ((ρ (n + 1)) (Equiv.Perm.decomposeFin.symm (0, σ))).asHom) =
        (fpDimension C X : ℂ) * unitScalar C (p.rightTrace ((ρ n) σ).asHom))
    (hmoved : ∀ n (q : Fin (n + 1)), q ≠ 0 → ∀ σ,
      unitScalar C (p.rightTrace ((ρ (n + 1)) (Equiv.Perm.decomposeFin.symm (q, σ))).asHom) =
        unitScalar C (p.rightTrace ((ρ n) σ).asHom)) :
    ∃ m : ℕ, fpDimension C X = m := by
  let F : ∀ n : ℕ, Equiv.Perm (Fin n) → ℂ := fun n σ =>
    unitScalar C (p.rightTrace ((ρ n) σ).asHom)
  have hz : F 0 1 = 1 := by
    change unitScalar C (p.rightTrace (((ρ 0) 1).asHom)) = 1
    rw [map_one]
    change unitScalar C (p.rightTrace (𝟙 (𝟙_ C.Obj))) = 1
    rw [Dimensions.rightTrace_unit, unitScalar_eq_equiv, map_one]
  have hf := signedTraceSum_falling hz hfixed hmoved
  apply integral_of_signed_permutation_traces C p hdim X
  intro n
  exact ⟨ρ n, hf n⟩

end PropertyF.Ground.CentreCalculus

open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.CentreCalculus
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]

/-- Extend a permutation by fixing the first strand. -/
def fixHead (n : ℕ) : Equiv.Perm (Fin n) →* Equiv.Perm (Fin (n + 1)) where
  toFun σ := Equiv.Perm.decomposeFin.symm (0, σ)
  map_one' := by
    ext x
    refine Fin.cases ?_ (fun j => ?_) x <;> simp
  map_mul' σ τ := by
    ext x
    refine Fin.cases ?_ (fun j => ?_) x <;>
      simp [Equiv.Perm.mul_apply]

theorem fixHead_swap {n : ℕ} (i : Fin n) :
    fixHead (n + 1) (Equiv.swap i.castSucc i.succ) =
      Equiv.swap i.succ.castSucc i.succ.succ := by
  ext x
  refine Fin.cases ?_ (fun j => ?_) x
  · simp [fixHead, Equiv.swap_apply_def, Fin.ext_iff]
  ·
    have h : i.succ.castSucc = i.castSucc.succ := Fin.ext rfl
    rw [h]
    simp only [fixHead, MonoidHom.coe_mk, OneHom.coe_mk,
      Equiv.Perm.decomposeFin_symm_apply_succ, Equiv.swap_self, Equiv.refl_apply,
      Equiv.swap_apply_def, Fin.succ_inj]
    split_ifs <;> rfl

set_option backward.isDefEq.respectTransparency false in
/-- Inserting a fixed first strand acts by tensoring the old automorphism
on the left with the identity of the new strand. -/
theorem permutationAction_fixHead {X : C}
    (hX : SelfTransparent X) {n : ℕ}
    (σ : Equiv.Perm (Fin (n + 2))) :
    permutationAction X hX (n + 1) (fixHead (n + 2) σ) =
      (tensorLeft X).mapAut (tensorPower X (n + 2)) (permutationAction X hX n σ) := by
  let f := (permutationAction X hX (n + 1)).comp (fixHead (n + 2))
  let g := ((tensorLeft X).mapAut (tensorPower X (n + 2))).comp (permutationAction X hX n)
  have heq : f = g := by
    apply MonoidHom.ext
    intro σ
    obtain ⟨w, rfl⟩ := strandPermutation_surjective n σ
    have hh : f.comp (strandPermutation n) = g.comp (strandPermutation n) := by
      apply FreeGroup.ext_hom
      intro i
      change permutationAction X hX (n + 1) (fixHead (n + 2) (strandPermutation n (FreeGroup.of i))) =
        (tensorLeft X).mapAut (tensorPower X (n + 2))
          (permutationAction X hX n (strandPermutation n (FreeGroup.of i)))
      simp only [strandPermutation, FreeGroup.lift_apply_of, fixHead_swap, permutationAction_swap]
      exact (braidGenerator_succ X i).symm
    exact DFunLike.congr_fun hh w
  exact DFunLike.congr_fun heq σ

/-- Inserting a fixed strand tensors the permutation action with its identity. -/
theorem tensorPermutationAction_fixHead {X : C}
    (hX : SelfTransparent X) :
    ∀ {n} (σ : Equiv.Perm (Fin n)),
      tensorPermutationAction X hX (n + 1) (fixHead n σ) =
        (tensorLeft X).mapEnd (tensorPower X n) (tensorPermutationAction X hX n σ) := by
  intro n σ
  cases n with
  | zero =>
    have hσ : σ = 1 := Subsingleton.elim _ _
    subst σ
    simp [tensorPermutationAction, Functor.mapEnd]
    rfl
  | succ n =>
    cases n with
    | zero =>
      have hσ : σ = 1 := Equiv.ext fun x ↦ (Fin.eq_zero (σ x)).trans (Fin.eq_zero x).symm
      subst σ
      simp [tensorPermutationAction, Functor.mapEnd]
      rfl
    | succ n =>
      change Aut.toEnd (permutationAction X hX (n + 1) (fixHead (n + 2) σ)) = _
      rw [permutationAction_fixHead]
      rfl

set_option backward.isDefEq.respectTransparency false in
/-- A fixed inserted strand contributes its positive categorical dimension to
 the actual permutation trace. -/
theorem tensorPermutationTrace_fixHead (D : BraidedFusionCategory.{v,u})
    (p : Dimensions.PivotalStructure (C := D.Obj))
    (hdim : Modular.HasFPSimpleDimensions D p)
    (X : D.Obj) (hX : SelfTransparent X) :
    ∀ n (σ : Equiv.Perm (Fin n)),
      unitScalar D (p.rightTrace ((tensorPermutationAction X hX (n + 1))
        (fixHead n σ)).asHom) =
      (fpDimension D X : ℂ) * unitScalar D (p.rightTrace ((tensorPermutationAction X hX n) σ).asHom) := by
  intro n σ
  rw [tensorPermutationAction_fixHead]
  have ht := Dimensions.pivotalTrace_tensor p (unitScalarEquiv D) X (tensorPower X n)
    (𝟙 X) ((tensorPermutationAction X hX n) σ).asHom
  simp only [id_tensorHom, ← unitScalar_eq_equiv] at ht
  change unitScalar D (p.rightTrace (X ◁ ((tensorPermutationAction X hX n) σ).asHom)) = _
  rw [ht]
  change Dimensions.pivotalDimension D p X * _ = _
  rw [pivotalDimension_eq_fpDimension D p hdim]

end PropertyF.Ground.CentreCalculus
