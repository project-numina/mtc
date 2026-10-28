module
public import PropertyF.Ground.CentreCalculus.ProjectorReduction
public import PropertyF.Ground.CentreCalculus.PermutationInsert

/-!
# Parity-corrected permutation traces

Twisting by permutation sign relates signed and unsigned trace criteria.
The fixed-head and adjacent-crossing identities reduce integrality to a
one-strand deletion formula for either parity choice. We write `tr C p ρ n σ`
for the scalar pivotal trace of the permutation action and `sgn ℂ n σ`
for the permutation sign.
-/
@[expose] public noncomputable section
local notation "tr" => PropertyF.Ground.CentreCalculus.permScalarTrace
open PropertyF.Ground.Modular (HasFPSimpleDimensions)
local notation "sgn" => PropertyF.Ground.Centre.permutationSign
open Equiv.Perm (decomposeFin)
open PropertyF.Ground.Dimensions
open Equiv (Perm)
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.CentreCalculus
open CategoryTheory CategoryTheory.MonoidalCategory

/-- A moved-point extension is conjugate to the first adjacent extension. -/
theorem decomposeFin_succ_conj {n : ℕ} (j : Fin (n + 1)) (σ : Perm (Fin (n + 1))) :
    let τ := Equiv.swap 0 j
    let T := fixHead (n + 1) τ
    decomposeFin.symm (j.succ, σ) = T * decomposeFin.symm (1, τ⁻¹ * σ * τ) * T⁻¹ := by
  let τ : Perm (Fin (n + 1)) := Equiv.swap 0 j
  let T := fixHead (n + 1) τ
  change decomposeFin.symm (j.succ, σ) = T * decomposeFin.symm (1, τ⁻¹ * σ * τ) * T⁻¹
  have hswap : Equiv.swap 0 j.succ = T * Equiv.swap 0 1 * T⁻¹ := by
    simpa [T, τ, fixHead] using Equiv.swap_apply_apply T (0 : Fin (n + 2)) 1
  rw [decomposeFin_eq_swap_fixHead, decomposeFin_eq_swap_fixHead, hswap]
  simp [T, mul_assoc]

/-- Traces of permutation representations are invariant under conjugation. -/
theorem permutationTrace_conj {C : Type u} [Category.{v} C] [MonoidalCategory C]
    [RightRigidCategory C] (p : PivotalStructure (C := C)) {X : C}
    {G : Type*} [Group G] (ρ : G →* End X) (g h : G) :
    p.rightTrace (ρ (g * h * g⁻¹)).asHom = p.rightTrace (ρ h).asHom := by
  simpa only [← End.mul_asHom, ← map_mul, mul_assoc, inv_mul_cancel_left] using
    (p.rightTrace_cyclic (ρ (g * h)).asHom (ρ g⁻¹).asHom).symm

/-- It is enough to establish the moved-strand deletion identity for the
first adjacent swap: all other positions follow by conjugating the remaining
strands. -/
theorem movedTrace_of_adjacent {D : Type u} [Category.{v} D] [MonoidalCategory D]
    [RightRigidCategory D] {p : PivotalStructure (C := D)} {X : D} {R : Type*}
    (scalar : End (𝟙_ D) → R) (ρ : ∀ n : ℕ, Perm (Fin n) →* End (tensorPower X n))
    (hadj : HasAdjacentTrace (scalarPermTrace p scalar ρ)) :
    HasMovedTrace (scalarPermTrace p scalar ρ) := by
  intro n q hq σ
  simp only [HasAdjacentTrace, scalarPermTrace] at hadj ⊢
  cases n with
  | zero => exact (hq (Fin.eq_zero q)).elim
  | succ n =>
    obtain ⟨j, rfl⟩ := Fin.exists_succ_eq_of_ne_zero hq
    let τ : Perm (Fin (n + 1)) := Equiv.swap 0 j
    let T := fixHead (n + 1) τ
    rw [decomposeFin_succ_conj j σ, permutationTrace_conj p (ρ (n + 2)) T _, hadj]
    simpa only [inv_inv] using
      congrArg scalar (permutationTrace_conj p (ρ (n + 1)) τ⁻¹ σ)

end PropertyF.Ground.CentreCalculus

namespace PropertyF.Ground.CentreCalculus
universe v u

/-- Either the actual permutation action or its sign twist. -/
def parityPermAction (D : Type u) [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]
    [Preadditive D] [Linear ℂ D] {X : D} (hX : SelfTransparent X) (odd : Bool) (n : ℕ) :
    Perm (Fin n) →* End (tensorPower X n) :=
  if odd then Centre.twistAction (sgn ℂ n) (tensorPermAction X hX n)
  else tensorPermAction X hX n

/-- A sign twist multiplies any linear evaluation of the pivotal trace by the sign. -/
theorem scalarPermTrace_parity {D : Type u} [Category.{v} D] [MonoidalCategory D]
    [BraidedCategory D] [RightRigidCategory D] [Preadditive D] [Linear ℂ D]
    [MonoidalPreadditive D] [MonoidalLinear ℂ D]
    (p : PivotalStructure (C := D)) (scalar : End (𝟙_ D) →ₗ[ℂ] ℂ)
    {X : D} (hX : SelfTransparent X) {n : ℕ} (σ : Perm (Fin n)) :
    scalarPermTrace p scalar (parityPermAction D hX true) n σ =
      (sgn ℂ n σ : ℂ) * scalarPermTrace p scalar (tensorPermAction X hX) n σ := by
  simp [scalarPermTrace, parityPermAction, Centre.twistAction, p.rightTrace_smul, smul_eq_mul]

variable {C : BraidedFusionCategory.{v,u}} {p : PivotalStructure (C := C.Obj)}
  (hdim : HasFPSimpleDimensions C p) {X : C.Obj} (hX : SelfTransparent X) {n : ℕ}

/-- The sign-twisted permutation trace is the sign times the original trace. -/
theorem parityPermTrace_true (σ : Perm (Fin n)) :
    tr C p (parityPermAction C.Obj hX true) n σ =
      (sgn ℂ n σ : ℂ) * tr C p (tensorPermAction X hX) n σ := by
  simpa [permScalarTrace] using
    scalarPermTrace_parity p (unitScalarEquiv C).toLinearMap hX σ

section
variable {D : Type u} [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]
  [RightRigidCategory D] [Preadditive D] [Linear ℂ D] [MonoidalPreadditive D] [MonoidalLinear ℂ D]
variable (p : PivotalStructure (C := D)) (scalar : End (𝟙_ D) ≃ₐ[ℂ] ℂ)
  {X : D} (hX : SelfTransparent X) (odd : Bool) {n : ℕ}

/-- Sign twist preserves the fixed-strand trace deletion identity. -/
theorem parityPermTrace_fixHead (σ : Perm (Fin n)) :
    scalarPermTrace p scalar (parityPermAction D hX odd) (n + 1) (fixHead n σ) =
      scalar (p.rightTrace (𝟙 X)) * scalarPermTrace p scalar (parityPermAction D hX odd) n σ := by
  cases odd with
  | false => exact tensorPermTrace_fixHead p scalar hX σ
  | true =>
    change scalarPermTrace p scalar.toLinearMap (parityPermAction D hX true) (n + 1) (fixHead n σ) =
      scalar (p.rightTrace (𝟙 X)) * scalarPermTrace p scalar.toLinearMap (parityPermAction D hX true) n σ
    rw [scalarPermTrace_parity p scalar.toLinearMap, scalarPermTrace_parity p scalar.toLinearMap]
    change (sgn ℂ (n + 1) (fixHead n σ) : ℂ) *
        scalarPermTrace p scalar (tensorPermAction X hX) (n + 1) (fixHead n σ) = _
    rw [tensorPermTrace_fixHead p scalar hX σ]
    simp [fixHead, sign_decomposeFin, mul_left_comm]
end

variable (odd : Bool)

include hdim in
/-- Once the moved-strand trace deletion identity is shown for one parity,
positive dimensional integrality follows for the self-transparent object. -/
theorem integral_of_parity_moved_trace (hmoved : HasMovedTrace (tr C p (parityPermAction C.Obj hX odd))) :
    IsFPIntegral C X :=
  integral_of_trace_deletion hdim (parityPermAction C.Obj hX odd) ⟨(fun _ σ ↦ by
    simpa [fixHead, ← unitScalar_eq_equiv, ← pivotalDimension_eq_fpDimension hdim, pivotalDimension]
      using parityPermTrace_fixHead p (unitScalarEquiv C) hX odd σ), hmoved⟩

include hdim in
/-- Integrality reduces to the first-adjacent-crossing trace identity for
one of the two actual parity choices. -/
theorem integral_of_parity_adjacent_trace (hadj : HasAdjacentTrace (tr C p (parityPermAction C.Obj hX odd))) :
    IsFPIntegral C X :=
  integral_of_parity_moved_trace hdim hX odd
    (movedTrace_of_adjacent (unitScalarEquiv C) (parityPermAction C.Obj hX odd) hadj)

end PropertyF.Ground.CentreCalculus
