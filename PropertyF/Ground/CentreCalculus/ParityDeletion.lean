module
public import PropertyF.Ground.CentreCalculus.ProjectorReduction
public import PropertyF.Ground.CentreCalculus.PermutationInsert

/-!
# Parity-corrected permutation traces

Twisting by permutation sign relates signed and unsigned trace criteria.
The fixed-head and adjacent-crossing identities reduce integrality to a
one-strand deletion formula for either parity choice. We write `tr C p ρ n σ`
for the scalar pivotal trace of the permutation action.
-/
@[expose] public noncomputable section
local notation "tr" => PropertyF.Ground.CentreCalculus.permScalarTrace
open PropertyF.Ground.Modular (HasFPSimpleDimensions)
open PropertyF.Ground.Centre (permutationSign)
open Equiv.Perm (decomposeFin)
open PropertyF.Ground.Dimensions
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.CentreCalculus
universe v u

/-- Either the actual permutation action or its sign twist. -/
def parityPermAction (C : BraidedFusionCategory.{v,u}) {X : C.Obj}
    (hX : SelfTransparent X) (odd : Bool) (n : ℕ) :
    Equiv.Perm (Fin n) →* End (tensorPower X n) :=
  if odd then Centre.twistAction (permutationSign ℂ n) (tensorPermAction X hX n)
  else tensorPermAction X hX n

variable {C : BraidedFusionCategory.{v,u}} {p : PivotalStructure (C := C.Obj)}
  (hdim : HasFPSimpleDimensions C p) {X : C.Obj} (hX : SelfTransparent X)

/-- The sign-twisted permutation trace is the sign times the original trace. -/
theorem parityPermScalarTrace_true (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    tr C p (parityPermAction C hX true) n σ =
      (permutationSign ℂ n σ : ℂ) * tr C p (tensorPermAction X hX) n σ := by
  simp [permScalarTrace, parityPermAction, Centre.twistAction, p.rightTrace_smul,
    unitScalar_eq_equiv, smul_eq_mul]

variable (odd : Bool)

include hdim in
/-- Sign twist preserves the fixed-strand trace deletion identity. -/
theorem parityPermTrace_fixHead {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    tr C p (parityPermAction C hX odd) (n + 1) (fixHead n σ) =
    (fpDimension C X : ℂ) * tr C p (parityPermAction C hX odd) n σ := by
  cases odd with
  | false => exact tensorPermTrace_fixHead hdim hX σ
  | true =>
    have hs : (permutationSign ℂ (n + 1) (fixHead n σ) : ℂ) =
        (permutationSign ℂ n σ : ℂ) := by
      simpa [fixHead] using sign_decomposeFin (R := ℂ) 0 σ
    simp only [parityPermScalarTrace_true, hs, tensorPermTrace_fixHead hdim hX σ, mul_left_comm]

include hdim in
/-- Once the moved-strand trace deletion identity is shown for one parity,
positive dimensional integrality follows for the self-transparent object. -/
theorem integral_of_parity_moved_trace (hmoved : HasMovedTrace (tr C p (parityPermAction C hX odd))) :
    IsFPIntegral C X :=
  integral_of_trace_deletion hdim (parityPermAction C hX odd)
    ⟨(fun _ σ ↦ parityPermTrace_fixHead hdim hX odd σ), hmoved⟩

end PropertyF.Ground.CentreCalculus

namespace PropertyF.Ground.CentreCalculus
open CategoryTheory CategoryTheory.MonoidalCategory

/-- A moved-point extension is conjugate to the first adjacent extension. -/
theorem decomposeFin_succ_conj {n : ℕ} (j : Fin (n + 1)) (σ : Equiv.Perm (Fin (n + 1))) :
    let τ := Equiv.swap 0 j
    let T := fixHead (n + 1) τ
    decomposeFin.symm (j.succ, σ) = T * decomposeFin.symm (1, τ⁻¹ * σ * τ) * T⁻¹ := by
  let τ : Equiv.Perm (Fin (n + 1)) := Equiv.swap 0 j
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
theorem movedTrace_of_adjacent {C : BraidedFusionCategory.{v,u}}
    {p : PivotalStructure (C := C.Obj)} {X : C.Obj}
    (ρ : ∀ n : ℕ, Equiv.Perm (Fin n) →* End (tensorPower X n))
    (hadj : HasAdjacentTrace (tr C p ρ)) : HasMovedTrace (tr C p ρ) := by
  intro n q hq σ
  simp only [HasAdjacentTrace, permScalarTrace] at hadj ⊢
  cases n with
  | zero => exact (hq (Fin.eq_zero q)).elim
  | succ n =>
    obtain ⟨j, rfl⟩ := Fin.exists_succ_eq_of_ne_zero hq
    let τ : Equiv.Perm (Fin (n + 1)) := Equiv.swap 0 j
    let T := fixHead (n + 1) τ
    rw [decomposeFin_succ_conj j σ, permutationTrace_conj p (ρ (n + 2)) T _, hadj]
    simpa only [inv_inv] using
      congrArg (unitScalar C) (permutationTrace_conj p (ρ (n + 1)) τ⁻¹ σ)

end PropertyF.Ground.CentreCalculus

namespace PropertyF.Ground.CentreCalculus
open CategoryTheory CategoryTheory.MonoidalCategory
universe v u

variable {C : BraidedFusionCategory.{v,u}} {p : PivotalStructure (C := C.Obj)}
  (hdim : HasFPSimpleDimensions C p)

include hdim in
/-- Integrality reduces to the first-adjacent-crossing trace identity for
one of the two actual parity choices. -/
theorem integral_of_parity_adjacent_trace {X : C.Obj} (hX : SelfTransparent X) (odd : Bool)
    (hadj : HasAdjacentTrace (tr C p (parityPermAction C hX odd))) :
    IsFPIntegral C X :=
  integral_of_parity_moved_trace hdim hX odd
    (movedTrace_of_adjacent (parityPermAction C hX odd) hadj)

end PropertyF.Ground.CentreCalculus
