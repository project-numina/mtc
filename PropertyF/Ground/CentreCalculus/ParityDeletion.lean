module
public import PropertyF.Ground.CentreCalculus.ProjectorReduction
public import PropertyF.Ground.CentreCalculus.PermutationInsert

/-!
# Parity-corrected permutation traces

Twisting by permutation sign relates signed and unsigned trace criteria.
The fixed-head and adjacent-crossing identities reduce integrality to a
one-strand deletion formula for either parity choice.
-/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.CentreCalculus
universe v u

/-- Either the actual permutation action or its sign twist. -/
def parityPermutationAction (C : BraidedFusionCategory.{v,u}) {X : C.Obj}
    (hX : SelfTransparent X) (odd : Bool) (n : ℕ) :
    Equiv.Perm (Fin n) →* End (tensorPower X n) :=
  if odd then Centre.twistAction (Centre.permutationSign ℂ n) (tensorPermutationAction X hX n)
  else tensorPermutationAction X hX n

variable (C : BraidedFusionCategory.{v,u}) (p : Dimensions.PivotalStructure (C := C.Obj))
  (hdim : Modular.HasFPSimpleDimensions C p)

include hdim in
/-- Sign twist preserves the fixed-strand trace deletion identity. -/
theorem parityPermutationTrace_fixHead {X : C.Obj} (hX : SelfTransparent X) (odd : Bool)
    {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    permutationScalarTrace C p (parityPermutationAction C hX odd) (n + 1) (fixHead n σ) =
    (fpDimension C X : ℂ) * permutationScalarTrace C p (parityPermutationAction C hX odd) n σ := by
  cases odd with
  | false => exact tensorPermutationTrace_fixHead C p hdim X hX n σ
  | true =>
    have hs : (Centre.permutationSign ℂ (n + 1) (fixHead n σ) : ℂ) =
        (Centre.permutationSign ℂ n σ : ℂ) := by
      simpa [fixHead] using sign_decomposeFin 0 σ
    have ht := tensorPermutationTrace_fixHead C p hdim X hX n σ
    dsimp only [permutationScalarTrace] at ht
    simp only [permutationScalarTrace, parityPermutationAction, ↓reduceIte, Centre.twistAction,
      MonoidHom.coe_mk, OneHom.coe_mk, End.smul_asHom, p.rightTrace_smul,
      unitScalar_eq_equiv, map_smul, smul_eq_mul]
    rw [hs, ← unitScalar_eq_equiv, ← unitScalar_eq_equiv,
      ht]
    ring

include hdim in
/-- Once the moved-strand trace deletion identity is shown for one parity,
positive dimensional integrality follows for the self-transparent object. -/
theorem integral_of_parity_moved_trace {X : C.Obj} (hX : SelfTransparent X) (odd : Bool)
    (hmoved : ∀ n (q : Fin (n + 1)), q ≠ 0 → ∀ σ,
      permutationScalarTrace C p (parityPermutationAction C hX odd) (n + 1)
        (Equiv.Perm.decomposeFin.symm (q, σ)) =
      permutationScalarTrace C p (parityPermutationAction C hX odd) n σ) :
    ∃ m : ℕ, fpDimension C X = m :=
  integral_of_trace_deletion C p hdim X (parityPermutationAction C hX odd)
    (fun _ σ ↦ parityPermutationTrace_fixHead C p hdim hX odd σ) hmoved

end PropertyF.Ground.CentreCalculus

namespace PropertyF.Ground.CentreCalculus
open CategoryTheory CategoryTheory.MonoidalCategory

/-- A one-point permutation extension is the swap of that point with zero,
followed by the fixed-head extension of the smaller permutation. -/
theorem decomposeFin_eq_swap_fixHead {n : ℕ} (q : Fin (n + 1)) (σ : Equiv.Perm (Fin n)) :
    Equiv.Perm.decomposeFin.symm (q, σ) = Equiv.swap 0 q * fixHead n σ := by
  ext x
  refine Fin.cases ?_ (fun j => ?_) x <;>
    simp [fixHead, Equiv.Perm.mul_apply]

/-- Traces of permutation representations are invariant under conjugation. -/
theorem permutationTrace_conj {C : Type u} [Category.{v} C] [MonoidalCategory C]
    [RightRigidCategory C] (p : Dimensions.PivotalStructure (C := C)) {X : C}
    {G : Type*} [Group G] (ρ : G →* End X) (g h : G) :
    p.rightTrace (ρ (g * h * g⁻¹)).asHom = p.rightTrace (ρ h).asHom := by
  have hcyc := p.rightTrace_cyclic (ρ (g * h)).asHom (ρ g⁻¹).asHom
  simpa only [← End.mul_asHom, ← map_mul, mul_assoc, inv_mul_cancel_left] using hcyc.symm

/-- It is enough to establish the moved-strand deletion identity for the
first adjacent swap: all other positions follow by conjugating the remaining
strands. -/
theorem movedTrace_of_adjacent (C : BraidedFusionCategory.{v,u})
    (p : Dimensions.PivotalStructure (C := C.Obj)) (X : C.Obj)
    (ρ : ∀ n : ℕ, Equiv.Perm (Fin n) →* End (tensorPower X n))
    (hadj : ∀ n (σ : Equiv.Perm (Fin (n + 1))),
      permutationScalarTrace C p ρ (n + 2) (Equiv.Perm.decomposeFin.symm (1, σ)) =
      permutationScalarTrace C p ρ (n + 1) σ) :
    ∀ n (q : Fin (n + 1)), q ≠ 0 → ∀ σ,
      permutationScalarTrace C p ρ (n + 1) (Equiv.Perm.decomposeFin.symm (q, σ)) =
      permutationScalarTrace C p ρ n σ := by
  intro n q hq σ
  simp only [permutationScalarTrace] at hadj ⊢
  cases n with
  | zero => exact (hq (Fin.eq_zero q)).elim
  | succ n =>
    obtain ⟨j, rfl⟩ := Fin.exists_succ_eq_of_ne_zero hq
    let τ : Equiv.Perm (Fin (n + 1)) := Equiv.swap 0 j
    let T := fixHead (n + 1) τ
    have hswap : Equiv.swap 0 j.succ = T * Equiv.swap 0 1 * T⁻¹ := by
      simpa [T, τ, fixHead] using Equiv.swap_apply_apply T (0 : Fin (n + 2)) 1
    have hd : Equiv.Perm.decomposeFin.symm (j.succ, σ) =
        T * (Equiv.Perm.decomposeFin.symm (1, τ⁻¹ * σ * τ)) * T⁻¹ := by
      rw [decomposeFin_eq_swap_fixHead, decomposeFin_eq_swap_fixHead, hswap]
      simp only [map_mul, map_inv, ← mul_assoc]
      simp [T, mul_assoc]
    rw [hd, permutationTrace_conj p (ρ (n + 2)) T _, hadj]
    have hconj := permutationTrace_conj p (ρ (n + 1)) τ⁻¹ σ
    simp only [inv_inv] at hconj
    rw [hconj]

end PropertyF.Ground.CentreCalculus

namespace PropertyF.Ground.CentreCalculus
open CategoryTheory CategoryTheory.MonoidalCategory
universe v u

variable (C : BraidedFusionCategory.{v,u}) (p : Dimensions.PivotalStructure (C := C.Obj))
  (hdim : Modular.HasFPSimpleDimensions C p)

include hdim in
/-- Integrality reduces to the first-adjacent-crossing trace identity for
one of the two actual parity choices. -/
theorem integral_of_parity_adjacent_trace {X : C.Obj} (hX : SelfTransparent X) (odd : Bool)
    (hadj : ∀ n (σ : Equiv.Perm (Fin (n + 1))),
      permutationScalarTrace C p (parityPermutationAction C hX odd) (n + 2)
        (Equiv.Perm.decomposeFin.symm (1, σ)) =
      permutationScalarTrace C p (parityPermutationAction C hX odd) (n + 1) σ) :
    ∃ m : ℕ, fpDimension C X = m :=
  integral_of_parity_moved_trace C p hdim hX odd
    (movedTrace_of_adjacent C p X (parityPermutationAction C hX odd) hadj)

end PropertyF.Ground.CentreCalculus
