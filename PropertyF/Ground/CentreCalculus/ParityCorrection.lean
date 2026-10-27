module
public import PropertyF.Ground.CentreCalculus.ProjectorReduction

/-! The sign correction needed for super-symmetric objects. -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
open scoped BigOperators
namespace PropertyF.Ground.CentreCalculus
universe v u

/-- The complex scalar sign of a permutation has square one. -/
theorem permutationSign_mul_self (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    (Centre.permutationSign ℂ n σ : ℂ) * (Centre.permutationSign ℂ n σ : ℂ) = 1 := by
  have h : (Equiv.Perm.sign σ : ℤ) * (Equiv.Perm.sign σ : ℤ) = 1 := by
    exact congrArg (fun z : ℤˣ => (z : ℤ)) (Int.units_mul_self _)
  change ((Equiv.Perm.sign σ : ℤ) : ℂ) * ((Equiv.Perm.sign σ : ℤ) : ℂ) = 1
  exact_mod_cast h

/-- Twisting an action by permutation sign turns its alternating projector
into the ordinary group-average projector. -/
theorem alternatingProjector_sign_twist (C : BraidedFusionCategory.{v,u})
    (X : C.Obj) (n : ℕ) (ρ : Equiv.Perm (Fin n) →* End X) :
    letI := permutationCardInvertible n
    Centre.alternatingProjector (k := ℂ) n
      (Centre.twistAction (Centre.permutationSign ℂ n) ρ) =
    Centre.algebraAverage (k := ℂ) ρ := by
  letI := permutationCardInvertible n
  unfold Centre.alternatingProjector
  congr 1
  ext σ
  simp only [Centre.twistAction, MonoidHom.coe_mk, OneHom.coe_mk,
    smul_smul, permutationSign_mul_self, one_smul]

/-- An unsigned permutation-trace identity also implies integrality: it is
the signed identity for the sign-twisted action. This accommodates the
opposite parity case without identifying either trace formula here. -/
theorem integral_of_unsigned_permutation_traces (C : BraidedFusionCategory.{v,u})
    (p : Dimensions.PivotalStructure (C := C.Obj))
    (hdim : ∀ i, Modular.simpleDimension C p i = (fpSimple C i : ℂ))
    (X : C.Obj)
    (hTrace : ∀ n : ℕ, ∃ ρ : Equiv.Perm (Fin n) →* End (tensorPower X n),
      (∑ σ : Equiv.Perm (Fin n), unitScalar C (p.rightTrace (ρ σ).asHom)) =
        ∏ k ∈ Finset.range n, ((fpDimension C X : ℂ) - (k : ℂ))) :
    ∃ m : ℕ, fpDimension C X = m := by
  apply integral_of_signed_permutation_traces C p hdim X
  intro n
  obtain ⟨ρ, hρ⟩ := hTrace n
  refine ⟨Centre.twistAction (Centre.permutationSign ℂ n) ρ, ?_⟩
  convert hρ using 1
  apply Finset.sum_congr rfl
  intro σ _
  simp only [Centre.twistAction, MonoidHom.coe_mk, OneHom.coe_mk, End.smul_asHom,
    p.rightTrace_smul, unitScalar_eq_equiv, map_smul, smul_eq_mul, ← mul_assoc,
    permutationSign_mul_self, one_mul]

end PropertyF.Ground.CentreCalculus
