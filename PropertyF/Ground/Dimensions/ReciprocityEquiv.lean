module
public import PropertyF.Ground.Dimensions.SimplePairing
public import PropertyF.Ground.Dimensions.ENOReciprocity

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
namespace PropertyF.Ground.Dimensions
universe v u

/-- Braiding identifies the right dual with the chosen left-dual representative. -/
def rightDualLabelIso (C : Ground.BraidedFusionCategory.{v,u}) (i : Fin (Ground.rank C)) :
    (Ground.simples C i)ᘁ ≅ Ground.simples C (Ground.dualIndex C i) :=
  leftDualIso (BraidedCategory.exactPairing_swap (Ground.simples C i) ((Ground.simples C i)ᘁ))
    HasLeftDual.exact ≪≫ Classical.choice (Ground.dualIndex_iso C i)

/-- The actual ENO Frobenius/semisimple reciprocity isomorphism: the dual of
one fusion multiplicity space is the dual-label multiplicity space. -/
def enoReciprocityEquiv (C : Ground.BraidedFusionCategory.{v,u})
    (i j k : Fin (Ground.rank C)) :
    Module.Dual ℂ (Ground.simples C k ⟶ Ground.simples C i ⊗ Ground.simples C j) ≃ₗ[ℂ]
      (Ground.simples C j ⟶ Ground.simples C (Ground.dualIndex C i) ⊗ Ground.simples C k) := by
  let Xi := Ground.simples C i
  let Xj := Ground.simples C j
  let Xk := Ground.simples C k
  letI : ExactPairing (Xiᘁ) Xi := BraidedCategory.exactPairing_swap Xi (Xiᘁ)
  let eq1 := (simpleHomPairingEquiv C k (Xi ⊗ Xj)).symm
  let eq2 := Ground.tensorLeftHomLinearEquiv Xj (Xiᘁ) Xi Xk
  let eq3 := Linear.homCongr ℂ (Iso.refl Xj) (rightDualLabelIso C i ⊗ᵢ Iso.refl Xk)
  exact eq1.trans (eq2.trans eq3)

/-- The categorical operator intertwining under the actual reciprocity
isomorphism implies ENO's trace-transpose relation. -/
theorem enoTraceMatrix_reciprocity_of_operator_intertwining
    (C : Ground.BraidedFusionCategory.{v,u})
    (hintertwine : ∀ i j k
      (v : Module.Dual ℂ (Ground.simples C j ⟶ Ground.simples C i ⊗ Ground.simples C k)),
      enoReciprocityEquiv C i k j
        (Module.Dual.transpose (multiplicityDefect C i k j).toLinearMap v) =
      rootDualSign C i • (multiplicityDefect C (Ground.dualIndex C i) j k)
        (enoReciprocityEquiv C i k j v)) :
    ∀ i j k, enoTraceMatrix C (Ground.dualIndex C i) j k =
      rootDualSign C i * enoTraceMatrix C i k j := by
  intro i j k
  let E := enoReciprocityEquiv C i k j
  let A := (multiplicityDefect C i k j).toLinearMap
  let B := (multiplicityDefect C (Ground.dualIndex C i) j k).toLinearMap
  have hconj : E.conj (Module.Dual.transpose A) = rootDualSign C i • B := by
    ext w
    obtain ⟨v, rfl⟩ := E.surjective w
    simpa [E, A, B, LinearEquiv.conj_apply] using hintertwine i j k v
  letI : FiniteDimensional ℂ (Ground.simples C j ⟶ Ground.simples C i ⊗ Ground.simples C k) :=
    Ground.IsFusionCategory.hom_finite _ _
  letI : FiniteDimensional ℂ (Ground.simples C k ⟶ Ground.simples C (Ground.dualIndex C i) ⊗ Ground.simples C j) :=
    Ground.IsFusionCategory.hom_finite _ _
  have ht := congrArg (LinearMap.trace ℂ _) hconj
  simp only [LinearMap.trace_conj', LinearMap.trace_transpose', map_smul, smul_eq_mul] at ht
  have hs := rootDualSign_sq C i
  change LinearMap.trace ℂ _ A = rootDualSign C i * LinearMap.trace ℂ _ B at ht
  change LinearMap.trace ℂ _ B = rootDualSign C i * LinearMap.trace ℂ _ A
  calc
    _ = (rootDualSign C i * rootDualSign C i) * LinearMap.trace ℂ _ B := by rw [hs, one_mul]
    _ = rootDualSign C i * (rootDualSign C i * LinearMap.trace ℂ _ B) := by ring
    _ = _ := by rw [← ht]

end PropertyF.Ground.Dimensions
