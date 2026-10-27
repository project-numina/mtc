module
public import PropertyF.Ground.Integrate.Arithmetic
public import PropertyF.Ground.Integrate.Fixedness
public import PropertyF.Ground.Integrate.ConjugateBound
public import PropertyF.Ground.Integrate.PropertyFTransport
public import PropertyF.Ground.Modular.FusionTransport

/-! Bundle-free reduction of the target to FP invariance under conjugacy and the
paper's Galois-fixedness argument for pseudo-unitary categories. -/

@[expose] public noncomputable section
namespace PropertyF.Ground
universe v u

/-- The two remaining categorical obligations suffice to prove the frozen target.
This is a reduction with explicitly displayed premises, not the target theorem. -/
theorem target_of_galois_invariance_and_pseudo_fixedness
    (hInvariant : ∀ {C D : BraidedFusionCategory.{v,u}} {σ : ℂ ≃+* ℂ},
      GaloisConjugate C D σ → globalFPDimension C = globalFPDimension D)
    (hFixed : ∀ (C : BraidedFusionCategory.{v,u}), PseudoUnitary C →
      HasPropertyF C.Obj → ∀ σ : ℂ ≃+* ℂ,
      σ (globalFPDimension C : ℂ) = (globalFPDimension C : ℂ)) :
    TargetStatement.{v,u} := by
  intro C hPU hF
  obtain ⟨D, σ, ⟨E⟩, hD⟩ := hPU
  have hDF : HasPropertyF D.Obj := galois_propertyF E hF
  have hDInt := weaklyIntegral_of_globalFPDimension_fixed D (hFixed D hD hDF)
  rwa [hInvariant E]

/-- Global FP invariance and property-F transport are constructed. The sole
remaining premise is the pseudo-unitary fixedness argument from the paper. -/
theorem target_of_pseudo_fixedness
    (hFixed : ∀ (C : BraidedFusionCategory.{v,u}), PseudoUnitary C →
      HasPropertyF C.Obj → ∀ σ : ℂ ≃+* ℂ,
      σ (globalFPDimension C : ℂ) = (globalFPDimension C : ℂ)) :
    TargetStatement.{v,u} :=
  target_of_galois_invariance_and_pseudo_fixedness
    (fun {C D} {_} E => Modular.conjugate_globalFPDimension C D E) hFixed

/-- Reduction to the three remaining numerical consequences of the categorical
centre argument. These are explicit premises and are not part of the target. -/
theorem target_of_numerical_witnesses
    (hPositive : ∀ (C : BraidedFusionCategory.{v,u}), PseudoUnitary C →
      HasPropertyF C.Obj → 0 < globalFPDimension C)
    (hConjugates : ∀ (C : BraidedFusionCategory.{v,u}), PseudoUnitary C →
      HasPropertyF C.Obj → ∀ σ : ℂ ≃+* ℂ, ∃ a : ℝ,
        0 < a ∧ a ≤ globalFPDimension C ∧
          σ (globalFPDimension C : ℂ) = (a : ℂ))
    (hWitness : ∀ (C : BraidedFusionCategory.{v,u}), PseudoUnitary C →
      HasPropertyF C.Obj → ∀ (σ : ℂ ≃+* ℂ) (a b : ℝ),
        0 < a → a < globalFPDimension C →
        σ (globalFPDimension C : ℂ) = (a : ℂ) →
        σ.symm (globalFPDimension C : ℂ) = (b : ℂ) →
        ∃ f d : ℝ, σ (f : ℂ) = (d : ℂ) ∧
          f * b = globalFPDimension C ∧ 1 ≤ f ∧ f = |d|) :
    TargetStatement.{v,u} := by
  apply target_of_pseudo_fixedness
  intro C hPU hF
  exact galois_fixed_of_smaller_conjugate_witness (globalFPDimension C)
    (hPositive C hPU hF) (hConjugates C hPU hF) (hWitness C hPU hF)

/-- The unit simple proves positivity, leaving only the bounded-conjugate and
centre/rigidity witness obligations. -/
theorem target_of_bounded_conjugates_and_witness
    (hConjugates : ∀ (C : BraidedFusionCategory.{v,u}), PseudoUnitary C →
      HasPropertyF C.Obj → ∀ σ : ℂ ≃+* ℂ, ∃ a : ℝ,
        0 < a ∧ a ≤ globalFPDimension C ∧
          σ (globalFPDimension C : ℂ) = (a : ℂ))
    (hWitness : ∀ (C : BraidedFusionCategory.{v,u}), PseudoUnitary C →
      HasPropertyF C.Obj → ∀ (σ : ℂ ≃+* ℂ) (a b : ℝ),
        0 < a → a < globalFPDimension C →
        σ (globalFPDimension C : ℂ) = (a : ℂ) →
        σ.symm (globalFPDimension C : ℂ) = (b : ℂ) →
        ∃ f d : ℝ, σ (f : ℂ) = (d : ℂ) ∧
          f * b = globalFPDimension C ∧ 1 ≤ f ∧ f = |d|) :
    TargetStatement.{v,u} :=
  target_of_numerical_witnesses (fun C _ _ => lt_of_lt_of_le (by norm_num) (one_le_globalFPDimension C)) hConjugates hWitness

/-- A spherical structure with self-dual simple dimensions supplies all
conjugate bounds. The remaining categorical premise is the centre witness. -/
theorem target_of_spherical_and_witness
    (hSpherical : ∀ (C : BraidedFusionCategory.{v,u}), PseudoUnitary C →
      ∃ p : Dimensions.PivotalStructure (C := C.Obj), p.IsSpherical ∧
        ∀ i, Dimensions.pivotalDimension C p (simples C (dualIndex C i)) =
          Dimensions.pivotalDimension C p (simples C i))
    (hWitness : ∀ (C : BraidedFusionCategory.{v,u}), PseudoUnitary C →
      HasPropertyF C.Obj → ∀ (σ : ℂ ≃+* ℂ) (a b : ℝ),
        0 < a → a < globalFPDimension C →
        σ (globalFPDimension C : ℂ) = (a : ℂ) →
        σ.symm (globalFPDimension C : ℂ) = (b : ℂ) →
        ∃ f d : ℝ, σ (f : ℂ) = (d : ℂ) ∧
          f * b = globalFPDimension C ∧ 1 ≤ f ∧ f = |d|) :
    TargetStatement.{v,u} := by
  apply target_of_bounded_conjugates_and_witness
  · intro C hPU _ σ
    obtain ⟨p, hp, hdual⟩ := hSpherical C hPU
    exact positive_bounded_conjugates_of_spherical C hPU p hp hdual σ
  · exact hWitness

end PropertyF.Ground
