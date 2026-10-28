module
public import PropertyF.Ground.Dimensions.ReciprocityEquiv
public import PropertyF.Ground.Dimensions.ENOCoherence

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
namespace PropertyF.Ground.Dimensions
universe v u

/-- Actual Frobenius reciprocity using the chosen dual-label identification. -/
def enoFrobeniusEquiv (C : Ground.BraidedFusionCategory.{v,u})
    (i j k : Fin (Ground.rank C)) :
    (Ground.simples C i ⊗ Ground.simples C j ⟶ Ground.simples C k) ≃ₗ[ℂ]
      (Ground.simples C j ⟶ Ground.simples C (Ground.dualIndex C i) ⊗ Ground.simples C k) := by
  let Xi := Ground.simples C i
  let Xj := Ground.simples C j
  let Xk := Ground.simples C k
  letI : ExactPairing (Xiᘁ) Xi := BraidedCategory.exactPairing_swap Xi (Xiᘁ)
  exact (Ground.tensorLeftHomLinearEquiv Xj (Xiᘁ) Xi Xk).trans
    (Linear.homCongr ℂ (Iso.refl Xj) (rightDualLabelIso C i ⊗ᵢ Iso.refl Xk))

/-- The ENO reciprocity equivalence is the composition pairing followed by
the actual Frobenius reciprocity map. -/
theorem enoReciprocityEquiv_pairing (C : Ground.BraidedFusionCategory.{v,u})
    (i j k : Fin (Ground.rank C))
    (g : Ground.simples C i ⊗ Ground.simples C j ⟶ Ground.simples C k) :
    enoReciprocityEquiv C i j k (simpleHomPairingEquiv C k (Ground.simples C i ⊗ Ground.simples C j) g) =
      enoFrobeniusEquiv C i j k g := by
  simp [enoReciprocityEquiv, enoFrobeniusEquiv]

/-- It is enough to prove the defect compatibility on ordinary categorical
morphisms before applying the perfect-pairing duality. -/
theorem enoTraceMatrix_reciprocity_of_frobenius_defect
    (C : Ground.BraidedFusionCategory.{v,u})
    (hcompat : ∀ i j k (g : Ground.simples C i ⊗ Ground.simples C k ⟶ Ground.simples C j),
      enoFrobeniusEquiv C i k j ((rootTensorDefect C (Ground.simples C i) (Ground.simples C k)).hom ≫ g) =
      rootDualSign C i • (enoFrobeniusEquiv C i k j g ≫
        (rootTensorDefect C (Ground.simples C (Ground.dualIndex C i)) (Ground.simples C j)).hom)) :
    ∀ i j k, enoTraceMatrix C (Ground.dualIndex C i) j k = rootDualSign C i * enoTraceMatrix C i k j := by
  apply enoTraceMatrix_reciprocity_of_operator_intertwining C
  intro i j k v
  letI : Simple (Ground.simples C j) := Ground.simples_simple C j
  let P := simpleHomPairingEquiv C j (Ground.simples C i ⊗ Ground.simples C k)
  let g := P.symm v
  have hv : P g = v := P.apply_symm_apply v
  rw [← hv]
  have hn := simpleHomPairing_natural C (Ground.simples C j)
    (Ground.simples C i ⊗ Ground.simples C k) g
    (rootTensorDefect C (Ground.simples C i) (Ground.simples C k)).hom
  have hm : (multiplicityDefect C i k j).toLinearMap =
      Linear.rightComp ℂ (Ground.simples C j) (rootTensorDefect C (Ground.simples C i) (Ground.simples C k)).hom := by
    ext f
    exact multiplicityDefect_apply C i k j f
  rw [hm]
  change P ((rootTensorDefect C (Ground.simples C i) (Ground.simples C k)).hom ≫ g) =
    Module.Dual.transpose (Linear.rightComp ℂ (Ground.simples C j)
      (rootTensorDefect C (Ground.simples C i) (Ground.simples C k)).hom) (P g) at hn
  rw [← hn, enoReciprocityEquiv_pairing, enoReciprocityEquiv_pairing, hcompat]
  simp [multiplicityDefect_apply]

end PropertyF.Ground.Dimensions
