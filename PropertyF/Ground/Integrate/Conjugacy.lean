module
public import PropertyF.Ground.Target

/-! Elementary consistency checks for the frozen conjugacy condition. -/

@[expose] public noncomputable section
open CategoryTheory
namespace PropertyF.Ground
universe v u

/-- Identity gives a genuine semilinear braided equivalence. -/
def GaloisConjugate.refl (C : BraidedFusionCategory.{v,u}) :
    GaloisConjugate C C (RingEquiv.refl ℂ) where
  equivalence := CategoryTheory.Equivalence.refl
  monoidal := inferInstanceAs ((𝟭 C.Obj).Monoidal)
  braided := inferInstanceAs ((𝟭 C.Obj).Braided)
  map_smul := by intros; rfl

/-- Semilinear braided equivalences compose with their scalar automorphisms. -/
def GaloisConjugate.trans {C D E : BraidedFusionCategory.{v,u}}
    {σ τ : ℂ ≃+* ℂ} (F : GaloisConjugate C D σ) (G : GaloisConjugate D E τ) :
    GaloisConjugate C E (σ.trans τ) := by
  letI := F.braided
  letI := G.braided
  exact {
    equivalence := F.equivalence.trans G.equivalence
    monoidal := inferInstance
    braided := by
      change (F.equivalence.functor ⋙ G.equivalence.functor).Braided
      infer_instance
    map_smul := by
      intro X Y z f
      change G.equivalence.functor.map (F.equivalence.functor.map (z • f)) = _
      rw [F.map_smul, G.map_smul]
      rfl
  }

/-- Pseudo-unitary categories satisfy the conjugate condition themselves. -/
theorem hasPseudoUnitaryGaloisConjugate_of_pseudoUnitary
    (C : BraidedFusionCategory.{v,u}) (h : PseudoUnitary C) :
    HasPseudoUnitaryGaloisConjugate C :=
  ⟨C, RingEquiv.refl ℂ, ⟨GaloisConjugate.refl C⟩, h⟩

end PropertyF.Ground
