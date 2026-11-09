module
public import MTC.PropertyF.Reduction.TwistedRigidity
public import MTC.PropertyF.Reduction.ActualCenterReduction
public import MTC.PropertyF.Pivotal.Statement

/-!
# Galois arithmetic for pivotal Property F

Scalar twisting transports the intrinsic global dimension. The arithmetic
step then turns pseudo-unitarity of all conjugates into weak integrality.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory MTC.Fusion MTC.PropertyF.Reduction
open scoped BigOperators
namespace MTC.PropertyF.Pivotal
universe v u
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
variable (C : BraidedFusionCategory.{v,u}) (σ : ℂ ≃+* ℂ)
local notation "Cσ" => ScalarTwist.category C σ

/-- Scalar twisting gives a semilinear braided equivalence. -/
def scalarTwistGaloisConjugate : GaloisConjugate C Cσ σ := by
  let E : C.Obj ≌ (ScalarTwist.category C σ).Obj := CategoryTheory.Equivalence.refl
  letI : E.functor.Monoidal := by
    change (𝟭 C.Obj).Monoidal
    infer_instance
  letI : E.functor.Braided := by
    change (𝟭 C.Obj).Braided
    infer_instance
  refine { equivalence := E, map_smul := ?_ }
  intro X Y z f
  change z • f = σ.symm (σ z) • f
  rw [σ.symm_apply_apply]

/-- Transparency is invariant under isomorphism. -/
theorem transparent_of_iso {X Y : C.Obj} (e : X ≅ Y) (h : MTC.Center.Transparent Y) :
    MTC.Center.Transparent X := by
  intro Z
  change Modular.doubleBraiding X Z = 𝟙 _
  let f := e.hom ⊗ₘ 𝟙 Z
  letI : IsIso f := inferInstance
  apply (cancel_mono f).1
  simpa only [Category.id_comp, Category.comp_id, Modular.doubleBraiding] using
    (Modular.doubleBraiding_natural e.hom (𝟙 Z)).trans (by
      rw [show Modular.doubleBraiding Y Z = 𝟙 _ from h Z, Category.comp_id])

/-- Scalar twisting preserves categorical nondegeneracy. -/
theorem isNondegenerate_scalarTwist (h : IsNondegenerate C) : IsNondegenerate Cσ := by
  intro j hj
  letI : Simple (simples Cσ j) := simples_simple Cσ j
  obtain ⟨i, ⟨e⟩⟩ := exists_simple_iso C (simples Cσ j)
  have hi : MTC.Center.Transparent (simples C i) := transparent_of_iso C e.symm hj
  have hiu := h i hi
  apply simples_injective Cσ
  have hu : Nonempty (simples C i ≅ 𝟙_ C.Obj) := by
    simpa only [hiu] using unitIndex_iso C
  exact ⟨e ≪≫ hu.some ≪≫ (unitIndex_iso Cσ).some.symm⟩

/-- The intrinsic squared norm commutes with scalar twisting. -/
theorem squaredNorm_scalarTwist (X : C.Obj) :
    squaredNorm Cσ X = σ (squaredNorm C X) := by
  change unitScalar Cσ (MTC.Braided.rightQuantumTrace (doubleDualIso C X)) *
      unitScalar Cσ (MTC.Braided.leftQuantumTrace (doubleDualIso C X)) = _
  rw [ScalarTwist.unitScalar_twist, ScalarTwist.unitScalar_twist, ← map_mul]
  rfl

/-- Global dimension transforms by the field automorphism; no commutation
of that automorphism with complex conjugation is assumed. -/
theorem globalDimension_scalarTwist : globalDimension Cσ = σ (globalDimension C) := by
  obtain ⟨e, he⟩ := Modular.simpleLabels_equiv C Cσ (CategoryTheory.Equivalence.refl)
  rw [globalDimension, globalDimension, map_sum]
  symm
  apply Fintype.sum_equiv e
  intro i
  rw [← squaredNorm_scalarTwist]
  exact MTC.CategoryTheory.Dimensions.target_squaredNorm_iso Cσ (he i).some

/-- If every represented Galois conjugate is pseudo-unitary, the global FP
dimension is fixed by all complex field automorphisms. -/
theorem globalFPDimension_galois_fixed_of_all_conjugates
    (hAll : AllGaloisConjugatesPseudoUnitary C) :
    σ (globalFPDimension C : ℂ) = (globalFPDimension C : ℂ) := by
  let E : C.Obj ≌ C.Obj := CategoryTheory.Equivalence.refl
  letI : E.functor.Braided := by
    change (𝟭 C.Obj).Braided
    infer_instance
  have hC : PseudoUnitary C := hAll C (RingEquiv.refl ℂ)
    ⟨{ equivalence := E, map_smul := by intros; rfl }⟩
  let Eσ := scalarTwistGaloisConjugate C σ
  have hσ : PseudoUnitary Cσ := hAll Cσ σ ⟨Eσ⟩
  calc
    σ (globalFPDimension C : ℂ) = σ (globalDimension C) := congrArg σ hC.symm
    _ = globalDimension Cσ := (globalDimension_scalarTwist C σ).symm
    _ = (globalFPDimension Cσ : ℂ) := hσ
    _ = (globalFPDimension C : ℂ) :=
      congrArg (fun x : ℝ ↦ (x : ℂ)) (Modular.conjugate_globalFPDimension Eσ).symm

/-- Pseudo-unitarity of all Galois conjugates implies weak integrality. -/
theorem weaklyIntegral_of_all_conjugates_pseudoUnitary
    (hAll : AllGaloisConjugatesPseudoUnitary C) :
    MTC.Braided.WeaklyIntegral (globalFPDimension C) :=
  integral_eq_int_of_complex_galois_fixed
    (IsIntegral.sum _ fun i _ ↦ (fpSimple_isIntegral i).pow 2)
    (fun σ ↦ globalFPDimension_galois_fixed_of_all_conjugates C σ hAll)

/-- It already suffices to know pseudo-unitarity for the canonical scalar
twists: no separate assumption about arbitrary equivalent presentations is
needed for arithmetic descent. -/
theorem weaklyIntegral_of_all_scalarTwists_pseudoUnitary
    (h : ∀ τ : ℂ ≃+* ℂ, PseudoUnitary (ScalarTwist.category C τ)) :
    MTC.Braided.WeaklyIntegral (globalFPDimension C) := by
  have hfp (τ : ℂ ≃+* ℂ) :
      globalFPDimension (ScalarTwist.category C τ) = globalFPDimension C :=
    (Modular.conjugate_globalFPDimension (scalarTwistGaloisConjugate C τ)).symm
  have hC : globalDimension C = (globalFPDimension C : ℂ) := by
    have h0 := h (RingEquiv.refl ℂ)
    change globalDimension (ScalarTwist.category C (RingEquiv.refl ℂ)) = _ at h0
    rw [globalDimension_scalarTwist, hfp] at h0
    simpa using h0
  apply integral_eq_int_of_complex_galois_fixed
    (IsIntegral.sum _ fun i _ ↦ (fpSimple_isIntegral i).pow 2)
  intro τ
  calc
    τ (globalFPDimension C : ℂ) = τ (globalDimension C) := congrArg τ hC.symm
    _ = globalDimension (ScalarTwist.category C τ) := (globalDimension_scalarTwist C τ).symm
    _ = (globalFPDimension (ScalarTwist.category C τ) : ℂ) := h τ
    _ = (globalFPDimension C : ℂ) := congrArg (fun x : ℝ ↦ (x : ℂ)) (hfp τ)

end MTC.PropertyF.Pivotal
