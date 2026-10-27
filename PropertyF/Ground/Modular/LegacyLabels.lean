module
public import PropertyF.Ground.Modular.FusionTransport
public import PropertyF.Ground.Fusion.Agreement

/-!
# Compatibility with legacy conjugate-label input

This file mentions the old category and fusion-data bundles solely to show that
their Galois-label field is constructible. It is not needed for the frozen ground
target, whose bundle-free label invariance is in `FusionTransport`.
-/
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open scoped BigOperators
@[expose] public noncomputable section
namespace PropertyF.Ground.Modular
universe v u
attribute [local instance] Abelian.hasFiniteBiproducts

/-- Forget the extra numerical choices in the old category bundle. -/
def groundOfLegacy (C : PropertyF.BraidedFusionCategory.{v,u}) : Ground.BraidedFusionCategory.{v,u} where
  Obj := C.Obj
  fusion := {
    hom_finite := C.fusion.hom_finite
    unit_simple := by
      let _ : Simple (C.fusion.simpleObject C.fusion.unitIndex) := C.fusion.simple_is_simple _
      exact Simple.of_iso C.fusion.unit_iso.symm
    finite_semisimple := ⟨C.fusion.rank, C.fusion.simpleObject, C.fusion.simple_is_simple,
      C.fusion.simple_injective, C.fusion.decomposition⟩ }

/-- Reindex the old representatives by the ground representatives. -/
theorem legacyLabels (C : PropertyF.BraidedFusionCategory.{v,u}) :
    ∃ e : Fin C.fusion.rank ≃ Fin (rank (groundOfLegacy C)),
      ∀ i, Nonempty (C.fusion.simpleObject i ≅ simples (groundOfLegacy C) (e i)) := by
  apply simple_presentation_equiv (groundOfLegacy C) C.fusion.simpleObject
    C.fusion.simple_is_simple C.fusion.simple_injective
  intro j
  let X : C.Obj := simples (groundOfLegacy C) j
  let _ : Simple X := simples_simple (groundOfLegacy C) j
  obtain ⟨m, ⟨e⟩⟩ := C.fusion.decomposition X
  let V : (Σ i, Fin (m i)) → C.Obj := fun p => C.fusion.simpleObject p.1
  have he : e.hom ≠ 0 := by
    intro h
    have hh := congrArg (fun t => t ≫ e.inv) h
    apply id_nonzero X
    simpa using hh
  have hp : ∃ p, e.hom ≫ biproduct.π V p ≠ 0 := by
    by_contra h
    push Not at h
    apply he
    apply biproduct.hom_ext
    intro p
    simpa using h p
  obtain ⟨p, hp⟩ := hp
  let _ : Simple (V p) := C.fusion.simple_is_simple p.1
  let _ : IsIso (e.hom ≫ biproduct.π V p) := CategoryTheory.isIso_of_hom_simple hp
  exact ⟨p.1, ⟨(asIso (e.hom ≫ biproduct.π V p)).symm⟩⟩

/-- The old and ground labels give the same Hom multiplicities. -/
theorem legacyCoeff (C : PropertyF.BraidedFusionCategory.{v,u})
    (e : Fin C.fusion.rank ≃ Fin (rank (groundOfLegacy C)))
    (he : ∀ i, Nonempty (C.fusion.simpleObject i ≅ simples (groundOfLegacy C) (e i)))
    (i j k : Fin C.fusion.rank) :
    Module.finrank ℂ (C.fusion.simpleObject k ⟶ C.fusion.simpleObject i ⊗ C.fusion.simpleObject j) =
      fusionCoeff (groundOfLegacy C) (e i) (e j) (e k) := by
  let vi : C.Obj := simples (groundOfLegacy C) (e i)
  let vj : C.Obj := simples (groundOfLegacy C) (e j)
  let vk : C.Obj := simples (groundOfLegacy C) (e k)
  let ai : C.fusion.simpleObject i ≅ vi := (he i).some
  let aj : C.fusion.simpleObject j ≅ vj := (he j).some
  let ak : C.fusion.simpleObject k ≅ vk := (he k).some
  have hh := (CategoryTheory.Linear.homCongr ℂ ak (ai ⊗ᵢ aj)).finrank_eq
  exact hh

/-- The two enumerations select the same tensor-unit label. -/
theorem legacyUnit (C : PropertyF.BraidedFusionCategory.{v,u})
    (e : Fin C.fusion.rank ≃ Fin (rank (groundOfLegacy C)))
    (he : ∀ i, Nonempty (C.fusion.simpleObject i ≅ simples (groundOfLegacy C) (e i))) :
    e C.fusion.unitIndex = unitIndex (groundOfLegacy C) := by
  obtain ⟨a⟩ := he C.fusion.unitIndex
  obtain ⟨b⟩ := unitIndex_iso (groundOfLegacy C)
  apply simples_injective (groundOfLegacy C)
  exact ⟨a.symm ≪≫ C.fusion.unit_iso ≪≫ b.symm⟩


/-- The specified positive fusion character agrees with the spectral-radius
FP dimensions after reindexing. -/
theorem legacyFP (C : PropertyF.BraidedFusionCategory.{v,u})
    (e : Fin C.fusion.rank ≃ Fin (rank (groundOfLegacy C)))
    (he : ∀ i, Nonempty (C.fusion.simpleObject i ≅ simples (groundOfLegacy C) (e i))) :
    ∀ i, C.fusion.fpSimple i = fpSimple (groundOfLegacy C) (e i) := by
  let G := groundOfLegacy C
  let f : Fin (rank G) → ℝ := fun j => C.fusion.fpSimple (e.symm j)
  have hunit : f (unitIndex G) = 1 := by
    have h := legacyUnit C e he
    change C.fusion.fpSimple (e.symm (unitIndex G)) = 1
    rw [← h, e.symm_apply_apply, C.fusion.fp_unit]
  have hmul : ∀ i j, f i * f j = ∑ k, (fusionCoeff G i j k : ℝ) * f k := by
    intro i j
    calc
      f i * f j = ∑ k : Fin C.fusion.rank,
          (Module.finrank ℂ (C.fusion.simpleObject k ⟶
            C.fusion.simpleObject (e.symm i) ⊗ C.fusion.simpleObject (e.symm j)) : ℝ) *
              C.fusion.fpSimple k := C.fusion.fp_character _ _
      _ = ∑ k : Fin C.fusion.rank,
          (fusionCoeff G i j (e k) : ℝ) * f (e k) := by
        apply Finset.sum_congr rfl
        intro k _
        rw [legacyCoeff C e he]
        simp only [e.apply_symm_apply, f, e.symm_apply_apply]
        rfl
      _ = ∑ k, (fusionCoeff G i j k : ℝ) * f k :=
        e.sum_comp (fun k => (fusionCoeff G i j k : ℝ) * f k)
  have hf : f = fpSimple G := by
    apply positive_character_unique G f (fpSimple G)
    · intro i; exact C.fusion.fp_positive _
    · exact fpSimple_pos G
    · exact hunit
    · exact fpSimple_unit G
    · exact hmul
    · exact fpSimple_mul G
  intro i
  have h := congrFun hf (e i)
  simpa only [f, e.symm_apply_apply] using h


/-- Construct the original `StandardInputs.conjugate_labels` field from the
actual semilinear braided equivalence and positive-character uniqueness. -/
theorem legacy_conjugate_labels {C D : PropertyF.BraidedFusionCategory.{v,u}}
    {σ : ℂ ≃+* ℂ} (h : PropertyF.GaloisConjugate C D σ) :
    ∃ e : Fin C.fusion.rank ≃ Fin D.fusion.rank,
      ∀ i, C.fusion.fpSimple i = D.fusion.fpSimple (e i) := by
  let C' := groundOfLegacy C
  let D' := groundOfLegacy D
  let h' : Ground.GaloisConjugate C' D' σ := {
    equivalence := h.equivalence
    monoidal := h.monoidal
    braided := h.braided
    map_smul := h.map_smul }
  obtain ⟨eC, heC⟩ := legacyLabels C
  obtain ⟨eD, heD⟩ := legacyLabels D
  obtain ⟨eG, heG⟩ := conjugate_labels C' D' h'
  let e := eC.trans (eG.trans eD.symm)
  refine ⟨e, ?_⟩
  intro i
  calc
    C.fusion.fpSimple i = fpSimple C' (eC i) := legacyFP C eC heC i
    _ = fpSimple D' (eG (eC i)) := heG (eC i)
    _ = D.fusion.fpSimple (e i) := by
      symm
      simpa [e] using legacyFP D eD heD (eD.symm (eG (eC i)))

end PropertyF.Ground.Modular
