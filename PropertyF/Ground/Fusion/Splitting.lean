module
public import PropertyF.Ground.Target
public import Mathlib.CategoryTheory.Preadditive.Schur

/-! Splitting maps from simples in a finite semisimple category. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits

namespace PropertyF.Ground
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [BraidedCategory C] [Abelian C] [Linear ℂ C] [RigidCategory C]
  [MonoidalPreadditive C] [MonoidalLinear ℂ C] [IsFusionCategory C]

attribute [local instance] Abelian.hasFiniteBiproducts

/-- A nonzero morphism from a simple object into a semisimple object splits. -/
theorem split_from_simple {S X : C} [Simple S] (f : S ⟶ X) (hf : f ≠ 0) :
    ∃ r : X ⟶ S, f ≫ r = 𝟙 S := by
  classical
  obtain ⟨n, T, hsimple, _, hdecomp⟩ := IsFusionCategory.finite_semisimple (C := C)
  obtain ⟨m, ⟨e⟩⟩ := hdecomp X
  let V : (Σ i, Fin (m i)) → C := fun p => T p.1
  have hg : f ≫ e.hom ≠ 0 := by
    intro h
    apply hf
    have := congrArg (fun t => t ≫ e.inv) h
    simpa using this
  have hcomponent : ∃ p, f ≫ e.hom ≫ biproduct.π V p ≠ 0 := by
    by_contra h
    push Not at h
    apply hg
    apply biproduct.hom_ext
    intro p
    simpa [Category.assoc] using h p
  obtain ⟨p, hp⟩ := hcomponent
  letI : Simple (V p) := hsimple p.1
  let g : S ⟶ V p := f ≫ e.hom ≫ biproduct.π V p
  letI : IsIso g := CategoryTheory.isIso_of_hom_simple hp
  refine ⟨e.hom ≫ biproduct.π V p ≫ inv g, ?_⟩
  simpa only [g, Category.assoc] using IsIso.hom_inv_id g

/-- The tensor unit is a retract of the left dual tensored with any simple
object. This is the split-unit input for identity-strand embeddings. -/
theorem unit_retract_leftDual_tensor (X : C) [Simple X] :
    ∃ (s : 𝟙_ C ⟶ (ᘁX) ⊗ X) (r : (ᘁX) ⊗ X ⟶ 𝟙_ C), s ≫ r = 𝟙 (𝟙_ C) := by
  letI : Simple (𝟙_ C) := IsFusionCategory.unit_simple (C := C)
  have hcoe : ExactPairing.coevaluation (ᘁX) X ≠ 0 := by
    intro h
    have ht := ExactPairing.coevaluation_evaluation (ᘁX) X
    rw [h] at ht
    simp at ht
    have ht' := congrArg (fun t => (ρ_ X).inv ≫ t ≫ (λ_ X).hom) ht
    have hz : 𝟙 X = 0 := by simpa [Category.assoc] using ht'.symm
    exact id_nonzero X hz
  obtain ⟨r, hr⟩ := split_from_simple (ExactPairing.coevaluation (ᘁX) X) hcoe
  exact ⟨_, r, hr⟩

end PropertyF.Ground
