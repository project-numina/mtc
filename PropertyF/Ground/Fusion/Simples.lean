module
public import PropertyF.Ground.Target
public import Mathlib.CategoryTheory.Preadditive.Schur
public import Mathlib.Analysis.Complex.Polynomial.Basic

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
  let : Simple (V p) := hsimple p.1
  let g : S ⟶ V p := f ≫ e.hom ≫ biproduct.π V p
  let : IsIso g := CategoryTheory.isIso_of_hom_simple hp
  refine ⟨e.hom ≫ biproduct.π V p ≫ inv g, ?_⟩
  simpa only [g, Category.assoc] using IsIso.hom_inv_id g

/-- The tensor unit is a retract of the left dual tensored with any simple
object. This is the split-unit input for identity-strand embeddings. -/
theorem unit_retract_leftDual_tensor (X : C) [Simple X] :
    ∃ (s : 𝟙_ C ⟶ (ᘁX) ⊗ X) (r : (ᘁX) ⊗ X ⟶ 𝟙_ C), s ≫ r = 𝟙 (𝟙_ C) := by
  let : Simple (𝟙_ C) := IsFusionCategory.unit_simple (C := C)
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

end

/-! Simple representatives chosen by the ground category interface. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits

namespace PropertyF.Ground
universe v u
attribute [local instance] Abelian.hasFiniteBiproducts
variable (C : BraidedFusionCategory.{v,u})

theorem simples_simple (i : Fin (rank C)) : Simple (simples C i) :=
  (Classical.choose_spec (Classical.choose_spec
    (IsFusionCategory.finite_semisimple (C := C.Obj)))).1 i

theorem simples_injective (i j : Fin (rank C))
    (h : Nonempty (simples C i ≅ simples C j)) : i = j :=
  (Classical.choose_spec (Classical.choose_spec
    (IsFusionCategory.finite_semisimple (C := C.Obj)))).2.1 i j h

theorem simples_decompose (X : C.Obj) : ∃ m : Fin (rank C) → ℕ,
    Nonempty (X ≅ ⨁ (fun p : Σ i, Fin (m i) => simples C p.1)) :=
  (Classical.choose_spec (Classical.choose_spec
    (IsFusionCategory.finite_semisimple (C := C.Obj)))).2.2 X

/-- Every simple object is isomorphic to one of the chosen representatives. -/
theorem exists_simple_iso (X : C.Obj) [Simple X] :
    ∃ i : Fin (rank C), Nonempty (X ≅ simples C i) := by
  classical
  obtain ⟨m, ⟨e⟩⟩ := simples_decompose C X
  let V : (Σ i, Fin (m i)) → C.Obj := fun p => simples C p.1
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
  let : Simple (V p) := simples_simple C p.1
  let : IsIso (e.hom ≫ biproduct.π V p) := CategoryTheory.isIso_of_hom_simple hp
  exact ⟨p.1, ⟨asIso (e.hom ≫ biproduct.π V p)⟩⟩

/-- The tensor unit occurs among the representatives. -/
theorem exists_unit_iso : ∃ i : Fin (rank C), Nonempty (simples C i ≅ 𝟙_ C.Obj) := by
  let : Simple (𝟙_ C.Obj) := IsFusionCategory.unit_simple
  obtain ⟨i, ⟨e⟩⟩ := exists_simple_iso C (𝟙_ C.Obj)
  exact ⟨i, ⟨e.symm⟩⟩

/-- Hom spaces between the chosen simples have the expected multiplicities. -/
theorem finrank_simples_hom (i j : Fin (rank C)) :
    Module.finrank ℂ (simples C i ⟶ simples C j) = if i = j then 1 else 0 := by
  classical
  let : Simple (simples C i) := simples_simple C i
  let : Simple (simples C j) := simples_simple C j
  let : ∀ X Y : C.Obj, FiniteDimensional ℂ (X ⟶ Y) := IsFusionCategory.hom_finite
  rw [CategoryTheory.finrank_hom_simple_simple ℂ]
  congr 1
  exact propext ⟨simples_injective C i j, fun h => by subst j; exact ⟨Iso.refl _⟩⟩

end PropertyF.Ground

end
