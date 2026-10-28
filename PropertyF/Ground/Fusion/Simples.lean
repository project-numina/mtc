module
public import PropertyF.Ground.Target
public import Mathlib.CategoryTheory.Preadditive.Schur
public import Mathlib.Analysis.Complex.Polynomial.Basic

/-! Splitting maps from simples in a finite semisimple category. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits

namespace PropertyF.Ground
universe v u

/-- A monomorphism from an object with nonzero identity is nonzero. -/
theorem mono_ne_zero_of_id_ne_zero {C : Type u} [Category.{v} C] [HasZeroMorphisms C] {X Y : C}
    (f : X ⟶ Y) [Mono f]
    (h : 𝟙 X ≠ 0) : f ≠ 0 :=
  fun hf ↦ h ((IsZero.iff_id_eq_zero X).mp (IsZero.of_mono_eq_zero f hf))

/-- The evaluation and coevaluation of a dual pair are nonzero when the right object is nonzero. -/
theorem exactPairing_ne_zero {C : Type u} [Category.{v} C] [MonoidalCategory C]
    [Preadditive C] [MonoidalPreadditive C] (X Y : C) [ExactPairing X Y]
    (hY : 𝟙 Y ≠ 0) : ExactPairing.coevaluation X Y ≠ 0 ∧
      ExactPairing.evaluation X Y ≠ 0 := by
  constructor <;> intro h <;> apply hY <;>
    simpa [h, Category.assoc] using congrArg (fun t ↦ (ρ_ Y).inv ≫ t ≫ (λ_ Y).hom)
      (ExactPairing.coevaluation_evaluation X Y).symm

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
  obtain ⟨p, hp⟩ : ∃ p, f ≫ e.hom ≫ biproduct.π V p ≠ 0 := by
    by_contra! h
    exact hf ((cancel_mono e.hom).1 (by simpa only [zero_comp] using
      (biproduct.hom_ext _ _ fun p ↦ by simpa only [zero_comp, Category.assoc] using h p)))
  let : Simple (V p) := hsimple p.1
  let g : S ⟶ V p := f ≫ e.hom ≫ biproduct.π V p
  let : IsIso g := CategoryTheory.isIso_of_hom_simple hp
  refine ⟨e.hom ≫ biproduct.π V p ≫ inv g, ?_⟩
  simpa only [g, Category.assoc] using IsIso.hom_inv_id g

/-- The tensor unit is a retract of the left dual tensored with any simple
object. This is the split-unit input for identity-strand embeddings. -/
theorem unit_retract_leftDual_tensor (X : C) [Simple X] :
    ∃ (s : 𝟙_ C ⟶ (ᘁX) ⊗ X) (r : (ᘁX) ⊗ X ⟶ 𝟙_ C), s ≫ r = 𝟙 (𝟙_ C) :=
  letI : Simple (𝟙_ C) := IsFusionCategory.unit_simple (C := C)
  ⟨_, split_from_simple (ExactPairing.coevaluation (ᘁX) X)
    (exactPairing_ne_zero (ᘁX) X (id_nonzero X)).1⟩

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

local instance (i : Fin (rank C)) : Simple (simples C i) := simples_simple C i

theorem simples_injective {i j : Fin (rank C)}
    (h : Nonempty (simples C i ≅ simples C j)) : i = j :=
  (Classical.choose_spec (Classical.choose_spec
    (IsFusionCategory.finite_semisimple (C := C.Obj)))).2.1 i j h

theorem simples_decompose (X : C.Obj) : ∃ m : Fin (rank C) → ℕ,
    Nonempty (X ≅ ⨁ (fun p : Σ i, Fin (m i) => simples C p.1)) :=
  (Classical.choose_spec (Classical.choose_spec
    (IsFusionCategory.finite_semisimple (C := C.Obj)))).2.2 X

/-- Every object with nonzero identity has a chosen simple retract. -/
theorem exists_simple_retract {X : C.Obj} (hX : 𝟙 X ≠ 0) :
    ∃ (i : Fin (rank C)) (s : X ⟶ simples C i) (t : simples C i ⟶ X),
      s ≠ 0 ∧ t ≫ s = 𝟙 (simples C i) := by
  classical
  obtain ⟨m, ⟨e⟩⟩ := simples_decompose C X
  let V : (Σ i, Fin (m i)) → C.Obj := fun p => simples C p.1
  obtain ⟨p, hp⟩ : ∃ p, e.hom ≫ biproduct.π V p ≠ 0 := by
    by_contra! h
    exact mono_ne_zero_of_id_ne_zero e.hom hX
      (biproduct.hom_ext _ _ fun p ↦ by simpa only [zero_comp] using h p)
  refine ⟨p.1, e.hom ≫ biproduct.π V p, biproduct.ι V p ≫ e.inv, hp, ?_⟩
  simp [V, Category.assoc]

/-- Every simple object is isomorphic to one of the chosen representatives. -/
theorem exists_simple_iso (X : C.Obj) [Simple X] :
    ∃ i : Fin (rank C), Nonempty (X ≅ simples C i) :=
  (exists_simple_retract C (id_nonzero X)).imp fun _i ⟨s, _, hs, _⟩ ↦
    letI : IsIso s := CategoryTheory.isIso_of_hom_simple hs
    ⟨asIso s⟩

/-- The tensor unit occurs among the representatives. -/
theorem exists_unit_iso : ∃ i : Fin (rank C), Nonempty (simples C i ≅ 𝟙_ C.Obj) :=
  letI : Simple (𝟙_ C.Obj) := IsFusionCategory.unit_simple
  (exists_simple_iso C (𝟙_ C.Obj)).imp fun _ h => h.map Iso.symm

/-- Hom spaces between the chosen simples have the expected multiplicities. -/
theorem finrank_simples_hom (i j : Fin (rank C)) :
    Module.finrank ℂ (simples C i ⟶ simples C j) = if i = j then 1 else 0 := by
  classical
  let : ∀ X Y : C.Obj, FiniteDimensional ℂ (X ⟶ Y) := IsFusionCategory.hom_finite
  simp only [CategoryTheory.finrank_hom_simple_simple ℂ,
    show Nonempty (simples C i ≅ simples C j) ↔ i = j from
      ⟨simples_injective C, fun h ↦ by subst j; exact ⟨Iso.refl _⟩⟩]

end PropertyF.Ground

end
