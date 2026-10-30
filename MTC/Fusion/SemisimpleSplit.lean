module
public import MTC.Fusion.Simples
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic

open MTC.Fusion

open MTC.Braided

/-! # Splittings in fusion categories

Nonzero maps to a simple object split. Finite semisimple decompositions then
show that simples and their finite sums are injective, so every monomorphism
in a fusion category is split.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
namespace MTC
universe v u
attribute [local instance] Abelian.hasFiniteBiproducts

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [Abelian C] [Linear ℂ C] [RigidCategory C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [IsFusionCategory C]

/-- A nonzero morphism into a simple object splits. -/
theorem split_to_simple {S X : C} [Simple S] (f : X ⟶ S) (hf : f ≠ 0) :
    ∃ s : S ⟶ X, s ≫ f = 𝟙 S := by
  obtain ⟨n, T, hsimple, _, hdecomp⟩ := IsFusionCategory.finite_semisimple (C := C)
  obtain ⟨m, ⟨e⟩⟩ := hdecomp X
  let V : (Σ i, Fin (m i)) → C := fun p => T p.1
  obtain ⟨p, hp⟩ : ∃ p, biproduct.ι V p ≫ e.inv ≫ f ≠ 0 := by
    by_contra! h
    exact hf ((cancel_epi e.inv).1 (by simpa only [comp_zero] using
      (biproduct.hom_ext' _ _ fun p ↦ by simpa only [comp_zero, Category.assoc] using h p)))
  let : Simple (V p) := hsimple p.1
  let g : V p ⟶ S := biproduct.ι V p ≫ e.inv ≫ f
  let : IsIso g := CategoryTheory.isIso_of_hom_simple hp
  exact ⟨inv g ≫ biproduct.ι V p ≫ e.inv, by simpa only [g, Category.assoc] using IsIso.inv_hom_id g⟩

/-- Every simple object is injective, by the dual pushout argument. -/
theorem simple_injective (S : C) [Simple S] : Injective S where
  factors := fun {X Y} g f [hf : Mono f] ↦ (split_from_simple (pushout.inr f g)
    (mono_ne_zero_of_id_ne_zero _ (id_nonzero S))).elim fun r hr ↦
      ⟨pushout.inl f g ≫ r, by simpa [hr] using congrArg (· ≫ r) (pushout.condition (f := f))⟩

/-- Every object is injective. -/
theorem object_injective (X : C) : Injective X :=
  (IsFusionCategory.finite_semisimple (C := C)).elim fun _ ⟨T, hs, _, hd⟩ ↦
    (hd X).elim fun m ⟨e⟩ ↦
      letI : ∀ p : Σ i, Fin (m i), Injective (T p.1) := fun p ↦
        letI : Simple (T p.1) := hs p.1
        simple_injective (T p.1)
      Injective.of_iso e.symm inferInstance

/-- Every monomorphism splits. -/
theorem mono_splits {X Y : C} (f : X ⟶ Y) [Mono f] : IsSplitMono f :=
  letI : Injective X := object_injective X
  IsSplitMono.mk' ⟨Injective.factorThru (𝟙 X) f, Injective.comp_factorThru (𝟙 X) f⟩

end MTC
