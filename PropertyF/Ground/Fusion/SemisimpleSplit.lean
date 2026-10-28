module
public import PropertyF.Ground.Fusion.Simples
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic

/-! All morphisms of the appropriate variance split in a fusion category. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
namespace PropertyF.Ground
universe v u
attribute [local instance] Abelian.hasFiniteBiproducts

section
variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]

/-- An epimorphism to an object with nonzero identity is nonzero. -/
theorem epi_ne_zero_of_id_ne_zero {X Y : C} (f : X ⟶ Y) [Epi f]
    (h : 𝟙 Y ≠ 0) : f ≠ 0 :=
  fun hf ↦ h ((IsZero.iff_id_eq_zero Y).mp (IsZero.of_epi_eq_zero f hf))


end

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [Abelian C] [Linear ℂ C] [RigidCategory C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [IsFusionCategory C]

/-- A nonzero morphism into a simple object splits. -/
theorem split_to_simple {S X : C} [Simple S] (f : X ⟶ S) (hf : f ≠ 0) :
    ∃ s : S ⟶ X, s ≫ f = 𝟙 S := by
  classical
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
  refine ⟨inv g ≫ biproduct.ι V p ≫ e.inv, ?_⟩
  simpa only [g, Category.assoc] using IsIso.inv_hom_id g

/-- Every simple object is projective: pull an epimorphism back to the simple
object and split the resulting nonzero map. -/
theorem simple_projective (S : C) [Simple S] : Projective S where
  factors := fun {X Y} g f [hf : Epi f] ↦
    (split_to_simple (pullback.snd f g) (epi_ne_zero_of_id_ne_zero _ (id_nonzero S))).elim
      fun s hs ↦ ⟨s ≫ pullback.fst f g, by
        rw [Category.assoc, pullback.condition, ← Category.assoc, hs, Category.id_comp]⟩

/-- Every simple object is injective, by the dual pushout argument. -/
theorem simple_injective (S : C) [Simple S] : Injective S where
  factors := fun {X Y} g f [hf : Mono f] ↦
    (split_from_simple (pushout.inr f g) (mono_ne_zero_of_id_ne_zero _ (id_nonzero S))).elim
      fun r hr ↦ ⟨pushout.inl f g ≫ r, by
        rw [← Category.assoc, pushout.condition, Category.assoc, hr, Category.comp_id]⟩

/-- Every object is projective. -/
theorem object_projective (X : C) : Projective X := by
  obtain ⟨n, T, hsimple, _, hdecomp⟩ := IsFusionCategory.finite_semisimple (C := C)
  obtain ⟨m, ⟨e⟩⟩ := hdecomp X
  let V : (Σ i, Fin (m i)) → C := fun p => T p.1
  let : ∀ p, Projective (V p) := fun p => by
    let : Simple (V p) := hsimple p.1
    exact simple_projective (V p)
  have hV : Projective (⨁ V) := by
    refine ⟨?_⟩
    intro A B g f hf
    let : Epi f := hf
    refine ⟨biproduct.desc (fun p => Projective.factorThru (biproduct.ι V p ≫ g) f), ?_⟩
    exact biproduct.hom_ext' _ _ fun p ↦ by simp
  exact Projective.of_iso e.symm hV

/-- Every object is injective. -/
theorem object_injective (X : C) : Injective X :=
  (IsFusionCategory.finite_semisimple (C := C)).elim fun _ ⟨T, hs, _, hd⟩ ↦
    (hd X).elim fun m ⟨e⟩ ↦
      letI : ∀ p : Σ i, Fin (m i), Injective (T p.1) := fun p ↦
        letI : Simple (T p.1) := hs p.1
        simple_injective (T p.1)
      Injective.of_iso e.symm inferInstance

/-- Every epimorphism splits. -/
theorem epi_splits {X Y : C} (f : X ⟶ Y) [Epi f] : IsSplitEpi f :=
  letI : Projective Y := object_projective Y
  IsSplitEpi.mk' {
    section_ := Projective.factorThru (𝟙 Y) f
    id := Projective.factorThru_comp (𝟙 Y) f }

/-- Every monomorphism splits. -/
theorem mono_splits {X Y : C} (f : X ⟶ Y) [Mono f] : IsSplitMono f :=
  letI : Injective X := object_injective X
  IsSplitMono.mk' {
    retraction := Injective.factorThru (𝟙 X) f
    id := Injective.comp_factorThru (𝟙 X) f }

end PropertyF.Ground
