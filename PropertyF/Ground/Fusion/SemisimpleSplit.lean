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

variable (D : BraidedFusionCategory.{v,u})

/-- A nonzero morphism into a simple object splits. -/
theorem split_to_simple {S X : D.Obj} [Simple S] (f : X ⟶ S) (hf : f ≠ 0) :
    ∃ s : S ⟶ X, s ≫ f = 𝟙 S := by
  classical
  obtain ⟨m, ⟨e⟩⟩ := simples_decompose D X
  let V : (Σ i, Fin (m i)) → D.Obj := fun p => simples D p.1
  have hg : e.inv ≫ f ≠ 0 := fun h ↦ hf ((cancel_epi e.inv).1 (by simpa using h))
  have hc : ∃ p, biproduct.ι V p ≫ e.inv ≫ f ≠ 0 := by
    by_contra h
    push Not at h
    apply hg
    apply biproduct.hom_ext'
    intro p
    simpa [Category.assoc] using h p
  obtain ⟨p, hp⟩ := hc
  let : Simple (V p) := simples_simple D p.1
  let g : V p ⟶ S := biproduct.ι V p ≫ e.inv ≫ f
  let : IsIso g := CategoryTheory.isIso_of_hom_simple hp
  refine ⟨inv g ≫ biproduct.ι V p ≫ e.inv, ?_⟩
  simpa only [g, Category.assoc] using IsIso.inv_hom_id g

/-- Every simple object is projective: pull an epimorphism back to the simple
object and split the resulting nonzero map. -/
theorem simple_projective (S : D.Obj) [Simple S] : Projective S where
  factors := by
    intro X Y g f hf
    let : Epi f := hf
    obtain ⟨s, hs⟩ := split_to_simple D (pullback.snd f g)
      (epi_ne_zero_of_id_ne_zero _ (id_nonzero S))
    refine ⟨s ≫ pullback.fst f g, ?_⟩
    rw [Category.assoc, pullback.condition, ← Category.assoc, hs, Category.id_comp]

/-- Every simple object is injective, by the dual pushout argument. -/
theorem simple_injective (S : D.Obj) [Simple S] : Injective S where
  factors := by
    intro X Y g f hf
    let : Mono f := hf
    obtain ⟨r, hr⟩ := split_from_simple (pushout.inr f g)
      (mono_ne_zero_of_id_ne_zero _ (id_nonzero S))
    refine ⟨pushout.inl f g ≫ r, ?_⟩
    rw [← Category.assoc, pushout.condition, Category.assoc, hr, Category.comp_id]

/-- Every object is projective. -/
theorem object_projective (X : D.Obj) : Projective X := by
  obtain ⟨m, ⟨e⟩⟩ := simples_decompose D X
  let V : (Σ i, Fin (m i)) → D.Obj := fun p => simples D p.1
  let : ∀ p, Projective (V p) := fun p => by
    let : Simple (V p) := simples_simple D p.1
    exact simple_projective D (V p)
  have hV : Projective (⨁ V) := by
    refine ⟨?_⟩
    intro A B g f hf
    let : Epi f := hf
    refine ⟨biproduct.desc (fun p => Projective.factorThru (biproduct.ι V p ≫ g) f), ?_⟩
    apply biproduct.hom_ext'
    intro p
    simp
  exact Projective.of_iso e.symm hV

/-- Every object is injective. -/
theorem object_injective (X : D.Obj) : Injective X := by
  obtain ⟨m, ⟨e⟩⟩ := simples_decompose D X
  let V : (Σ i, Fin (m i)) → D.Obj := fun p => simples D p.1
  let : ∀ p, Injective (V p) := fun p => by
    let : Simple (V p) := simples_simple D p.1
    exact simple_injective D (V p)
  exact Injective.of_iso e.symm inferInstance

/-- Every epimorphism splits. -/
theorem epi_splits {X Y : D.Obj} (f : X ⟶ Y) [Epi f] : IsSplitEpi f := by
  let : Projective Y := object_projective D Y
  obtain ⟨s, hs⟩ := Projective.factors (𝟙 Y) f
  exact IsSplitEpi.mk' { section_ := s, id := hs }

/-- Every monomorphism splits. -/
theorem mono_splits {X Y : D.Obj} (f : X ⟶ Y) [Mono f] : IsSplitMono f := by
  let : Injective X := object_injective D X
  obtain ⟨r, hr⟩ := Injective.factors (𝟙 X) f
  exact IsSplitMono.mk' { retraction := r, id := hr }

end PropertyF.Ground
