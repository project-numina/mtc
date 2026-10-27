module
public import PropertyF.Ground.Fusion.Simples
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic

/-! All morphisms of the appropriate variance split in a fusion category. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
namespace PropertyF.Ground
universe v u
attribute [local instance] Abelian.hasFiniteBiproducts
variable (D : BraidedFusionCategory.{v,u})

/-- A nonzero morphism into a simple object splits. -/
theorem split_to_simple {S X : D.Obj} [Simple S] (f : X ⟶ S) (hf : f ≠ 0) :
    ∃ s : S ⟶ X, s ≫ f = 𝟙 S := by
  classical
  obtain ⟨m, ⟨e⟩⟩ := simples_decompose D X
  let V : (Σ i, Fin (m i)) → D.Obj := fun p => simples D p.1
  have hg : e.inv ≫ f ≠ 0 := by
    intro h
    apply hf
    have := congrArg (fun t => e.hom ≫ t) h
    simpa using this
  have hc : ∃ p, biproduct.ι V p ≫ e.inv ≫ f ≠ 0 := by
    by_contra h
    push Not at h
    apply hg
    apply biproduct.hom_ext'
    intro p
    simpa [Category.assoc] using h p
  obtain ⟨p, hp⟩ := hc
  letI : Simple (V p) := simples_simple D p.1
  let g : V p ⟶ S := biproduct.ι V p ≫ e.inv ≫ f
  letI : IsIso g := CategoryTheory.isIso_of_hom_simple hp
  refine ⟨inv g ≫ biproduct.ι V p ≫ e.inv, ?_⟩
  simpa only [g, Category.assoc] using IsIso.inv_hom_id g

/-- Every simple object is projective: pull an epimorphism back to the simple
object and split the resulting nonzero map. -/
theorem simple_projective (S : D.Obj) [Simple S] : Projective S where
  factors := by
    intro X Y g f hf
    letI : Epi f := hf
    have hne : (pullback.snd f g : pullback f g ⟶ S) ≠ 0 := by
      intro h
      have hz := IsZero.of_epi_eq_zero (pullback.snd f g) h
      exact id_nonzero S ((IsZero.iff_id_eq_zero S).mp hz)
    obtain ⟨s, hs⟩ := split_to_simple D (pullback.snd f g) hne
    refine ⟨s ≫ pullback.fst f g, ?_⟩
    rw [Category.assoc, pullback.condition, ← Category.assoc, hs, Category.id_comp]

/-- Every simple object is injective, by the dual pushout argument. -/
theorem simple_injective (S : D.Obj) [Simple S] : Injective S where
  factors := by
    intro X Y g f hf
    letI : Mono f := hf
    have hne : (pushout.inr f g : S ⟶ pushout f g) ≠ 0 := by
      intro h
      have hz := IsZero.of_mono_eq_zero (pushout.inr f g) h
      exact id_nonzero S ((IsZero.iff_id_eq_zero S).mp hz)
    obtain ⟨r, hr⟩ := split_from_simple (pushout.inr f g) hne
    refine ⟨pushout.inl f g ≫ r, ?_⟩
    rw [← Category.assoc, pushout.condition, Category.assoc, hr, Category.comp_id]

/-- Every object is projective. -/
theorem object_projective (X : D.Obj) : Projective X := by
  obtain ⟨m, ⟨e⟩⟩ := simples_decompose D X
  let V : (Σ i, Fin (m i)) → D.Obj := fun p => simples D p.1
  letI : ∀ p, Projective (V p) := fun p => by
    letI : Simple (V p) := simples_simple D p.1
    exact simple_projective D (V p)
  have hV : Projective (⨁ V) := by
    refine ⟨?_⟩
    intro A B g f hf
    letI : Epi f := hf
    refine ⟨biproduct.desc (fun p => Projective.factorThru (biproduct.ι V p ≫ g) f), ?_⟩
    apply biproduct.hom_ext'
    intro p
    simp
  exact Projective.of_iso e.symm hV

/-- Every object is injective. -/
theorem object_injective (X : D.Obj) : Injective X := by
  obtain ⟨m, ⟨e⟩⟩ := simples_decompose D X
  let V : (Σ i, Fin (m i)) → D.Obj := fun p => simples D p.1
  letI : ∀ p, Injective (V p) := fun p => by
    letI : Simple (V p) := simples_simple D p.1
    exact simple_injective D (V p)
  exact Injective.of_iso e.symm inferInstance

/-- Every epimorphism splits. -/
theorem epi_splits {X Y : D.Obj} (f : X ⟶ Y) [Epi f] : IsSplitEpi f := by
  letI : Projective Y := object_projective D Y
  obtain ⟨s, hs⟩ := Projective.factors (𝟙 Y) f
  exact IsSplitEpi.mk' { section_ := s, id := hs }

/-- Every monomorphism splits. -/
theorem mono_splits {X Y : D.Obj} (f : X ⟶ Y) [Mono f] : IsSplitMono f := by
  letI : Injective X := object_injective D X
  obtain ⟨r, hr⟩ := Injective.factors (𝟙 X) f
  exact IsSplitMono.mk' { retraction := r, id := hr }

end PropertyF.Ground
