module
public import PropertyF.Ground.Fusion.FunctorDimension
/-! FP dimension preservation for functors between independently sized categories. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open CategoryTheory.Functor.Monoidal
open scoped BigOperators
namespace PropertyF.Ground
universe v u v' u'
attribute [local instance] Abelian.hasFiniteBiproducts

/-- Applying an additive functor to a canonical decomposition expresses the
FP dimension of the image as the sum of the dimensions of image simples,
with independent category universes. -/
theorem fpDimension_functor_decomposition_universe (C : BraidedFusionCategory.{v,u})
    (D : BraidedFusionCategory.{v',u'})
    (F : C.Obj ⥤ D.Obj) [F.Additive] (X : C.Obj) :
    fpDimension D (F.obj X) = ∑ i,
      (Module.finrank ℂ (simples C i ⟶ X) : ℝ) * fpDimension D (F.obj (simples C i)) := by
  classical
  let m : Fin (rank C) → ℕ := fun i => Module.finrank ℂ (simples C i ⟶ X)
  let V : (Σ i, Fin (m i)) → C.Obj := fun p => simples C p.1
  obtain ⟨e⟩ := exists_canonical_decomposition C X
  let e' : F.obj X ≅ ⨁ (fun p => F.obj (V p)) := F.mapIso e ≪≫ F.mapBiproduct V
  rw [fpDimension_iso D e', fpDimension_biproduct, Fintype.sum_sigma]
  simp [V, m]

/-- An additive faithful strong monoidal functor preserves FP dimension,
without requiring the source and target to have the same universes. -/
theorem fpDimension_functor_universe (C : BraidedFusionCategory.{v,u})
    (D : BraidedFusionCategory.{v',u'})
    (F : C.Obj ⥤ D.Obj) [F.Additive] [F.Faithful] [F.Monoidal] (X : C.Obj) :
    fpDimension D (F.obj X) = fpDimension C X := by
  classical
  let f : Fin (rank C) → ℝ := fun i => fpDimension D (F.obj (simples C i))
  have hpos : ∀ i, 0 < f i := by
    intro i
    apply lt_of_lt_of_le zero_lt_one
    apply one_le_fpDimension
    intro hz
    have hid : (𝟙 (simples C i) : simples C i ⟶ simples C i) = 0 := by
      apply F.map_injective
      simpa using ((IsZero.iff_id_eq_zero _).mp hz)
    letI : Simple (simples C i) := simples_simple C i
    exact id_nonzero _ hid
  have hunit : f (unitIndex C) = 1 := by
    obtain ⟨e⟩ := unitIndex_iso C
    rw [show f (unitIndex C) = fpDimension D (𝟙_ D.Obj) from
      fpDimension_iso D (F.mapIso e ≪≫ (εIso F).symm), fpDimension_unit]
  have hmul : ∀ i j, f i * f j = ∑ k, (fusionCoeff C i j k : ℝ) * f k := by
    intro i j
    calc
      _ = fpDimension D (F.obj (simples C i) ⊗ F.obj (simples C j)) :=
        (fpDimension_tensor D _ _).symm
      _ = fpDimension D (F.obj (simples C i ⊗ simples C j)) :=
        fpDimension_iso D (μIso F _ _)
      _ = _ := fpDimension_functor_decomposition_universe C D F _
  have heq : f = fpSimple C := positive_character_unique C f (fpSimple C)
    hpos (fpSimple_pos C) hunit (fpSimple_unit C) hmul (fpSimple_mul C)
  rw [fpDimension_functor_decomposition_universe]
  change (∑ i, (Module.finrank ℂ (simples C i ⟶ X) : ℝ) * f i) = _
  rw [heq]
  rfl

end PropertyF.Ground
