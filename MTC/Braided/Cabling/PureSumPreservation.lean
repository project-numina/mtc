module
public import MTC.Braided.Cabling.PureSum
public import MTC.Braided.Cabling.PureSumColored

/-! Actual pure braid images preserve each colored retract block. -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.BraidedCategory
namespace MTC.Braided.Cabling
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]

/-- Every element of the actual pure braid image preserves a colored block. -/
theorem pureBraidImage_preserves_coloredBlock (n : ℕ)
    (X : Fin (n + 2) → C) (Y : C) (f : ∀ j, X j ⟶ Y) (g : ∀ j, Y ⟶ X j)
    (hf : ∀ j, f j ≫ g j = 𝟙 (X j)) (h : pureBraidImage Y n) :
    let ι := coloredBlockInclusion (n + 2) X Y f
    let π := coloredBlockProjection (n + 2) X Y g
    let b := h.val.val.asIso.hom
    ι ≫ b = (ι ≫ b ≫ π) ≫ ι := by
  obtain ⟨w, hw, he⟩ := h.property
  obtain ⟨l, hl⟩ := Quot.exists_rep w
  change FreeGroup.mk l = w at hl
  subst w
  change strandPermutation n (FreeGroup.mk l) = 1 at hw
  rw [← he]
  exact pureWord_preserves_coloredBlock n l hw X Y f g hf

/-- A finite group containing all actual colored pure-word endomorphisms
makes the corresponding diagonal pure-braid block range finite. -/
theorem finite_pureBlock_range_of_colored_group (n : ℕ)
    (X : Fin (n + 2) → C) (Y : C) (f : ∀ j, X j ⟶ Y) (g : ∀ j, Y ⟶ X j)
    (hf : ∀ j, f j ≫ g j = 𝟙 (X j))
    (H : Subgroup (Aut (coloredTensor (n + 2) X))) (hH : Finite H)
    (hcable : ∀ (w : List (Fin (n + 1) × Bool))
      (hw : strandPermutation n (FreeGroup.mk w) = 1),
      ∃ z : H, z.val.asIso.hom = coloredPureWordHom n w hw X) :
    Set.Finite (Set.range fun h : pureBraidImage Y n =>
      coloredBlockInclusion (n + 2) X Y f ≫ h.val.val.asIso.hom ≫
        coloredBlockProjection (n + 2) X Y g) := by
  classical
  letI : Finite H := hH
  apply (Set.finite_range (fun z : H => z.val.asIso.hom)).subset
  rintro _ ⟨h, rfl⟩
  obtain ⟨w, hw, he⟩ := h.property
  obtain ⟨l, hl⟩ := Quot.exists_rep w
  change FreeGroup.mk l = w at hl
  subst w
  change strandPermutation n (FreeGroup.mk l) = 1 at hw
  obtain ⟨z, hz⟩ := hcable l hw
  refine ⟨z, ?_⟩
  dsimp only
  rw [hz, ← he]
  exact (pureWord_coloredBlock_diagonal n l hw X Y f g hf).symm

/-- Explicit cabling into one finite original-strand braid image gives
finite range of an actual pure braid diagonal block. -/
theorem finite_pureBlock_range_of_cabling (n r : ℕ)
    (X : Fin (n + 2) → C) (Y Z : C) (f : ∀ j, X j ⟶ Y) (g : ∀ j, Y ⟶ X j)
    (hf : ∀ j, f j ≫ g j = 𝟙 (X j)) (e : coloredTensor (n + 2) X ≅ tensorPower Z (r + 2))
    (hfinite : Finite (braidImage Z r))
    (hcable : ∀ (w : List (Fin (n + 1) × Bool))
      (hw : strandPermutation n (FreeGroup.mk w) = 1),
      ∃ z : braidImage Z r, coloredPureWordHom n w hw X =
        e.hom ≫ z.val.asIso.hom ≫ e.inv) :
    Set.Finite (Set.range fun h : pureBraidImage Y n =>
      coloredBlockInclusion (n + 2) X Y f ≫ h.val.val.asIso.hom ≫
        coloredBlockProjection (n + 2) X Y g) := by
  classical
  letI : Finite (braidImage Z r) := hfinite
  apply (Set.finite_range (fun z : braidImage Z r => e.hom ≫ z.val.asIso.hom ≫ e.inv)).subset
  rintro _ ⟨h, rfl⟩
  obtain ⟨w, hw, he⟩ := h.property
  obtain ⟨l, hl⟩ := Quot.exists_rep w
  change FreeGroup.mk l = w at hl
  subst w
  change strandPermutation n (FreeGroup.mk l) = 1 at hw
  obtain ⟨z, hz⟩ := hcable l hw
  refine ⟨z, ?_⟩
  dsimp only
  rw [← he, pureWord_coloredBlock_diagonal n l hw X Y f g hf, hz]

/-- If every actual colored pure word is the identity, the corresponding
pure braid diagonal range is contained in the singleton identity. -/
theorem finite_pureBlock_range_of_colored_trivial (n : ℕ)
    (X : Fin (n + 2) → C) (Y : C) (f : ∀ j, X j ⟶ Y) (g : ∀ j, Y ⟶ X j)
    (hf : ∀ j, f j ≫ g j = 𝟙 (X j))
    (htrivial : ∀ (w : List (Fin (n + 1) × Bool))
      (hw : strandPermutation n (FreeGroup.mk w) = 1),
      coloredPureWordHom n w hw X = 𝟙 _) :
    Set.Finite (Set.range fun h : pureBraidImage Y n =>
      coloredBlockInclusion (n + 2) X Y f ≫ h.val.val.asIso.hom ≫
        coloredBlockProjection (n + 2) X Y g) := by
  classical
  apply (Set.finite_singleton (𝟙 (coloredTensor (n + 2) X))).subset
  rintro _ ⟨h, rfl⟩
  obtain ⟨w, hw, he⟩ := h.property
  obtain ⟨l, hl⟩ := Quot.exists_rep w
  change FreeGroup.mk l = w at hl
  subst w
  change strandPermutation n (FreeGroup.mk l) = 1 at hw
  simp only [Set.mem_singleton_iff]
  rw [← he, pureWord_coloredBlock_diagonal n l hw X Y f g hf, htrivial]

end MTC.Braided.Cabling
end
