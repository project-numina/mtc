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
    {X : Fin (n + 2) → C} {Y : C} (f : ∀ j, X j ⟶ Y) (g : ∀ j, Y ⟶ X j)
    (hf : ∀ j, f j ≫ g j = 𝟙 (X j)) (h : pureBraidImage Y n) :
    let ι := coloredBlockInclusion (n + 2) X Y f
    let π := coloredBlockProjection (n + 2) X Y g
    let b := h.val.val.asIso.hom
    ι ≫ b = (ι ≫ b ≫ π) ≫ ι := by
  obtain ⟨l, hw, he⟩ := pureBraidImage_exists_word h
  rw [← he]
  exact pureWord_preserves_coloredBlock n l hw f g hf

/-- Every diagonal component of an actual pure braid is the action of a
colored pure word. This range inclusion lets finiteness arguments work with
any finite family containing those actions. -/
theorem pureBlock_range_subset_coloredWords {n : ℕ}
    {X : Fin (n + 2) → C} {Y : C} (f : ∀ j, X j ⟶ Y) (g : ∀ j, Y ⟶ X j)
    (hf : ∀ j, f j ≫ g j = 𝟙 (X j)) :
    Set.range (fun h : pureBraidImage Y n =>
      coloredBlockInclusion (n + 2) X Y f ≫ h.val.val.asIso.hom ≫
        coloredBlockProjection (n + 2) X Y g) ⊆
      {a | ∃ (w : List (Fin (n + 1) × Bool))
        (hw : strandPermutation n (FreeGroup.mk w) = 1),
          a = coloredPureWordHom n w hw X} := by
  rintro _ ⟨h, rfl⟩
  obtain ⟨l, hw, he⟩ := pureBraidImage_exists_word h
  refine ⟨l, hw, ?_⟩
  dsimp only
  rw [← he, pureWord_coloredBlock_diagonal n l hw f g hf]

/-- A finite family covering the colored pure-word actions gives finite diagonal range. -/
theorem finite_pureBlock_range_of_finite_cover {n : ℕ}
    {X : Fin (n + 2) → C} {Y : C} (f : ∀ j, X j ⟶ Y) (g : ∀ j, Y ⟶ X j)
    (hf : ∀ j, f j ≫ g j = 𝟙 (X j)) {A : Type*} [Finite A]
    (a : A → (coloredTensor (n + 2) X ⟶ coloredTensor (n + 2) X))
    (ha : ∀ (w : List (Fin (n + 1) × Bool))
      (hw : strandPermutation n (FreeGroup.mk w) = 1),
      ∃ z, a z = coloredPureWordHom n w hw X) :
    Set.Finite (Set.range fun h : pureBraidImage Y n =>
      coloredBlockInclusion (n + 2) X Y f ≫ h.val.val.asIso.hom ≫
        coloredBlockProjection (n + 2) X Y g) := by
  apply (Set.finite_range a).subset
  rintro x hx
  obtain ⟨w, hw, rfl⟩ := pureBlock_range_subset_coloredWords f g hf hx
  exact ha w hw

/-- A finite group containing all actual colored pure-word endomorphisms
makes the corresponding diagonal pure-braid block range finite. -/
theorem finite_pureBlock_range_of_colored_group (n : ℕ)
    {X : Fin (n + 2) → C} {Y : C} (f : ∀ j, X j ⟶ Y) (g : ∀ j, Y ⟶ X j)
    (hf : ∀ j, f j ≫ g j = 𝟙 (X j))
    (H : Subgroup (Aut (coloredTensor (n + 2) X))) (hH : Finite H)
    (hcable : ∀ (w : List (Fin (n + 1) × Bool))
      (hw : strandPermutation n (FreeGroup.mk w) = 1),
      ∃ z : H, z.val.asIso.hom = coloredPureWordHom n w hw X) :
    Set.Finite (Set.range fun h : pureBraidImage Y n =>
      coloredBlockInclusion (n + 2) X Y f ≫ h.val.val.asIso.hom ≫
        coloredBlockProjection (n + 2) X Y g) := by
  let : Finite H := hH
  exact finite_pureBlock_range_of_finite_cover f g hf (fun z : H => z.val.asIso.hom) hcable

/-- Explicit cabling into one finite original-strand braid image gives
finite range of an actual pure braid diagonal block. -/
theorem finite_pureBlock_range_of_cabling {n r : ℕ}
    {X : Fin (n + 2) → C} {Y Z : C} (f : ∀ j, X j ⟶ Y) (g : ∀ j, Y ⟶ X j)
    (hf : ∀ j, f j ≫ g j = 𝟙 (X j)) (e : coloredTensor (n + 2) X ≅ tensorPower Z (r + 2))
    (hfinite : Finite (braidImage Z r))
    (hcable : ∀ (w : List (Fin (n + 1) × Bool))
      (hw : strandPermutation n (FreeGroup.mk w) = 1),
      ∃ z : braidImage Z r, coloredPureWordHom n w hw X =
        e.hom ≫ z.val.asIso.hom ≫ e.inv) :
    Set.Finite (Set.range fun h : pureBraidImage Y n =>
      coloredBlockInclusion (n + 2) X Y f ≫ h.val.val.asIso.hom ≫
        coloredBlockProjection (n + 2) X Y g) := by
  let : Finite (braidImage Z r) := hfinite
  apply finite_pureBlock_range_of_finite_cover f g hf
    (fun z : braidImage Z r => e.hom ≫ z.val.asIso.hom ≫ e.inv)
  intro w hw
  obtain ⟨z, hz⟩ := hcable w hw
  exact ⟨z, hz.symm⟩

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
  apply finite_pureBlock_range_of_finite_cover f g hf (fun _ : Unit => 𝟙 _)
  intro w hw
  exact ⟨(), (htrivial w hw).symm⟩

end MTC.Braided.Cabling
end
