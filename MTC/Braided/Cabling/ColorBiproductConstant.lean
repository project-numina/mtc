module
public import MTC.Braided.Cabling.ColorBiproductFinite
public import MTC.PropertyF.Pivotal.SymmetricPropertyF

/-! # Homogeneous colored blocks of pure braid actions -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open scoped BigOperators
namespace MTC.Braided.Cabling
universe v u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {C : Type u} [Category.{v} C] [Preadditive C] [MonoidalCategory C]
  [MonoidalPreadditive C] [HasFiniteBiproducts C] [BraidedCategory C]

/-- A homogeneous colored pure word is the actual pure braid action on the
homogeneous tensor power, conjugated by the canonical comparison. -/
theorem coloredPureWordHom_constant (n : ℕ)
    (w : List (Fin (n + 1) × Bool)) (hw : strandPermutation n (FreeGroup.mk w) = 1)
    (X : C) : coloredPureWordHom n w hw (fun _ => X) =
      (coloredConstantIso X (n + 2)).hom ≫
        ((braidWordAction X n (FreeGroup.mk w)).val).asIso.hom ≫
          (coloredConstantIso X (n + 2)).inv := by
  have h := pureWord_coloredBlock_diagonal n w hw
    (fun _ => 𝟙 X) (fun _ => 𝟙 X) (fun _ => Category.id_comp _)
  simpa [coloredBlockInclusion, coloredBlockProjection, coloredTensorMap_id] using h.symm

/-- A homogeneous colored retract block has finite pure-braid diagonal range
whenever its common object has property F. -/
theorem finite_pureBlock_range_of_constant (n : ℕ) (X Y : C)
    (f : ∀ _ : Fin (n + 2), X ⟶ Y) (g : ∀ _ : Fin (n + 2), Y ⟶ X)
    (hf : ∀ j, f j ≫ g j = 𝟙 X) (hX : ObjectPropertyF X) :
    Set.Finite (Set.range fun h : pureBraidImage Y n =>
      coloredBlockInclusion (n + 2) (fun _ => X) Y f ≫ h.val.val.asIso.hom ≫
        coloredBlockProjection (n + 2) (fun _ => X) Y g) := by
  apply finite_pureBlock_range_of_cabling f g hf
    (coloredConstantIso X (n + 2)) (hX n)
  intro w hw
  exact ⟨braidWordAction X n (FreeGroup.mk w), coloredPureWordHom_constant n w hw X⟩

/-- A colored block all of whose objects equal one property-F object has
finite pure-braid diagonal range. -/
theorem finite_pureBlock_range_of_equal_colors {n : ℕ} {X : Fin (n + 2) → C} {T Y : C}
    (hconst : ∀ j, X j = T) (f : ∀ j, X j ⟶ Y) (g : ∀ j, Y ⟶ X j)
    (hf : ∀ j, f j ≫ g j = 𝟙 (X j)) (hT : ObjectPropertyF T) :
    Set.Finite (Set.range fun h : pureBraidImage Y n =>
      coloredBlockInclusion (n + 2) X Y f ≫ h.val.val.asIso.hom ≫
        coloredBlockProjection (n + 2) X Y g) := by
  have heq : X = fun _ => T := funext hconst
  subst X
  exact finite_pureBlock_range_of_constant n T Y f g hf hT

/-- A coloring whose summands all equal one property-F object has finite
pure-braid diagonal range. -/
theorem finite_pureColor_range_of_equal_colors
    {I : Type} [Fintype I] [DecidableEq I] (V : I → C)
    (n : ℕ) (f : Fin (n + 2) → I) {T : C}
    (hconst : ∀ j, V (f j) = T) (hT : ObjectPropertyF T) :
    Set.Finite (Set.range fun h : pureBraidImage (⨁ V) n =>
      colorInclusion V (n + 2) f ≫ h.val.val.asIso.hom ≫ colorProjection V (n + 2) f) := by
  have h := finite_pureBlock_range_of_equal_colors hconst (fun j => biproduct.ι V (f j)) (fun j => biproduct.π V (f j))
    (fun j => biproduct.ι_π_self V (f j)) hT
  simpa only [← colorInclusion_eq_coloredBlockInclusion,
    ← colorProjection_eq_coloredBlockProjection] using h

/-- The tensor unit has property F in every braided monoidal category. -/
theorem tensorUnit_objectPropertyF : ObjectPropertyF (𝟙_ C) := by
  apply MTC.PropertyF.Pivotal.objectPropertyF_of_selfTransparent
  simp [MTC.Center.Trace.SelfTransparent]
  monoidal

/-- If every selected color is the tensor unit, its pure-braid diagonal range
is finite. This covers the zero-original-strand case. -/
theorem finite_pureColor_range_of_unit_colors
    {I : Type} [Fintype I] [DecidableEq I] (V : I → C)
    (n : ℕ) (f : Fin (n + 2) → I) (hconst : ∀ j, V (f j) = 𝟙_ C) :
    Set.Finite (Set.range fun h : pureBraidImage (⨁ V) n =>
      colorInclusion V (n + 2) f ≫ h.val.val.asIso.hom ≫ colorProjection V (n + 2) f) :=
  finite_pureColor_range_of_equal_colors V n f hconst tensorUnit_objectPropertyF

/-- For a coloring of tensor powers with zero total original strands, the
actual pure-braid diagonal range is finite. -/
theorem finite_pureColor_range_of_zero_total
    {I : Type} [Fintype I] [DecidableEq I] (X : C) (k : I → ℕ)
    (n : ℕ) (f : Fin (n + 2) → I) (hzero : ∑ j, k (f j) = 0) :
    Set.Finite (Set.range fun h : pureBraidImage (⨁ (fun i => tensorPower X (k i))) n =>
      colorInclusion (fun i => tensorPower X (k i)) (n + 2) f ≫ h.val.val.asIso.hom ≫
        colorProjection (fun i => tensorPower X (k i)) (n + 2) f) := by
  apply finite_pureColor_range_of_unit_colors (fun i => tensorPower X (k i)) n f
  intro j
  have hj : k (f j) = 0 := (Finset.sum_eq_zero_iff.mp hzero) j (Finset.mem_univ j)
  simp [hj, tensorPower]

end MTC.Braided.Cabling
end
