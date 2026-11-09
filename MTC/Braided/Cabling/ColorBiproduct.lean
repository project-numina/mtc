module
public import MTC.Braided.Cabling.PureSumColored
public import MTC.Braided.Cabling.Generated

/-! # Colored tensor components of tensor powers of finite biproducts -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open scoped BigOperators
namespace MTC.Braided.Cabling
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe v u
variable {C : Type u} [Category.{v} C] [Preadditive C] [MonoidalCategory C]
  [MonoidalPreadditive C] [HasFiniteBiproducts C] [BraidedCategory C]
variable {I : Type} [Fintype I] [DecidableEq I] (V : I → C)

/-- The actual inclusion of a colored tensor component. -/
def colorInclusion : ∀ n : ℕ, (f : Fin n → I) →
    coloredTensor n (fun j => V (f j)) ⟶ tensorPower (⨁ V) n
  | 0, _ => 𝟙 _
  | n + 1, f => biproduct.ι V (f 0) ⊗ₘ colorInclusion n (fun j => f j.succ)

/-- The actual projection onto a colored tensor component. -/
def colorProjection : ∀ n : ℕ, (f : Fin n → I) →
    tensorPower (⨁ V) n ⟶ coloredTensor n (fun j => V (f j))
  | 0, _ => 𝟙 _
  | n + 1, f => biproduct.π V (f 0) ⊗ₘ colorProjection n (fun j => f j.succ)

/-- Each recursive inclusion is the independent-strand tensor map followed
by the canonical homogeneous tensor-power comparison. -/
theorem colorInclusion_eq_coloredTensorMap : ∀ {n : ℕ} (f : Fin n → I),
    colorInclusion V n f = coloredTensorMap n (fun j => biproduct.ι V (f j)) ≫
      (coloredConstantIso (⨁ V) n).hom
  | 0, _ => by simp [colorInclusion, coloredTensorMap, coloredConstantIso]
  | n + 1, f => by
    rw [colorInclusion, coloredTensorMap, coloredConstantIso]
    simp only [tensorIso_hom, Iso.refl_hom, tensorHom_comp_tensorHom, Category.comp_id]
    rw [← colorInclusion_eq_coloredTensorMap (fun j => f j.succ)]

/-- Each recursive projection is the homogeneous comparison followed by the
independent-strand tensor map of biproduct projections. -/
theorem colorProjection_eq_coloredTensorMap : ∀ {n : ℕ} (f : Fin n → I),
    colorProjection V n f = (coloredConstantIso (⨁ V) n).inv ≫
      coloredTensorMap n (fun j => biproduct.π V (f j))
  | 0, _ => by simp [colorProjection, coloredTensorMap, coloredConstantIso, coloredTensor, tensorPower]
  | n + 1, f => by
    rw [colorProjection, coloredTensorMap, coloredConstantIso]
    simp only [tensorIso_inv, Iso.refl_inv, tensorHom_comp_tensorHom, Category.id_comp]
    rw [← colorProjection_eq_coloredTensorMap (fun j => f j.succ)]

/-- Each colored inclusion and its matching projection compose to identity. -/
@[simp] theorem colorInclusion_projection_self : ∀ n (f : Fin n → I),
    colorInclusion V n f ≫ colorProjection V n f = 𝟙 _ := by
  intro n f
  rw [colorInclusion_eq_coloredTensorMap, colorProjection_eq_coloredTensorMap]
  simp only [Category.assoc, Iso.hom_inv_id_assoc, ← coloredTensorMap_comp]
  simpa only [biproduct.ι_π_self] using coloredTensorMap_id n (fun j => V (f j))

omit [HasFiniteBiproducts C] [BraidedCategory C] in
/-- A tensor map vanishes if one of its component maps vanishes. -/
theorem coloredTensorMap_eq_zero_of_component : ∀ (n : ℕ) {X Y : Fin n → C}
    (f : ∀ i, X i ⟶ Y i) (j : Fin n), f j = 0 → coloredTensorMap n f = 0
  | 0, _, _, _, j => Fin.elim0 j
  | n + 1, _, _, f, j => by
    refine Fin.cases ?_ (fun k => ?_) j
    · intro h
      simp [coloredTensorMap, h]
    · intro h
      have ht := coloredTensorMap_eq_zero_of_component n (fun i => f i.succ) k h
      simp [coloredTensorMap, ht]

/-- Distinct colorings give orthogonal inclusion/projection components. -/
theorem colorInclusion_projection_ne : ∀ {n : ℕ} (f g : Fin n → I), f ≠ g →
    colorInclusion V n f ≫ colorProjection V n g = 0 := by
  intro n f g h
  classical
  obtain ⟨j, hj⟩ := Function.ne_iff.mp h
  rw [colorInclusion_eq_coloredTensorMap, colorProjection_eq_coloredTensorMap]
  simp only [Category.assoc, Iso.hom_inv_id_assoc, ← coloredTensorMap_comp]
  exact coloredTensorMap_eq_zero_of_component n _ j (biproduct.ι_π_ne V hj)

omit [BraidedCategory C] [DecidableEq I] in
/-- The resolution for one more tensor factor is the tensor product of the
biproduct resolution and the resolution for the remaining factors. -/
theorem colorProjection_inclusion_succ (n : ℕ) :
    (∑ f : Fin (n + 1) → I, colorProjection V (n + 1) f ≫ colorInclusion V (n + 1) f) =
      (∑ a : I, biproduct.π V a ≫ biproduct.ι V a) ⊗ₘ
        (∑ f : Fin n → I, colorProjection V n f ≫ colorInclusion V n f) := by
  classical
  rw [← (Fin.consEquiv (fun _ => I)).sum_comp, Fintype.sum_prod_type]
  simp only [Fin.consEquiv_apply, colorProjection, colorInclusion, tensorHom_comp_tensorHom]
  change (∑ a : I, ∑ f : Fin n → I,
    (biproduct.π V a ≫ biproduct.ι V a) ⊗ₘ
      (colorProjection V n f ≫ colorInclusion V n f)) = _
  simp_rw [← tensor_sum]
  rw [← sum_tensor]

-- Retain the original theorem's braided and decidable-equality assumptions.
set_option linter.unusedSectionVars false in
/-- The colored components resolve the identity on every tensor power. -/
theorem colorProjection_inclusion_total : ∀ n,
    (∑ f : Fin n → I, colorProjection V n f ≫ colorInclusion V n f) =
      𝟙 (tensorPower (⨁ V) n)
  | 0 => by
    classical
    simp [colorProjection, colorInclusion, tensorPower]
  | n + 1 => by
    classical
    rw [colorProjection_inclusion_succ, biproduct.total, colorProjection_inclusion_total n]
    simp [tensorPower]

/-- Tensor powers of a finite biproduct decompose into the actual colored
tensor products of its summands. -/
def coloredBiproductIso (n : ℕ) : tensorPower (⨁ V) n ≅
    ⨁ (fun f : Fin n → I => coloredTensor n (fun j => V (f j))) where
  hom := biproduct.lift (colorProjection V n)
  inv := biproduct.desc (colorInclusion V n)
  hom_inv_id := by rw [biproduct.lift_desc, colorProjection_inclusion_total]
  inv_hom_id := by
    classical
    apply biproduct.hom_ext'
    intro f
    apply biproduct.hom_ext
    intro g
    simp only [Category.assoc, biproduct.ι_desc_assoc, biproduct.lift_π,
      Category.comp_id]
    by_cases h : f = g
    · subst g
      simp
    · rw [colorInclusion_projection_ne V f g h]
      simp [biproduct.ι_π_ne _ h]

/-- The decomposition's component projections are the recursive maps. -/
@[simp] theorem coloredBiproductIso_hom_π (n : ℕ) (f : Fin n → I) :
    (coloredBiproductIso V n).hom ≫
      biproduct.π (fun f : Fin n → I => coloredTensor n (fun j => V (f j))) f =
        colorProjection V n f := by
  simp [coloredBiproductIso]

/-- The decomposition's component inclusions are the recursive maps. -/
@[simp] theorem coloredBiproductIso_ι_inv (n : ℕ) (f : Fin n → I) :
    biproduct.ι (fun f : Fin n → I => coloredTensor n (fun j => V (f j))) f ≫
      (coloredBiproductIso V n).inv = colorInclusion V n f := by
  simp [coloredBiproductIso]

/-- Every actual colored signed word intertwines the corresponding
component inclusion with the actual braid action on the finite sum. -/
theorem coloredWordIso_intertwines_colorInclusion (n : ℕ)
    (w : List (Fin (n + 1) × Bool)) (f : Fin (n + 2) → I) :
    (coloredWordIso n w (fun j => V (f j))).hom ≫
      colorInclusion V (n + 2) (fun j => f (coloredWordSwap n w j)) =
    colorInclusion V (n + 2) f ≫
      ((braidWordAction (⨁ V) n (FreeGroup.mk w.reverse)).val).asIso.hom := by
  simp only [colorInclusion_eq_coloredTensorMap, Category.assoc]
  exact coloredWordIso_intertwines_uniform w (fun j => biproduct.ι V (f j))

/-- Every actual braid word intertwines the colored projections in the
opposite direction. -/
theorem braidWordAction_intertwines_colorProjection (n : ℕ)
    (w : List (Fin (n + 1) × Bool)) (f : Fin (n + 2) → I) :
    ((braidWordAction (⨁ V) n (FreeGroup.mk w.reverse)).val).asIso.hom ≫
      colorProjection V (n + 2) (fun j => f (coloredWordSwap n w j)) =
    colorProjection V (n + 2) f ≫ (coloredWordIso n w (fun j => V (f j))).hom := by
  have hc := coloredWordIso_constant n w (⨁ V)
  have hn := coloredWordIso_natural w (X := fun _ => ⨁ V) (Y := fun j => V (f j))
    (fun j => biproduct.π V (f j))
  rw [colorProjection_eq_coloredTensorMap, colorProjection_eq_coloredTensorMap]
  simp only [Category.assoc]
  rw [Iso.eq_inv_comp, ← Category.assoc, ← hc]
  simpa only [Category.assoc, Iso.hom_inv_id_assoc] using hn

/-- The component inclusion agrees with the independently constructed
colored-block inclusion for the actual biproduct injections. -/
theorem colorInclusion_eq_coloredBlockInclusion (n : ℕ) (f : Fin n → I) :
    colorInclusion V n f = coloredBlockInclusion n (fun j => V (f j)) (⨁ V)
      (fun j => biproduct.ι V (f j)) :=
  colorInclusion_eq_coloredTensorMap V f

/-- The component projection agrees with the independently constructed
colored-block projection for the actual biproduct projections. -/
theorem colorProjection_eq_coloredBlockProjection (n : ℕ) (f : Fin n → I) :
    colorProjection V n f = coloredBlockProjection n (fun j => V (f j)) (⨁ V)
      (fun j => biproduct.π V (f j)) :=
  colorProjection_eq_coloredTensorMap V f

/-- The colored retract blocks associated to the biproduct summands resolve
the identity on the whole tensor power. -/
theorem coloredBlockProjection_inclusion_total (n : ℕ) :
    (∑ f : Fin n → I,
      coloredBlockProjection n (fun j => V (f j)) (⨁ V) (fun j => biproduct.π V (f j)) ≫
      coloredBlockInclusion n (fun j => V (f j)) (⨁ V) (fun j => biproduct.ι V (f j))) =
      𝟙 (tensorPower (⨁ V) n) := by
  simp only [← colorProjection_eq_coloredBlockProjection,
    ← colorInclusion_eq_coloredBlockInclusion]
  exact colorProjection_inclusion_total V n

end MTC.Braided.Cabling
end
